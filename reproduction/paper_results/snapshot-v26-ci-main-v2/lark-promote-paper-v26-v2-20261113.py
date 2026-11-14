"""Guard a non-force main fast-forward with actual v26 source CI and public replay."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path('/tmp/lark-paper-v26-20261113')
MAIN = Path('/home/harsh/lark')
OUT = Path('/tmp/lark-paper-v26-ci-main-v2-20261113')
BASE = 'reproduction/paper_results/'
SOURCE = 'ce5611655946a0a8cca76f97beb8f85bf8f4fc2b'
OLD = 'db1eb9bbb96d365987f685e085ff3e4a314ec128'
RUN = 43544667567
PREFIXES = tuple(BASE + name for name in (
    'snapshot-v26-publication', 'snapshot-v26-source-ci-v2', 'snapshot-v26-source-ci-failed-v1'))
SNAPSHOT = BASE + 'snapshots/20261113-v26'
DOCS = {'README.md', BASE + 'README.md', BASE + 'ARCHIVE_FORMAT.md'}
sys.path.insert(0, str(ROOT))
from reproduction.local_models import compare_full_shape as comparison  # noqa: E402


def require(value, message):
    if not value:
        raise ValueError(message)


def call(command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True, timeout=60).strip()


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    temporary = path.with_name(path.name + '.next')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--target', required=True)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    target = args.target
    require(re.fullmatch('[0-9a-f]{40}', target), 'Exact target commit required')
    require(call(['git', 'rev-parse', 'HEAD']) == target and not call(['git', 'status', '--porcelain']),
            'Candidate must be the clean pinned commit')
    require(call(['git', 'rev-parse', 'HEAD'], MAIN) == OLD and not call(['git', 'status', '--porcelain'], MAIN),
            'Local main changed')
    require(call(['git', 'rev-parse', 'refs/remotes/origin/main']) == OLD, 'Tracking main changed')
    for ancestor in [SOURCE, OLD]:
        subprocess.run(['git', 'merge-base', '--is-ancestor', ancestor, target], cwd=ROOT, check=True)
    expected = set(DOCS)
    for prefix in PREFIXES:
        folder = ROOT / prefix
        require(folder.is_dir() and not any(p.is_symlink() for p in folder.rglob('*')), 'Receipt path invalid')
        for manifest in folder.rglob('manifest.json'):
            actual = {p.name: sha(p) for p in manifest.parent.iterdir() if p.is_file() and p.name != 'manifest.json'}
            require(actual == read(manifest), 'Receipt inventory or byte mismatch: ' + str(manifest))
        expected.update(p.relative_to(ROOT).as_posix() for p in folder.rglob('*') if p.is_file())
    changed = call(['git', 'diff', '--name-only', SOURCE, target]).splitlines()
    require(set(changed) == expected, 'Only the exact three documents and three receipt packets may follow tested source')
    require(sha(ROOT / SNAPSHOT / 'manifest.json') == '251d9b381282f54cc721587bc88d78e0f344a44eaeaf03f112fb6f6556baf6ed', 'Frozen v26 differs')
    require(sha(ROOT / BASE / 'snapshots/20261113-v25/manifest.json') == 'e90502aaaedfacbea8c0ded36ad8facd8adf1870c755c3b5a38de321dead572f', 'Legacy v25 differs')
    report = read(ROOT / SNAPSHOT / 'results/audit.json')
    require(report['counts'] == {'tables': 17, 'outer_figure_groups': 7, 'narrative_anchors': 16}
            and report['completion_percentage'] is None and report['original_paper_fully_reproduced'] is False,
            'Paper audit scope differs')
    require(len(report['evidence_sha256']) == 3792, 'Complete evidence roster differs')
    old_report = read(ROOT / BASE / 'snapshots/20261113-v25/results/audit.json')
    require(len(old_report['evidence_sha256']) == 3623 and all(
        report['evidence_sha256'].get(name) == digest
        for name, digest in old_report['evidence_sha256'].items()),
        'Every original evidence path and hash must be retained')
    for name in ['auditor.py', 'targets.json']:
        require(sha(ROOT / BASE / 'frozen-definitions/20261113-v25' / name)
                == sha(ROOT / BASE / 'snapshots/20261113-v25' / name),
                'Historical frozen definition differs: ' + name)
    for family in ['pointwise', 'dot', 'matrix', 'batched', 'linear']:
        evidence = report['ptx_' + family + '_evidence_checks']
        require(evidence['independent_source_bound_development_proofs'] == 1
                and evidence['direct_Lean_negative_controls'] == 4
                and evidence['nvidia_execution'] is evidence['original_paper_fully_reproduced'] is False,
                'Development proof scope differs: ' + family)
    for family, jobs in [('batched', 22), ('linear', 23)]:
        evidence = report['ptx_' + family + '_evidence_checks']
        require(evidence['current_SDK_positive_Main_checks'] == 4 and evidence['successful_source_CI_jobs'] == jobs,
                'Historical exact proof-source CI differs: ' + family)
    models = report['full_shape_model_evidence_checks']
    require(models['complete_independent_cohorts'] == 6 and models['all_six_independent_cohorts_present'] is True
            and models['missing_independent_cohorts'] == [], 'Complete six-cohort roster required')
    spec = read(ROOT / SNAPSHOT / 'targets.json')['full_shape_models']
    fresh = comparison.compare([ROOT / row['prefix'] for row in spec['packets']])
    recorded = read(ROOT / spec['comparison_prefix'] / 'results.json')
    require({k: v for k, v in fresh.items() if k != 'created_at_utc'} ==
            {k: v for k, v in recorded.items() if k != 'created_at_utc'}
            and comparison.markdown(fresh) == (ROOT / spec['comparison_prefix'] / 'RESULTS.md').read_text(),
            'Six-cohort report does not regenerate from all raw/audit inputs')
    public = read(ROOT / PREFIXES[0] / 'results.json')
    require(public['source_commit'] == SOURCE and public['snapshot'] == '20261113-v26'
            and public['positive_replays'] == 8 and public['negative_controls'] == 81
            and public['authenticated_download_requests'] is public['git_on_replay_path'] is False
            and public['tls_verification'] is public['all_downloads_match_committed_bytes'] is True
            and public['original_paper_fully_reproduced'] is False, 'Public validation scope differs')
    names = set(call(['git', 'ls-tree', '-r', '--name-only', SOURCE, '--', SNAPSHOT]).splitlines())
    names.update(BASE + name for name in ['replay_snapshot.py', 'check_snapshot_controls.py',
                                        'snapshot_archives.py', 'snapshot_control_archives.py'])
    records = public['downloaded_files']
    require(len(names) == len(records) == 17 and {r['path'] for r in records} == names
            and sum(r['bytes'] for r in records) == public['total_downloaded_bytes'] == 238899106,
            'Complete source-tree download roster differs')
    for record in records:
        path = ROOT / record['path']
        require(sha(path) == record['sha256'] and path.stat().st_size == record['bytes']
                and record['http_status'] == 200 and record['curl_ssl_verify_result'] == 0
                and record['tls_verification'] is True and record['authorization_header'] is False,
                'Actual anonymous TLS download differs: ' + record['path'])
    require(public['checker_sha256'] == sha(ROOT / BASE / 'check_public_snapshot.py'), 'Public checker source differs')
    validation = read(ROOT / PREFIXES[0] / 'validation/results.json')
    require(validation == public['validation'] and validation['status'] == 'passed'
            and len(validation['checks']) == 89 and validation['positive_replays'] == 8
            and validation['negative_controls'] == 81
            and len(validation['released_completed_temporary_control_copies']) == 80
            and validation['all_control_payloads_complete_during_replay'] is True
            and validation['replayer_sha256'] == sha(ROOT / BASE / 'replay_snapshot.py')
            and validation['control_runner_sha256'] == sha(ROOT / BASE / 'check_snapshot_controls.py'),
            'Public full-control receipt or source binding differs')
    require(len(list((ROOT / PREFIXES[0] / 'validation').glob('*.log'))) == 89, 'All actual control logs required')
    observed = read(ROOT / PREFIXES[0] / 'observer/results.json')
    require(observed['source_commit'] == SOURCE and observed['exit_code'] == 0 and not observed['timed_out']
            and observed['completed_CI_ledger_job_before_start'] == 132293060832,
            'Single-launch public observer differs')
    captured = read(ROOT / PREFIXES[0] / 'capture/captured-file-inventory.json')
    for record in captured['files']:
        label, relative = record['path'].split('/', 1)
        folder = ROOT / PREFIXES[0]
        path = folder / relative if label == 'public' else folder / label / relative
        require(path.stat().st_size == record['bytes'] and sha(path) == record['sha256'], 'Captured receipt bytes differ')
    workflow = (ROOT / '.github/workflows/ci.yml').read_text().split('\njobs:\n', 1)[1]
    expected_jobs = set(re.findall(r'^  ([a-z][a-z0-9-]*):$', workflow, re.M))
    require(len(expected_jobs) == 23 and 'paper-ledger' in expected_jobs, 'Complete workflow roster required')
    receipt = read(ROOT / PREFIXES[1] / 'results.json')
    require(receipt['source_commit'] == SOURCE and receipt['run_id'] == RUN
            and receipt['successful_jobs'] == 23 and receipt['status'] == 'exact-source-CI-all-23-passed'
            and set(receipt['expected_jobs']) == expected_jobs, 'Actual successful source-CI receipt differs')
    failed = read(ROOT / PREFIXES[2] / 'results.json')
    require(failed['source_commit'] == '411663e0aefe96ce7fc72dc94c459c95b7dd1c3d'
            and failed['run_id'] == 43541910060 and failed['successful_jobs'] == 22
            and failed['status'] == 'exact-source-CI-terminal-non-success', 'Earlier failed source CI must remain failed')
    ci = json.loads(call(['gh', 'api', f'repos/harsh-nod/lark/actions/runs/{RUN}']))
    jobs = json.loads(call(['gh', 'api', f'repos/harsh-nod/lark/actions/runs/{RUN}/jobs?per_page=100']))
    require(ci['head_sha'] == SOURCE and ci['status'] == 'completed' and ci['conclusion'] == 'success'
            and ci['run_attempt'] == 1 and jobs['total_count'] == len(jobs['jobs']) == 23
            and {j['name'] for j in jobs['jobs']} == expected_jobs
            and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs['jobs']),
            'Fresh actual complete source CI required')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha'] == OLD,
            'Remote main changed')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/reproduction/paper-v26']))['object']['sha'] == target,
            'Public candidate branch differs')
    state = {'schema': 1, 'status': 'v26-main-all-gates-passed-update-pending',
             'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'source_checkpoint': SOURCE,
             'source_CI_executed_for_promoted_commit': False, 'old_main': OLD, 'promoted_commit': target,
             'source_ci': ci, 'source_ci_jobs': jobs, 'changed_paths_after_checked_source': changed,
             'checks': {'actual23_source_jobs_all_success': True,
                        'only_three_docs_and_exact_new_receipts_after_source': True,
                        'all_code_workflow_tests_Lean_and_snapshots_identical_to_tested_source': True,
                        'all_six_model_cohorts_regenerated_from_raw_and_audit_inputs': True,
                        'all17_public_files_anonymous_TLS_source_exact': True,
                        'all89_downloaded_snapshot_checks_passed_without_git': True,
                        'all3792_frozen_evidence_and_old3623_hashes_and_both_prior_definitions_retained': True,
                        'earlier_failed_source_CI_preserved': True,
                        'clean_main_candidate_and_ancestry_verified': True},
             'helper_sha256': sha(Path(__file__)), 'model_calls_by_promotion': 0,
             'fresh_lean_checks_by_promotion': 0, 'gpu_trials_by_promotion': 0,
             'original_paper_fully_reproduced': False}
    if args.check_only:
        print(json.dumps({'status': 'v26-main-preflight-passed', 'source_CI_jobs': 23,
                          'anonymous_files': 17, 'receipt_docs_delta_files': len(changed)}))
        return
    OUT.mkdir(exist_ok=False)
    write(OUT / 'progress.json', state)
    write(OUT / 'update.json', {'sha': target, 'force': False})
    state['remote_update'] = json.loads(call(['gh', 'api', '--method', 'PATCH',
        'repos/harsh-nod/lark/git/refs/heads/main', '--input', str(OUT / 'update.json')]))
    require(state['remote_update']['object']['sha'] == target, 'Remote main update differs')
    state['status'] = 'v26-remote-main-fast-forwarded-local-pending'
    write(OUT / 'progress.json', state)
    state['local_merge'] = call(['git', 'merge', '--ff-only', target], MAIN)
    subprocess.run(['git', 'update-ref', 'refs/remotes/origin/main', target, OLD], cwd=ROOT, check=True)
    require(call(['git', 'rev-parse', 'HEAD'], MAIN) == target and not call(['git', 'status', '--porcelain'], MAIN),
            'Local main differs after guarded fast-forward')
    state['status'] = 'v26-main-fast-forward-complete'
    write(OUT / 'results.json', state)
    print(json.dumps({'status': state['status'], 'main': target, 'source_CI_jobs': 23,
                      'original_paper_fully_reproduced': False}))


if __name__ == '__main__':
    main()
