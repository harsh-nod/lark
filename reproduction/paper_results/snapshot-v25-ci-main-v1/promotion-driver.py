"""Gate the v25 main fast-forward on actual twenty-one-job CI and public frozen replay."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path('/tmp/lark-paper-v25-20261113')
MAIN = Path('/home/harsh/lark')
OUT = Path('/tmp/lark-paper-v25-ci-main-v1-20261113')
SOURCE = '63aabf370aebd2aa5d45abced22dc5255886d65f'
OLD = '4b29886f31485825616f9539386c8fc7e1fbaf0a'
RUN = 43511578275
BASE = 'reproduction/paper_results/'
PREFIXES = (BASE + 'snapshot-v25-publication', BASE + 'snapshot-v25-source-ci-v1')
SNAPSHOT = BASE + 'snapshots/20261113-v25'
sys.path.insert(0, str(ROOT))
from reproduction.local_models import compare_full_shape as comparison  # noqa: E402


def require(condition, message):
    if not condition:
        raise ValueError(message)


def call(command, cwd=ROOT):
    return subprocess.check_output(command, cwd=cwd, text=True, timeout=60).strip()


def read(path):
    return json.loads(path.read_text())


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    temporary = path.with_name(path.name + '.next')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(path)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--target', required=True)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    target = args.target
    require(re.fullmatch('[0-9a-f]{40}', target) is not None, 'Concrete target required')
    require(call(['git', 'rev-parse', 'HEAD']) == target
            and not call(['git', 'status', '--porcelain']), 'Candidate is not the clean pinned commit')
    require(call(['git', 'rev-parse', 'HEAD'], MAIN) == OLD
            and not call(['git', 'status', '--porcelain'], MAIN), 'Local main changed')
    require(call(['git', 'rev-parse', 'refs/remotes/origin/main']) == OLD, 'Tracking main changed')
    for ancestor in (OLD, SOURCE):
        subprocess.run(['git', 'merge-base', '--is-ancestor', ancestor, target], cwd=ROOT, check=True)
    expected = {BASE + 'README.md'}
    for prefix in PREFIXES:
        folder = ROOT / prefix
        require(not any(p.is_symlink() for p in folder.rglob('*')), 'Receipt symlink')
        for manifest in [folder / 'manifest.json', *sorted(folder.glob('*/manifest.json'))]:
            records = read(manifest)
            actual = {p.name: sha(p) for p in manifest.parent.iterdir()
                      if p.is_file() and p.name != 'manifest.json'}
            require(actual == records, 'Exact receipt inventory or bytes differ: ' + str(manifest))
        expected.update(p.relative_to(ROOT).as_posix() for p in folder.rglob('*') if p.is_file())
    changed = call(['git', 'diff', '--name-only', SOURCE, target]).splitlines()
    require(set(changed) == expected, 'Only the exact publication/CI receipts and paper README may follow source CI')
    require(sha(ROOT / SNAPSHOT / 'manifest.json')
            == 'e90502aaaedfacbea8c0ded36ad8facd8adf1870c755c3b5a38de321dead572f', 'Frozen snapshot changed')
    report = read(ROOT / SNAPSHOT / 'results/audit.json')
    require(report['counts'] == {'tables': 17, 'outer_figure_groups': 7, 'narrative_anchors': 16}
            and report['completion_percentage'] is None
            and report['original_paper_fully_reproduced'] is False, 'Paper audit scope changed')
    require(len(report['evidence_sha256']) == 3623, 'Full evidence roster differs')
    gemv = report['ptx_dot_evidence_checks']
    require(gemv['independent_source_bound_development_proofs'] == 1
            and gemv['retained_positive_Main_checks'] == 4 and gemv['positive_rechecks'] == 3
            and gemv['direct_Lean_negative_controls'] == 4 and gemv['successful_source_CI_jobs'] == 20
            and gemv['original_paper_fully_reproduced'] is gemv['nvidia_execution'] is False,
            'Complete-source GEMV scope differs')
    gemm = report['ptx_matrix_evidence_checks']
    require(gemm['independent_source_bound_development_proofs'] == 1
            and gemm['retained_positive_Main_checks'] == 4 and gemm['positive_rechecks'] == 3
            and gemm['direct_Lean_negative_controls'] == 4 and gemm['successful_source_CI_jobs'] == 21
            and gemm['original_paper_fully_reproduced'] is gemm['nvidia_execution'] is False,
            'Complete-source GEMM scope differs')
    models = report['full_shape_model_evidence_checks']
    require(models['complete_independent_cohorts'] == 6
            and models['all_six_independent_cohorts_present'] is True
            and models['missing_independent_cohorts'] == [], 'Actual six-cohort roster required')
    spec = read(ROOT / SNAPSHOT / 'targets.json')['full_shape_models']
    fresh = comparison.compare([ROOT / row['prefix'] for row in spec['packets']])
    recorded = read(ROOT / spec['comparison_prefix'] / 'results.json')
    require({k: v for k, v in fresh.items() if k != 'created_at_utc'}
            == {k: v for k, v in recorded.items() if k != 'created_at_utc'}
            and comparison.markdown(fresh) == (ROOT / spec['comparison_prefix'] / 'RESULTS.md').read_text(),
            'Strict complete comparison does not regenerate from every raw/audit packet')
    publication = read(ROOT / PREFIXES[0] / 'results.json')
    require(publication['source_commit'] == SOURCE and publication['snapshot'] == '20261113-v25'
            and publication['positive_replays'] == 6 and publication['negative_controls'] == 65
            and publication['authenticated_download_requests'] is False
            and publication['tls_verification'] is True and publication['git_on_replay_path'] is False
            and publication['all_downloads_match_committed_bytes'] is True
            and publication['original_paper_fully_reproduced'] is False, 'Public replay receipt differs')
    names = {p.relative_to(ROOT).as_posix() for p in (ROOT / SNAPSHOT).rglob('*') if p.is_file()}
    names.update(BASE + name for name in ('replay_snapshot.py', 'check_snapshot_controls.py'))
    records = publication['downloaded_files']
    require(len(records) == len(names) == 11 and {r['path'] for r in records} == names
            and sum(r['bytes'] for r in records) == publication['total_downloaded_bytes'] == sum((ROOT / name).stat().st_size for name in names)
            and all(r['http_status'] == 200 and r['curl_ssl_verify_result'] == 0
                    and r['tls_verification'] is True and r['authorization_header'] is False
                    and sha(ROOT / r['path']) == r['sha256']
                    and (ROOT / r['path']).stat().st_size == r['bytes'] for r in records),
            'Every public source/snapshot byte must match its anonymous TLS receipt')
    replay = read(ROOT / PREFIXES[0] / 'validation/results.json')
    require(replay == publication['validation'] and replay['status'] == 'passed'
            and replay['positive_replays'] == 6 and replay['negative_controls'] == 65
            and replay['replayer_sha256'] == sha(ROOT / BASE / 'replay_snapshot.py')
            and replay['control_runner_sha256'] == sha(ROOT / BASE / 'check_snapshot_controls.py'),
            'Public replay/source binding differs')
    workflow_jobs = (ROOT / '.github/workflows/ci.yml').read_text().split('\njobs:\n', 1)[1]
    expected_jobs = set(re.findall(r'^  ([a-z][a-z0-9-]*):$', workflow_jobs, re.M))
    require(len(expected_jobs) == 21 and 'paper-ledger' in expected_jobs, 'All twenty-one source jobs required')
    receipt = read(ROOT / PREFIXES[1] / 'results.json')
    require(receipt['source_commit'] == SOURCE and receipt['run_id'] == RUN
            and receipt['successful_jobs'] == 21 and set(receipt['expected_jobs']) == expected_jobs,
            'Recorded actual twenty-one-job CI receipt differs')
    ci = json.loads(call(['gh', 'run', 'view', str(RUN), '--repo', 'harsh-nod/lark',
                         '--json', 'status,conclusion,headSha,jobs,url']))
    require(ci['headSha'] == SOURCE and ci['status'] == 'completed' and ci['conclusion'] == 'success'
            and len(ci['jobs']) == 21 and {j['name'] for j in ci['jobs']} == expected_jobs
            and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in ci['jobs']),
            'All twenty-one actual source CI jobs must be freshly observed successful')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha'] == OLD,
            'Remote main changed')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/reproduction/paper-v25']))
            ['object']['sha'] == target, 'Public candidate branch differs')
    state = {'schema': 1, 'status': 'v25-main-all-gates-passed-update-pending',
             'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'source_checkpoint': SOURCE,
             'source_CI_executed_for_promoted_commit': False, 'old_main': OLD,
             'promoted_commit': target, 'source_ci': ci, 'changed_paths_after_checked_source': changed,
             'checks': {'actual21_source_jobs_all_success': True,
                        'all_other_source_workflow_tests_and_snapshots_identical_to_CI_source': True,
                        'strict_six_cohort_comparison_regenerated_from_all_raw_and_audit_packets': True,
                        'all11_public_source_snapshot_files_TLS_anonymous_exact_bytes': True,
                        'downloaded_snapshot6_positive65_negative_replays_passed_without_git': True,
                        'clean_main_and_candidate_and_ancestry_checked': True},
             'model_calls_by_promotion': 0, 'fresh_lean_checks_by_promotion': 0,
             'gpu_trials_by_promotion': 0, 'original_paper_fully_reproduced': False,
             'helper_sha256': sha(Path(__file__))}
    if args.check_only:
        print(json.dumps({'status': 'v25-main-preflight-passed', 'source_ci_jobs': 21,
                          'receipt_docs_delta_files': len(changed), 'anonymous_files': 11,
                          'original_paper_fully_reproduced': False}))
        return
    OUT.mkdir(exist_ok=False)
    write(OUT / 'progress.json', state)
    write(OUT / 'update.json', {'sha': target, 'force': False})
    state['remote_update'] = json.loads(call(['gh', 'api', '--method', 'PATCH',
        'repos/harsh-nod/lark/git/refs/heads/main', '--input', str(OUT / 'update.json')]))
    require(state['remote_update']['object']['sha'] == target, 'Remote update differs')
    state['status'] = 'v25-remote-main-fast-forwarded-local-pending'
    write(OUT / 'progress.json', state)
    state['local_merge'] = call(['git', 'merge', '--ff-only', target], MAIN)
    subprocess.run(['git', 'update-ref', 'refs/remotes/origin/main', target, OLD], cwd=ROOT, check=True)
    require(call(['git', 'rev-parse', 'HEAD'], MAIN) == target
            and not call(['git', 'status', '--porcelain'], MAIN), 'Local main differs after fast-forward')
    state['status'] = 'v25-main-fast-forward-complete'
    write(OUT / 'results.json', state)
    print(json.dumps({'status': state['status'], 'main': target, 'source_ci_jobs': 21,
                      'original_paper_fully_reproduced': False}))


if __name__ == '__main__':
    main()
