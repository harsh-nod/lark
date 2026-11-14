"""Check exact Linear source/publication/CI before one non-force main update."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path('/tmp/lark-ptx-linear-refinement-20261113')
MAIN = Path('/home/harsh/lark')
OUT = Path('/tmp/lark-ptx-linear-ci-main-v1-20261113')
SOURCE = '1e005415a113c69a94a28487803ffdfefa3c0f94'
OLD = '2c0c96ea5aac0df7b8c41aca55b2a3818b98b4a3'
RUN = 43531324083
PROOF = 'reproduction/ptx/results/full-size-linear-proof-v1'
PUBLICATION = 'reproduction/ptx/results/full-size-linear-proof-publication-v1'
CI = 'reproduction/ptx/results/full-size-linear-proof-ci-v1'
DOC_CHANGES = {
    'README.md': [(
        'and isolated installed-wheel replay passed. Publication and source CI are\n'
        'still being completed; this adds no original model or NVIDIA result.\n',
        'and isolated installed-wheel replay passed. Anonymous publication verification\n'
        'and all twenty-three source CI jobs passed. This adds no original model or\n'
        'NVIDIA result.\n')],
    'reproduction/ptx/LINEAR.md': [(
        'replay have passed. Raw evidence packaging, anonymous publication and actual\n'
        'source CI remain. Four independent PTX kernel proofs remain published; this\n'
        'additional compiled Linear proof adds no original model success.\n',
        'replay have passed. The [complete evidence packet](results/full-size-linear-proof-v1/RESULTS.md),\n'
        'anonymous publication verification and all twenty-three actual source CI\n'
        'jobs passed. This fifth independent compiled PTX development proof adds\n'
        'no original model success.\n'), (
        'The complete proof still needs its retained evidence packet, anonymous\n'
        'publication verification and actual source CI before promotion. Passing local\n'
        'checks establishes none of those publication outcomes or original model results.\n'
        'No registered legacy profile exists for Linear.\n',
        'The [anonymous publication record](results/full-size-linear-proof-publication-v1/results.json)\n'
        'matched all 56 changed files (94,911,615 bytes), seven archives, 960 members\n'
        'and 64 SDK/Lean source bindings to source `1e00541`, with TLS verification\n'
        'enabled. It retained every development attempt, including all five failures.\n'
        'The [actual source CI record](results/full-size-linear-proof-ci-v1/results.json)\n'
        'records all twenty-three jobs passing, including the separate complete\n'
        'Linear cold export/replay, four controls and SDK adversarial checks.\n'
        'The later receipt commit changes only recorded receipts and this document\n'
        'and the root README. All SDK, Lean, tests, workflow and frozen snapshots\n'
        'retain their exact tested source identities. Publication repeated no\n'
        'scientific proof, model or GPU trial. No registered legacy profile or\n'
        'original model result is added.\n')],
}


def require(condition, message):
    if not condition:
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


def checked_folder(prefix):
    folder = ROOT / prefix
    require(folder.is_dir() and not any(p.is_symlink() for p in folder.rglob('*')), 'Missing or symlinked receipt')
    files = {p.name: sha(p) for p in folder.iterdir() if p.is_file() and p.name != 'manifest.json'}
    require(files == read(folder / 'manifest.json') and len(list(folder.iterdir())) == len(files) + 1,
            'Exact receipt inventory differs: ' + prefix)
    return {prefix + '/' + name for name in [*files, 'manifest.json']}


def expected_doc(name):
    original = subprocess.check_output(['git', 'show', SOURCE + ':' + name], cwd=ROOT).decode()
    for before, after in DOC_CHANGES[name]:
        require(original.count(before) == 1, 'Exact source document anchor required')
        original = original.replace(before, after)
    return original


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--target', required=True)
    parser.add_argument('--check-only', action='store_true')
    args = parser.parse_args()
    target = args.target
    require(re.fullmatch('[0-9a-f]{40}', target) is not None, 'Concrete target required')
    require(call(['git', 'rev-parse', 'HEAD']) == target and not call(['git', 'status', '--porcelain']),
            'Clean pinned candidate required')
    require(call(['git', 'rev-parse', 'HEAD'], MAIN) == OLD
            and call(['git', 'branch', '--show-current'], MAIN) == 'main'
            and not call(['git', 'status', '--porcelain'], MAIN), 'Clean local main changed')
    require(call(['git', 'rev-parse', 'refs/remotes/origin/main']) == OLD, 'Tracking main changed')
    for ancestor in (OLD, SOURCE):
        subprocess.run(['git', 'merge-base', '--is-ancestor', ancestor, target], cwd=ROOT, check=True)
    expected = set(DOC_CHANGES) | checked_folder(PUBLICATION) | checked_folder(CI)
    changed = call(['git', 'diff', '--name-only', SOURCE, target]).splitlines()
    require(set(changed) == expected and len(changed) == 12,
            'Only exact publication/CI receipts and two documents may follow checked source')
    require(all((ROOT / name).read_text() == expected_doc(name) for name in DOC_CHANGES),
            'Exact receipt document updates required')
    checked_folder(PROOF)
    require(sha(ROOT / PROOF / 'manifest.json') == '651a708c23dc0e4cffb89e2d7ac10af83226e2fa6a3f2de7576296b6827bed32',
            'Frozen complete Linear proof packet changed')
    proof = read(ROOT / PROOF / 'results.json')
    require(proof['independent_source_bound_development_proofs'] == 1
            and proof['retained_positive_Main_checks'] == proof['current_SDK_positive_Main_checks'] == 4
            and proof['positive_rechecks'] == 3 and proof['owned_module_builds_across_four_checks'] == 40
            and proof['retained_failed_official_exports'] == 0
            and proof['retained_pre_SDK_development_attempts'] == 12
            and proof['accepted_pre_SDK_development_checks'] == 7
            and proof['failed_pre_SDK_development_checks'] == 5
            and proof['direct_Lean_negative_controls'] == 4 and proof['negative_timeouts'] == 0
            and proof['owned_source_files'] == 64
            and proof['library_axiom_audits_per_check'] == 280 and proof['Main_axiom_audits_per_check'] == 6
            and proof['shapes'] == [[64, 256], [256, 512], [512], [64, 512]]
            and proof['PTX_instructions'] == 179 and proof['launch'] == {'grid': 32768, 'block': 1, 'warp': 32}
            and proof['unchanged_CUDA_contract_fuel'] == [1030, 1, 1, 1]
            and proof['new_registered_source_certificates'] == 0
            and proof['original_paper_fully_reproduced'] is proof['nvidia_execution'] is False,
            'Completed Linear scope differs')
    require(sha(ROOT / 'reproduction/paper_results/snapshots/20261113-v25/manifest.json')
            == 'e90502aaaedfacbea8c0ded36ad8facd8adf1870c755c3b5a38de321dead572f', 'Frozen v25 changed')
    publication = read(ROOT / PUBLICATION / 'results.json')
    binding = read(ROOT / PUBLICATION / 'binding.json')
    require(publication['source_commit'] == SOURCE
            and publication['all_downloads_match_committed_bytes'] is True
            and publication['tls_verification'] is True and publication['authorization_header'] is False
            and publication['archives_checked'] == 7 and publication['archive_members_checked'] == 960
            and publication['owned_source_bindings_checked'] == 64
            and publication['all_pre_SDK_development_attempts_retained'] == 12
            and publication['failed_pre_SDK_development_attempts_retained'] == 5
            and binding['source_commit'] == SOURCE and binding['observed_exit_code'] == 0
            and binding['verifier_sha256'] == sha(ROOT / PUBLICATION / 'verifier.py')
            and binding['anonymous_results_sha256'] == sha(ROOT / PUBLICATION / 'results.json')
            and binding['proof_packet_manifest_sha256'] == sha(ROOT / PROOF / 'manifest.json'),
            'Actual anonymous source/proof observation differs')
    records = publication['downloaded_files']
    public_paths = set(call(['git', 'diff', '--name-only', OLD, SOURCE]).splitlines())
    require(len(records) == len(public_paths) == 56 and {r['path'] for r in records} == public_paths
            and publication['total_downloaded_bytes'] == sum(r['bytes'] for r in records) == 94911615,
            'Every public changed file required')
    for row in records:
        data = subprocess.check_output(['git', 'show', SOURCE + ':' + row['path']], cwd=ROOT, timeout=60)
        require(row['http_status'] == 200 and row['curl_ssl_verify_result'] == 0
                and row['authorization_header'] is False and row['tls_verification'] is True
                and row['matches_committed_bytes'] is True and len(data) == row['bytes']
                and hashlib.sha256(data).hexdigest() == row['sha256'], 'Exact public Source Git bytes differ')
    section = (ROOT / '.github/workflows/ci.yml').read_text().split('\njobs:\n', 1)[1]
    names = set(re.findall(r'^  ([a-z][a-z0-9-]*):$', section, re.M))
    require(len(names) == 23 and {'paper-ledger', 'proof-tests', 'ptx-linear'} <= names,
            'All actual twenty-three jobs required')
    receipt = read(ROOT / CI / 'results.json')
    require(receipt['source_commit'] == SOURCE and receipt['run_id'] == RUN
            and receipt['status'] == 'exact-source-CI-all-23-passed'
            and receipt['successful_jobs'] == 23 and set(receipt['expected_jobs']) == names,
            'Recorded source CI differs')
    ci = json.loads(call(['gh', 'api', f'repos/harsh-nod/lark/actions/runs/{RUN}']))
    jobs = json.loads(call(['gh', 'api', f'repos/harsh-nod/lark/actions/runs/{RUN}/jobs?per_page=100']))
    require(ci['head_sha'] == SOURCE and ci['status'] == 'completed' and ci['conclusion'] == 'success'
            and ci['head_branch'] == 'reproduction/ptx-linear-refinement'
            and ci['event'] == 'push' and ci['name'] == 'Verify'
            and jobs['total_count'] == len(jobs['jobs']) == 23 and {j['name'] for j in jobs['jobs']} == names
            and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs['jobs']),
            'Fresh actual twenty-three source CI successes required')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha'] == OLD,
            'Remote main changed')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/reproduction/ptx-linear-refinement']))
            ['object']['sha'] == target, 'Published candidate branch differs')
    state = {'schema': 1, 'status': 'Linear-main-all-gates-passed-update-pending',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'source_checkpoint': SOURCE,
        'source_CI_executed_for_promoted_commit': False, 'old_main': OLD, 'promoted_commit': target,
        'source_ci': ci, 'source_ci_jobs': jobs, 'changed_paths_after_checked_source': changed,
        'checks': {'actual23_Linear_source_jobs_all_success': True,
            'all_other_code_Lean_tests_workflow_and_snapshots_identical_to_CI_source': True,
            'one_kernel_four_Main_checks40_fresh_module_builds4_Lean_controls_bound': True,
            'all56_public_changed_files_anonymous_TLS_exact_source_bytes': True,
            'seven_public_archives960_members64_wheel_source_bindings_verified': True,
            'all12_development_attempts_including5_failures_retained': True,
            'v25_snapshot_preserved': True, 'clean_main_candidate_ancestry_checked': True},
        'model_calls_by_promotion': 0, 'fresh_lean_checks_by_promotion': 0,
        'gpu_trials_by_promotion': 0, 'original_paper_fully_reproduced': False,
        'helper_sha256': sha(Path(__file__))}
    if args.check_only:
        print(json.dumps({'status': 'Linear-main-preflight-passed', 'source_ci_jobs': 23,
                         'receipt_docs_delta_files': len(changed), 'anonymous_files': 56}))
        return
    OUT.mkdir(exist_ok=False)
    write(OUT / 'progress.json', state)
    write(OUT / 'update.json', {'sha': target, 'force': False})
    state['remote_update'] = json.loads(call(['gh', 'api', '--method', 'PATCH',
        'repos/harsh-nod/lark/git/refs/heads/main', '--input', str(OUT / 'update.json')]))
    require(state['remote_update']['object']['sha'] == target, 'Remote main result differs')
    state['status'] = 'Linear-remote-main-fast-forwarded-local-pending'
    write(OUT / 'progress.json', state)
    state['local_merge'] = call(['git', 'merge', '--ff-only', target], MAIN)
    subprocess.run(['git', 'update-ref', 'refs/remotes/origin/main', target, OLD], cwd=ROOT, check=True)
    require(call(['git', 'rev-parse', 'HEAD'], MAIN) == target
            and not call(['git', 'status', '--porcelain'], MAIN), 'Local main differs after update')
    state['status'] = 'Linear-main-fast-forward-complete'
    write(OUT / 'results.json', state)
    print(json.dumps({'status': state['status'], 'main': target, 'source_ci_jobs': 23,
                     'original_paper_fully_reproduced': False}))


if __name__ == '__main__':
    main()
