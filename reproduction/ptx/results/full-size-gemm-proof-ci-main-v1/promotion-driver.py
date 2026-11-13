"""Gate a non-force main fast-forward on actual GEMM CI and public proof bytes."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path('/tmp/lark-ptx-matrix-refinement-20261113')
MAIN = Path('/home/harsh/lark')
OUT = Path('/tmp/lark-ptx-matrix-ci-main-v2-20261113')
SOURCE = 'a2100f361d451fafd9babb853319a3fcd6bf5c82'
OLD = 'ae61a113489f1eb9b946f877028c6edb7796dced'
RUN = 43500937594
BASE = 'reproduction/ptx/results/'
PROOF = BASE + 'full-size-gemm-proof-v1'
PUBLICATION = BASE + 'full-size-gemm-proof-publication-v2'
CI = BASE + 'full-size-gemm-proof-ci-v2'
DOC = 'reproduction/ptx/MATRIX.md'
PUB_PARAGRAPH = (
    '\nThe [anonymous publication check](results/full-size-gemm-proof-publication-v2/results.json)\n'
    'matched all 59 changed files (22,753,879 bytes) to corrected source `a2100f3`\n'
    'with TLS verification enabled. It checked all five archives, 382 archive\n'
    'members and 55 wheel/source bindings. The initial failed CI record and\n'
    'fixture-layout correction are retained. This check repeated no proof, model\n'
    'or GPU experiment.\n'
)
CI_PARAGRAPH = (
    '\nThe [actual corrected-source CI record](results/full-size-gemm-proof-ci-v2/results.json)\n'
    'records all twenty-one jobs passing at source `a2100f3`, including the separate\n'
    'complete GEMM cold export/replay and four direct controls, integration and\n'
    'tampering tests, the four bounded PTX fixtures and all existing ledger checks.\n'
    'The later receipt commit changes only this document and recorded receipts.\n'
    'All SDK, Lean, tests, workflow and frozen snapshots retain their exact tested\n'
    'source identities.\n'
)



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
    require(not any(p.is_symlink() for p in folder.rglob('*')), 'Receipt symlink')
    files = {p.name: sha(p) for p in folder.iterdir() if p.is_file() and p.name != 'manifest.json'}
    require(files == read(folder / 'manifest.json')
            and len(list(folder.iterdir())) == len(files) + 1, 'Exact folder inventory differs: ' + prefix)
    return {prefix + '/' + name for name in [*files, 'manifest.json']}


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
            and not call(['git', 'status', '--porcelain'], MAIN), 'Local main changed')
    require(call(['git', 'rev-parse', 'refs/remotes/origin/main']) == OLD, 'Tracking main changed')
    for ancestor in (OLD, SOURCE):
        subprocess.run(['git', 'merge-base', '--is-ancestor', ancestor, target], cwd=ROOT, check=True)
    expected = {DOC} | checked_folder(PUBLICATION) | checked_folder(CI)
    changed = call(['git', 'diff', '--name-only', SOURCE, target]).splitlines()
    require(set(changed) == expected and len(changed) == 11,
            'Only exact publication/CI receipts and DOT document may follow checked source')
    source_doc = subprocess.check_output(['git', 'show', SOURCE + ':' + DOC], cwd=ROOT).decode()
    anchor = 'checks cover one independent development kernel.\n'
    require(source_doc.count(anchor) == 1 and (ROOT / DOC).read_text()
            == source_doc.replace(anchor, anchor + PUB_PARAGRAPH + CI_PARAGRAPH), 'Exact receipt paragraphs required')
    checked_folder(PROOF)
    require(sha(ROOT / PROOF / 'manifest.json')
            == 'a9fca306da2b3694b235933c24deb2aa28254984e6fe838b7d734b59cd6c03cf', 'Frozen GEMM proof packet changed')
    proof = read(ROOT / PROOF / 'results.json')
    require(proof['independent_source_bound_development_proofs'] == 1
            and proof['retained_positive_Main_checks'] == 4 and proof['positive_rechecks'] == 3
            and proof['owned_module_builds_across_four_checks'] == 20
            and proof['direct_Lean_negative_controls'] == 4 and proof['negative_timeouts'] == 0
            and proof['shapes'] == [[64, 256], [256, 512], [64, 512]] and proof['PTX_instructions'] == 171
            and proof['unchanged_CUDA_contract_fuel'] == [1030, 1, 1, 1]
            and proof['new_registered_source_certificates'] == 0
            and proof['original_paper_fully_reproduced'] is proof['nvidia_execution'] is False,
            'Completed GEMM proof scope differs')
    require(sha(ROOT / 'reproduction/paper_results/snapshots/20261113-v24/manifest.json')
            == '1fc1061662eaa4cd9a0fdc8bbdf9e6c7daca3b6a8ba5284f9ca8bcce80371abc', 'Existing v24 snapshot changed')
    publication = read(ROOT / PUBLICATION / 'results.json')
    binding = read(ROOT / PUBLICATION / 'binding.json')
    require(publication['source_commit'] == SOURCE and publication['all_downloads_match_committed_bytes'] is True
            and publication['tls_verification'] is True and publication['authorization_header'] is False
            and publication['archives_checked'] == 5 and publication['archive_members_checked'] == 382
            and publication['owned_source_bindings_checked'] == 55
            and publication['prior_failed_source_CI_runs_retained'] == 1
            and publication['original_paper_fully_reproduced'] is False
            and binding['verifier_sha256'] == sha(ROOT / PUBLICATION / 'verifier.py')
            and binding['observed_exit_code'] == 0
            and binding['prior_failed_source_CI_runs_retained'] == 1
            and binding['anonymous_results_sha256'] == sha(ROOT / PUBLICATION / 'results.json')
            and binding['proof_packet_manifest_sha256'] == sha(ROOT / PROOF / 'manifest.json'),
            'Actual public proof/source verification binding differs')
    records = publication['downloaded_files']
    public_paths = set(call(['git', 'diff', '--name-only', OLD, SOURCE]).splitlines())
    require(len(records) == len(public_paths) == 59 and {r['path'] for r in records} == public_paths
            and publication['total_downloaded_bytes'] == sum(r['bytes'] for r in records) == 22753879,
            'All newly published source/evidence paths required')
    for row in records:
        committed = subprocess.check_output(['git', 'show', SOURCE + ':' + row['path']], cwd=ROOT, timeout=60)
        require(row['http_status'] == 200 and row['curl_ssl_verify_result'] == 0
                and row['authorization_header'] is False and row['tls_verification'] is True
                and row['matches_committed_bytes'] is True and len(committed) == row['bytes']
                and hashlib.sha256(committed).hexdigest() == row['sha256'], 'Anonymous exact source bytes differ')
    jobs_section = (ROOT / '.github/workflows/ci.yml').read_text().split('\njobs:\n', 1)[1]
    names = set(re.findall(r'^  ([a-z][a-z0-9-]*):$', jobs_section, re.M))
    require(len(names) == 21 and 'paper-ledger' in names and 'proof-tests' in names, 'All actual twenty-one jobs required')
    receipt = read(ROOT / CI / 'results.json')
    require(receipt['source_commit'] == SOURCE and receipt['run_id'] == RUN
            and receipt['successful_jobs'] == 21 and set(receipt['expected_jobs']) == names, 'Recorded source CI differs')
    ci = json.loads(call(['gh', 'run', 'view', str(RUN), '--repo', 'harsh-nod/lark',
                         '--json', 'status,conclusion,headSha,jobs,url']))
    require(ci['headSha'] == SOURCE and ci['status'] == 'completed' and ci['conclusion'] == 'success'
            and len(ci['jobs']) == 21 and {j['name'] for j in ci['jobs']} == names
            and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in ci['jobs']),
            'All twenty-one actual GEMM source CI jobs must be freshly observed passed')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha'] == OLD,
            'Remote main changed')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/reproduction/ptx-matrix-refinement']))
            ['object']['sha'] == target, 'Published candidate branch differs')
    state = {'schema': 1, 'status': 'GEMM-main-all-gates-passed-update-pending',
             'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'source_checkpoint': SOURCE,
             'source_CI_executed_for_promoted_commit': False, 'old_main': OLD, 'promoted_commit': target,
             'source_ci': ci, 'changed_paths_after_checked_source': changed, 'checks': {
                 'actual21_GEMM_source_jobs_all_success': True,
                 'all_other_code_Lean_tests_workflow_and_snapshots_identical_to_CI_source': True,
                 'core1_kernel4_Main_checks20_module_builds4_Lean_controls_scope_bound': True,
                 'all59_public_changed_files_anonymous_TLS_exact_source_bytes': True,
                 'five_public_archives382_members55_wheel_source_bindings_verified': True,
                 'v24_snapshot_preserved': True, 'clean_main_candidate_and_ancestry_checked': True},
             'model_calls_by_promotion': 0, 'fresh_lean_checks_by_promotion': 0,
             'gpu_trials_by_promotion': 0, 'original_paper_fully_reproduced': False, 'helper_sha256': sha(Path(__file__))}
    if args.check_only:
        print(json.dumps({'status': 'GEMM-main-preflight-passed', 'source_ci_jobs': 21,
                          'receipt_docs_delta_files': len(changed), 'anonymous_files': 59}))
        return
    OUT.mkdir(exist_ok=False)
    write(OUT / 'progress.json', state)
    write(OUT / 'update.json', {'sha': target, 'force': False})
    state['remote_update'] = json.loads(call(['gh', 'api', '--method', 'PATCH',
        'repos/harsh-nod/lark/git/refs/heads/main', '--input', str(OUT / 'update.json')]))
    require(state['remote_update']['object']['sha'] == target, 'Remote update differs')
    state['status'] = 'GEMM-remote-main-fast-forwarded-local-pending'
    write(OUT / 'progress.json', state)
    state['local_merge'] = call(['git', 'merge', '--ff-only', target], MAIN)
    subprocess.run(['git', 'update-ref', 'refs/remotes/origin/main', target, OLD], cwd=ROOT, check=True)
    require(call(['git', 'rev-parse', 'HEAD'], MAIN) == target
            and not call(['git', 'status', '--porcelain'], MAIN), 'Local main differs after update')
    state['status'] = 'GEMM-main-fast-forward-complete'
    write(OUT / 'results.json', state)
    print(json.dumps({'status': state['status'], 'main': target, 'source_ci_jobs': 21,
                      'original_paper_fully_reproduced': False}))


if __name__ == '__main__':
    main()
