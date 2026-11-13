"""Gate a non-force main fast-forward on actual BMM CI and public proof bytes."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess

ROOT = Path('/tmp/lark-ptx-batched-refinement-20261113')
MAIN = Path('/home/harsh/lark')
OUT = Path('/tmp/lark-ptx-batched-ci-main-v1-20261113')
SOURCE = '6978f098e1f628f9a1507b0858c005624f95f1d2'
OLD = 'f1dd8c2751e1b4f79c55d7e90c6b8466d8c691d8'
RUN = 43521648124
BASE = 'reproduction/ptx/results/'
PROOF = BASE + 'full-size-bmm-proof-v1'
PUBLICATION = BASE + 'full-size-bmm-proof-publication-v1'
CI = BASE + 'full-size-bmm-proof-ci-v1'
ARTIFACT = 'reproduction/paper_results/original-artifact-observation-bmm-20261113-v1'
DOC = 'reproduction/ptx/BATCHED.md'
BEFORE = (
    'the actual failed intermediate export and selected development history. Anonymous\n'
    'publication and actual source CI are still being completed. This is one\n'
    'independent development kernel, not an original optimized program or model-cohort\n'
    'result.\n'
)
AFTER = (
    'the actual failed intermediate export and selected development history. Anonymous\n'
    'publication and all twenty-two source CI jobs passed. This is one independent\n'
    'development kernel, not an original optimized program or model-cohort result.\n'
    '\nThe [anonymous publication record](results/full-size-bmm-proof-publication-v1/results.json)\n'
    'matched all 58 changed files (55,129,306 bytes) to source `6978f09`, with TLS\n'
    'verification enabled. All nine archives, 702 archive members and 60 current\n'
    'SDK/Lean source bindings were checked, including the wheel and earlier\n'
    'renderer at its own source revision. Publication repeated no Lean, model or\n'
    'GPU experiment.\n'
    '\nThe [actual source CI record](results/full-size-bmm-proof-ci-v1/results.json)\n'
    'records all twenty-two jobs passing at source `6978f09`, including the\n'
    'separate complete BMM cold export/replay, four direct source controls, SDK\n'
    'adversarial tests and all existing checks. The later receipt commit changes\n'
    'only this document and recorded receipts; all SDK, Lean, tests, workflow\n'
    'and frozen snapshots retain their exact tested source identities.\n'
    '\nA [bounded original-artifact observation](../paper_results/original-artifact-observation-bmm-20261113-v1/results.json)\n'
    'still found the named KernelCraft repository empty and the abstract page\n'
    'listing manuscript v1. It retains the initial anonymous-search rate limit\n'
    'and a read-only authenticated fallback. These observations do not establish\n'
    'global artifact absence or reproduce any scientific result.\n'
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
    require(folder.is_dir() and not any(p.is_symlink() for p in folder.rglob('*')),
            'Receipt folder missing or contains a symlink')
    files = {p.name: sha(p) for p in folder.iterdir() if p.is_file() and p.name != 'manifest.json'}
    require(files == read(folder / 'manifest.json')
            and len(list(folder.iterdir())) == len(files) + 1,
            'Exact folder inventory differs: ' + prefix)
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
            and call(['git', 'branch', '--show-current'], MAIN) == 'main'
            and not call(['git', 'status', '--porcelain'], MAIN), 'Clean local main changed')
    require(call(['git', 'rev-parse', 'refs/remotes/origin/main']) == OLD, 'Tracking main changed')
    for ancestor in (OLD, SOURCE):
        subprocess.run(['git', 'merge-base', '--is-ancestor', ancestor, target], cwd=ROOT, check=True)
    expected = {DOC} | checked_folder(PUBLICATION) | checked_folder(CI) | checked_folder(ARTIFACT)
    changed = call(['git', 'diff', '--name-only', SOURCE, target]).splitlines()
    require(set(changed) == expected and len(changed) == 25,
            'Only exact publication/CI/artifact receipts and BMM document may follow checked source')
    source_doc = subprocess.check_output(['git', 'show', SOURCE + ':' + DOC], cwd=ROOT).decode()
    require(source_doc.count(BEFORE) == 1 and (ROOT / DOC).read_text()
            == source_doc.replace(BEFORE, AFTER), 'Exact receipt paragraphs required')
    checked_folder(PROOF)
    require(sha(ROOT / PROOF / 'manifest.json')
            == 'e190d3b77b54d4dc57f5d1bf67885af8aec839acbff2aab86645704c466b7bf8',
            'Frozen BMM proof packet changed')
    proof = read(ROOT / PROOF / 'results.json')
    require(proof['independent_source_bound_development_proofs'] == 1
            and proof['retained_positive_Main_checks'] == 5 and proof['positive_rechecks'] == 4
            and proof['current_SDK_positive_Main_checks'] == 4
            and proof['initial_SDK_positive_Main_checks'] == 1
            and proof['owned_module_builds_across_four_current_checks'] == 32
            and proof['owned_module_builds_across_five_successful_official_checks'] == 40
            and proof['retained_failed_official_exports'] == 1
            and proof['direct_Lean_negative_controls'] == 4 and proof['negative_timeouts'] == 0
            and proof['owned_source_files'] == 60
            and proof['shapes'] == [[32, 64, 256], [32, 256, 512], [32, 64, 512]]
            and proof['PTX_instructions'] == 138
            and proof['unchanged_CUDA_contract_fuel'] == [1030, 1, 1, 1]
            and proof['new_registered_source_certificates'] == 0
            and proof['original_paper_fully_reproduced'] is proof['nvidia_execution'] is False,
            'Completed BMM proof scope differs')
    require(sha(ROOT / 'reproduction/paper_results/snapshots/20261113-v25/manifest.json')
            == 'e90502aaaedfacbea8c0ded36ad8facd8adf1870c755c3b5a38de321dead572f',
            'Existing v25 snapshot changed')
    publication = read(ROOT / PUBLICATION / 'results.json')
    binding = read(ROOT / PUBLICATION / 'binding.json')
    require(publication['source_commit'] == SOURCE
            and publication['all_downloads_match_committed_bytes'] is True
            and publication['tls_verification'] is True and publication['authorization_header'] is False
            and publication['archives_checked'] == 9 and publication['archive_members_checked'] == 702
            and publication['owned_source_bindings_checked'] == 60
            and publication['earlier_failed_official_exports_retained'] == 1
            and publication['original_paper_fully_reproduced'] is False
            and binding['source_commit'] == SOURCE
            and binding['verifier_sha256'] == sha(ROOT / PUBLICATION / 'verifier.py')
            and binding['observed_exit_code'] == 0
            and binding['anonymous_results_sha256'] == sha(ROOT / PUBLICATION / 'results.json')
            and binding['proof_packet_manifest_sha256'] == sha(ROOT / PROOF / 'manifest.json'),
            'Actual public proof/source verification binding differs')
    records = publication['downloaded_files']
    public_paths = set(call(['git', 'diff', '--name-only', OLD, SOURCE]).splitlines())
    require(len(records) == len(public_paths) == 58 and {r['path'] for r in records} == public_paths
            and publication['total_downloaded_bytes'] == sum(r['bytes'] for r in records) == 55129306,
            'All newly published source/evidence paths required')
    for row in records:
        committed = subprocess.check_output(['git', 'show', SOURCE + ':' + row['path']], cwd=ROOT, timeout=60)
        require(row['http_status'] == 200 and row['curl_ssl_verify_result'] == 0
                and row['authorization_header'] is False and row['tls_verification'] is True
                and row['matches_committed_bytes'] is True and len(committed) == row['bytes']
                and hashlib.sha256(committed).hexdigest() == row['sha256'],
                'Anonymous exact source bytes differ')
    observation = read(ROOT / ARTIFACT / 'results.json')
    require(observation['kernelcraft']['full_name'] == 'AICrossSim/KernelCraft'
            and observation['kernelcraft']['size'] == 0
            and observation['default_ref_status'] == 409
            and observation['initial_anonymous_search_rate_limit_retained'] is True
            and observation['authenticated_read_only_fallback_used'] is True
            and observation['original_paper_fully_reproduced'] is False,
            'Bounded artifact observation scope differs')
    jobs_section = (ROOT / '.github/workflows/ci.yml').read_text().split('\njobs:\n', 1)[1]
    names = set(re.findall(r'^  ([a-z][a-z0-9-]*):$', jobs_section, re.M))
    require(len(names) == 22 and {'paper-ledger', 'proof-tests', 'ptx-batched'} <= names,
            'All actual twenty-two jobs required')
    receipt = read(ROOT / CI / 'results.json')
    require(receipt['source_commit'] == SOURCE and receipt['run_id'] == RUN
            and receipt['status'] == 'exact-source-CI-all-22-passed'
            and receipt['successful_jobs'] == 22 and set(receipt['expected_jobs']) == names,
            'Recorded source CI differs')
    ci = json.loads(call(['gh', 'api', f'repos/harsh-nod/lark/actions/runs/{RUN}']))
    jobs = json.loads(call(['gh', 'api', f'repos/harsh-nod/lark/actions/runs/{RUN}/jobs?per_page=100']))
    require(ci['head_sha'] == SOURCE and ci['status'] == 'completed' and ci['conclusion'] == 'success'
            and ci['head_branch'] == 'reproduction/ptx-batched-refinement'
            and ci['event'] == 'push' and ci['name'] == 'Verify'
            and jobs['total_count'] == len(jobs['jobs']) == 22
            and {j['name'] for j in jobs['jobs']} == names
            and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs['jobs']),
            'All twenty-two actual BMM source CI jobs must be freshly observed passed')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha'] == OLD,
            'Remote main changed')
    require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/reproduction/ptx-batched-refinement']))
            ['object']['sha'] == target, 'Published candidate branch differs')
    state = {'schema': 1, 'status': 'BMM-main-all-gates-passed-update-pending',
             'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'source_checkpoint': SOURCE,
             'source_CI_executed_for_promoted_commit': False, 'old_main': OLD, 'promoted_commit': target,
             'source_ci': ci, 'source_ci_jobs': jobs, 'changed_paths_after_checked_source': changed,
             'checks': {
                 'actual22_BMM_source_jobs_all_success': True,
                 'all_other_code_Lean_tests_workflow_and_snapshots_identical_to_CI_source': True,
                 'one_kernel_five_official_Main_checks_four_current_checks32_fresh_modules_bound': True,
                 'all58_public_changed_files_anonymous_TLS_exact_source_bytes': True,
                 'nine_public_archives702_members60_wheel_source_bindings_verified': True,
                 'v25_snapshot_preserved': True, 'bounded_original_artifact_observation_retained': True,
                 'clean_main_candidate_and_ancestry_checked': True},
             'model_calls_by_promotion': 0, 'fresh_lean_checks_by_promotion': 0,
             'gpu_trials_by_promotion': 0, 'original_paper_fully_reproduced': False,
             'helper_sha256': sha(Path(__file__))}
    if args.check_only:
        print(json.dumps({'status': 'BMM-main-preflight-passed', 'source_ci_jobs': 22,
                          'receipt_docs_delta_files': len(changed), 'anonymous_files': 58}))
        return
    OUT.mkdir(exist_ok=False)
    write(OUT / 'progress.json', state)
    write(OUT / 'update.json', {'sha': target, 'force': False})
    state['remote_update'] = json.loads(call(['gh', 'api', '--method', 'PATCH',
        'repos/harsh-nod/lark/git/refs/heads/main', '--input', str(OUT / 'update.json')]))
    require(state['remote_update']['object']['sha'] == target, 'Remote update differs')
    state['status'] = 'BMM-remote-main-fast-forwarded-local-pending'
    write(OUT / 'progress.json', state)
    state['local_merge'] = call(['git', 'merge', '--ff-only', target], MAIN)
    subprocess.run(['git', 'update-ref', 'refs/remotes/origin/main', target, OLD], cwd=ROOT, check=True)
    require(call(['git', 'rev-parse', 'HEAD'], MAIN) == target
            and not call(['git', 'status', '--porcelain'], MAIN), 'Local main differs after update')
    state['status'] = 'BMM-main-fast-forward-complete'
    write(OUT / 'results.json', state)
    print(json.dumps({'status': state['status'], 'main': target, 'source_ci_jobs': 22,
                      'original_paper_fully_reproduced': False}))


if __name__ == '__main__':
    main()
