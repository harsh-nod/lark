import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path('/tmp/lark-full-shape-run-audit-20261113')
MAIN = Path('/home/harsh/lark')
OLD = 'bb114d8ae61183320242fa5f4463d0cfc727bcd1'
SOURCE = 'a582d6da15afd2ff1dba0a1a9fded4ac1bb07e37'
TARGET = '51147a3d63127ee11549a570f2910d67eecb7101'
OUT = Path('/tmp/lark-full-shape-auditor-ci-main-v1-20261113')
BASE = ROOT / 'reproduction/local_models/results'

def require(ok, message):
    if not ok:
        raise ValueError(message)

def call(argv, cwd=ROOT):
    return subprocess.check_output(argv, cwd=cwd, text=True, timeout=60).strip()

def read(path):
    return json.loads(path.read_text())

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')

def packet(name):
    folder = BASE / name
    manifest = read(folder / 'manifest.json')
    require({str(p.relative_to(folder)) for p in folder.rglob('*') if p.is_file()}
            == set(manifest) | {'manifest.json'}, 'Packet inventory differs: ' + name)
    require(all(sha(folder / n) == digest for n, digest in manifest.items()),
            'Frozen packet changed: ' + name)
    return read(folder / 'results.json')

parser = argparse.ArgumentParser()
parser.add_argument('--check-only', action='store_true')
args = parser.parse_args()
ci = json.loads(call(['gh', 'run', 'view', '43364220881', '--repo', 'harsh-nod/lark',
                      '--json', 'status,conclusion,headSha,jobs,url']))
prior = packet('full-shape-source-ci-main-v1')
expected = {j['name'] for j in prior['source_ci']['jobs']}
require(ci['headSha'] == SOURCE and len(ci['jobs']) == len(expected) == 18
        and {j['name'] for j in ci['jobs']} == expected, 'Exact-source CI roster differs')
ready = ci['status'] == 'completed' and ci['conclusion'] == 'success' and all(
    j['status'] == 'completed' and j['conclusion'] == 'success' for j in ci['jobs'])
require(call(['git', 'rev-parse', 'HEAD']) == TARGET
        and not call(['git', 'status', '--porcelain']), 'Candidate checkout changed')
require(call(['git', 'rev-parse', 'HEAD'], MAIN) == OLD
        and not call(['git', 'status', '--porcelain'], MAIN), 'Main checkout changed')
require(call(['git', 'rev-parse', 'refs/remotes/origin/main']) == OLD,
        'Tracking main changed')
for ancestor in (SOURCE, OLD):
    subprocess.run(['git', 'merge-base', '--is-ancestor', ancestor, TARGET], cwd=ROOT, check=True)
allowed = tuple('reproduction/local_models/results/' + name + '/' for name in (
    'full-shape-runtime-deepseek-v1', 'full-shape-pilot-replay-v1',
    'full-shape-source-ci-main-v1', 'full-shape-runtime-publication-v1'))
changed = call(['git', 'diff', '--name-only', SOURCE, TARGET]).splitlines()
require(changed and all(p == 'reproduction/local_models/README.md' or p.startswith(allowed)
                        for p in changed), 'Post-CI delta is not the recorded packets and README')
require(not call(['git', 'diff', '--name-only', SOURCE, TARGET, '--', 'lark_kernels',
                  'lean', 'lean-real', 'tests', '.github', 'pyproject.toml',
                  'reproduction/local_models/audit_full_shape.py',
                  'reproduction/local_models/full_shape.py',
                  'reproduction/local_models/full_shape_run.py']), 'Protected checked source changed')
runtime = packet('full-shape-runtime-deepseek-v1')
require(runtime['source_checkpoint'] == SOURCE and runtime['context_preflight_cases'] == 17
        and runtime['checkpoint_weights_rehashed'] == 48
        and runtime['checkpoint_support_files_rehashed'] == 31
        and runtime['context_archive_files'] == 51
        and runtime['max_initial_prompt_tokens'] == 22979
        and runtime['warmup_reported_tokens']['total_tokens'] == 69
        and runtime['proof_experiment_results_included'] is False,
        'DeepSeek setup evidence differs')
replay = packet('full-shape-pilot-replay-v1')
binding = read(BASE / 'full-shape-pilot-replay-v1/binding.json')
require(binding['source_checkpoint'] == SOURCE
        and binding['auditor_sha256'] == replay['auditor_sha256'] ==
        sha(ROOT / 'reproduction/local_models/audit_full_shape.py')
        and binding['tests_sha256'] == sha(ROOT / 'tests/test_full_shape_audit.py')
        and binding['regression_test_methods_passed'] == 10
        and binding['pilot_archive_sha256'] == sha(BASE / 'full-shape-pilot-glm53-v1/pilot.tar.gz')
        and binding['preparation_archive_sha256'] == sha(BASE / 'full-shape-preparation-v2/preparation.tar.gz')
        and len(replay['bound_model_requests']) == 4
        and replay['recorded_verified_model_proofs'] == replay['freshly_verified_model_proofs'] == 1
        and len(replay['fresh_accepted_proof_kernel_checks']) == 2
        and replay['complete_17_case_cohort'] is False and replay['model_calls_by_audit'] == 0,
        'Fresh pilot replay scope or source binding differs')
with tarfile.open(BASE / 'full-shape-pilot-replay-v1/replay.tar.gz', 'r:gz') as archive:
    for folder in replay['fresh_accepted_proof_kernel_checks']:
        data = archive.extractfile(folder + '/Main.lean').read()
        require(hashlib.sha256(data).hexdigest() ==
                '727675f34646dad23bba96f3b005623c612f33edcc74f039aa2e3f0ef4f831c1',
                'Fresh recheck Main differs from the actual model pilot')
publication = packet('full-shape-runtime-publication-v1')
require(publication['source_commit'] == '18e114b908d109c2f7e06e7e00fd76f68f142040'
        and len(publication['downloaded_files']) == 25
        and publication['total_downloaded_bytes'] == 459721
        and publication['all_downloads_match_committed_bytes'] is True
        and publication['tls_verification'] is True and publication['authorization_header'] is False
        and all(o['tls_verification'] is True and o['curl_ssl_verify_result'] == 0
                and o['authorization_header'] is False and o['matches_committed_bytes'] is True
                and sha(ROOT / o['path']) == o['sha256'] for o in publication['downloaded_files']),
        'Anonymous publication evidence differs')
require(all(x['original_paper_fully_reproduced'] is False
            for x in (runtime, replay, binding, publication, prior)), 'Unsupported original-paper claim')
require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha']
        == OLD, 'Remote main changed')
require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/commits/' + TARGET]))['sha']
        == TARGET, 'Candidate is not published')
if args.check_only:
    print(json.dumps({'status': 'full-size-auditor-main-gate-preflight-checked',
                      'source_ci_ready': ready,
                      'passed_jobs': sum(j['conclusion'] == 'success' for j in ci['jobs']),
                      'post_ci_receipt_paths': len(changed), 'full_cohorts_complete': False}))
    raise SystemExit(0)
require(ready, 'All eighteen exact-source CI jobs must pass; no mutation performed')
OUT.mkdir(exist_ok=False)
state = {'schema': 1, 'status': 'full-size-auditor-gates-passed-main-update-pending',
         'checked_at_utc': datetime.now(timezone.utc).isoformat(),
         'source_checkpoint': SOURCE, 'old_main': OLD, 'promoted_commit': TARGET,
         'source_ci': ci, 'post_source_receipt_paths': changed,
         'checks': {'all18_named_jobs_success': True, 'clean_main_and_candidate': True,
          'old_main_and_source_ancestors': True, 'protected_checked_sources_unchanged': True,
          'final_pilot_replay_two_fresh_kernel_checks': True,
          'anonymous25_file459721_byte_verified_TLS_publication': True},
         'model_calls_by_promotion': 0, 'gpu_trials_by_promotion': 0,
         'new_registered_certificates_by_promotion': 0,
         'full_17_case_cohorts_complete': False, 'original_paper_fully_reproduced': False}
write(OUT / 'progress.json', state)
write(OUT / 'update.json', {'sha': TARGET, 'force': False})
state['remote_update'] = json.loads(call(['gh', 'api', '--method', 'PATCH',
    'repos/harsh-nod/lark/git/refs/heads/main', '--input', str(OUT / 'update.json')]))
require(state['remote_update']['object']['sha'] == TARGET, 'Remote main update differs')
state['status'] = 'full-size-auditor-remote-main-fast-forwarded-local-pending'
write(OUT / 'progress.json', state)
state['local_merge'] = call(['git', 'merge', '--ff-only', TARGET], MAIN)
subprocess.run(['git', 'update-ref', 'refs/remotes/origin/main', TARGET, OLD], cwd=ROOT, check=True)
require(call(['git', 'rev-parse', 'HEAD'], MAIN) == TARGET
        and not call(['git', 'status', '--porcelain'], MAIN), 'Local main differs')
state.update(status='full-size-auditor-source-ci-main-fast-forward-complete',
             helper_sha256=sha(Path(__file__)))
write(OUT / 'results.json', state)
print(json.dumps({'status': state['status'], 'main': TARGET, 'source_ci_jobs': 18,
                  'full_cohorts_complete': False}))
