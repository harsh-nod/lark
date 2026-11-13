import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path('/tmp/lark-full-shape-cuda-models-20261113')
MAIN = Path('/home/harsh/lark')
OLD = '51147a3d63127ee11549a570f2910d67eecb7101'
SOURCE = '1b22551bc295431707dc81288a57ac9a2e6f9475'
TARGET = 'cd3185a32bc1611cb75229d90a955fe0c49a5c34'
OUT = Path('/tmp/lark-full-shape-cuda-ci-main-v1-20261113')
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

def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')

def packet(name):
    root = BASE / name
    manifest = read(root / 'manifest.json')
    require({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
            == set(manifest) | {'manifest.json'}, 'Packet inventory differs: ' + name)
    require(all(sha(root / n) == h for n, h in manifest.items()), 'Packet bytes differ: ' + name)
    return read(root / 'results.json')

parser = argparse.ArgumentParser()
parser.add_argument('--check-only', action='store_true')
args = parser.parse_args()
ci = json.loads(call(['gh', 'run', 'view', '43366990885', '--repo', 'harsh-nod/lark',
                      '--json', 'status,conclusion,headSha,jobs,url']))
prior = packet('full-shape-auditor-ci-main-v1')
expected = {j['name'] for j in prior['source_ci']['jobs']}
require(ci['headSha'] == SOURCE and len(ci['jobs']) == len(expected) == 18
        and {j['name'] for j in ci['jobs']} == expected, 'Exact-source CI roster differs')
ready = ci['status'] == 'completed' and ci['conclusion'] == 'success' and all(
    j['status'] == 'completed' and j['conclusion'] == 'success' for j in ci['jobs'])
require(call(['git', 'rev-parse', 'HEAD']) == TARGET
        and not call(['git', 'status', '--porcelain']), 'Candidate checkout changed')
require(call(['git', 'rev-parse', 'HEAD'], MAIN) == OLD
        and not call(['git', 'status', '--porcelain'], MAIN), 'Main checkout changed')
require(call(['git', 'rev-parse', 'refs/remotes/origin/main']) == OLD, 'Tracking main changed')
for ancestor in (SOURCE, OLD):
    subprocess.run(['git', 'merge-base', '--is-ancestor', ancestor, TARGET], cwd=ROOT, check=True)
names = ('full-shape-cuda-controller-validation-v1', 'full-shape-cuda-context-preflight-v1',
         'full-shape-auditor-ci-main-v1', 'full-shape-pilot-replay-v1',
         'full-shape-runtime-deepseek-v1', 'full-shape-source-ci-main-v1',
         'full-shape-runtime-publication-v1', 'full-shape-cuda-publication-v1')
allowed = tuple('reproduction/local_models/results/' + n + '/' for n in names)
changed = call(['git', 'diff', '--name-only', SOURCE, TARGET]).splitlines()
require(changed and all(n == 'reproduction/local_models/README.md' or n.startswith(allowed)
                        for n in changed), 'Post-CI delta is not README and recorded evidence')
protected = ['lark_kernels', 'lean', 'lean-real', 'tests', '.github', 'pyproject.toml',
             'reproduction/local_models/cuda_shape.py', 'reproduction/local_models/full_shape.py',
             'reproduction/local_models/full_shape_run.py',
             'reproduction/local_models/audit_full_shape.py',
             'reproduction/local_models/FULL_SHAPE_METHOD.md']
require(not call(['git', 'diff', '--name-only', SOURCE, TARGET, '--', *protected]),
        'Checked implementation, tests, methods, Lean or workflows changed')
prep = packet('full-shape-cuda-preparation-v1')
require(prep['language'] == 'cuda' and prep['native_warp'] == 32
        and prep['sdk_positive_lean_checks'] == prep['masked_negative_lean_checks'] == 17
        and prep['source_files'] == 145 and prep['frozen_files'] == 268
        and prep['all_request_proof_slots_masked'] is True
        and prep['existing_buffers_dtypes_and_fuels_preserved'] is True
        and prep['limits'] == {'maxRecDepth': 10000, 'maxHeartbeats': 2000000,
                               'lean_timeout_seconds': 180}
        and prep['preparation_manifest_sha256'] ==
        '6476ec66614e412a122654036b6bd66fab67b23007d7fc26181cdff7571f34c2',
        'CUDA preparation scope differs')
with tarfile.open(BASE / 'full-shape-cuda-preparation-v1/preparation.tar.gz', 'r:gz') as archive:
    members = archive.getmembers()
    raw = archive.extractfile('manifest.json').read()
    require(len(members) == 268 and all(m.isfile() for m in members)
            and hashlib.sha256(raw).hexdigest() == prep['preparation_manifest_sha256'],
            'Frozen CUDA preparation inventory or pin differs')
validation = packet('full-shape-cuda-controller-validation-v1')
require(validation['source_checkpoint'] == SOURCE and validation['final_test_methods_passed'] == 21
        and validation['real_model_inference_calls'] == validation['new_cuda_model_proofs'] == 0
        and validation['historical_pilot_replayed_requests'] == 4
        and validation['historical_model_proofs_freshly_rechecked'] == 1
        and validation['historical_fresh_kernel_checks'] == 2
        and all(sha(ROOT / n) == h for n, h in validation['source_sha256'].items()),
        'Final controller validation scope or sources differ')
context = packet('full-shape-cuda-context-preflight-v1')
require(context['source_checkpoint'] == SOURCE and context['source_language'] == 'cuda'
        and context['tokenization_requests'] == 34 and context['model_inference_calls'] == 0
        and context['context_limit'] == 65536
        and [(x['cases'], x['max_initial_prompt_tokens']) for x in context['models']]
        == [(17, 22496), (17, 23001)], 'CUDA context evidence differs')
publication = packet('full-shape-cuda-publication-v1')
require(publication['source_commit'] == '5163d9cb2e04718c3811f3cccee3121e663ad962'
        and len(publication['downloaded_files']) == 18
        and publication['total_downloaded_bytes'] == 949916
        and publication['tls_verification'] is True and publication['authorization_header'] is False
        and publication['all_downloads_match_committed_bytes'] is True
        and all(x['curl_ssl_verify_result'] == 0 and x['tls_verification'] is True
                and x['authorization_header'] is False and x['matches_committed_bytes'] is True
                and sha(ROOT / x['path']) == x['sha256'] for x in publication['downloaded_files']),
        'Anonymous publication evidence differs')
require(prior['promoted_commit'] == OLD and all(
    x['original_paper_fully_reproduced'] is False for x in (prior, prep, validation, context, publication)),
    'Unsupported paper completion or previous-main claim')
require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha']
        == OLD, 'Remote main changed')
require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/commits/' + TARGET]))['sha']
        == TARGET, 'Candidate is not published')
if args.check_only:
    print(json.dumps({'status': 'full-size-cuda-main-gate-preflight-checked',
                      'source_ci_ready': ready,
                      'passed_jobs': sum(j['conclusion'] == 'success' for j in ci['jobs']),
                      'post_ci_receipt_paths': len(changed), 'new_cuda_model_proofs': 0}))
    raise SystemExit(0)
require(ready, 'All eighteen exact-source CI jobs must pass; no mutation performed')
OUT.mkdir(exist_ok=False)
state = {'schema': 1, 'status': 'full-size-cuda-gates-passed-main-update-pending',
         'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'source_checkpoint': SOURCE,
         'old_main': OLD, 'promoted_commit': TARGET, 'source_ci': ci,
         'post_source_receipt_paths': changed,
         'checks': {'all18_named_jobs_success': True, 'clean_main_and_candidate': True,
          'old_main_and_source_ancestors': True, 'protected_checked_sources_unchanged': True,
          'cuda17_positive17_negative_proofs': True, 'final21_tests_and_fresh_legacy_proof_checks': True,
          'both_owned_tokenizers_fit17_cuda_tasks': True,
          'anonymous18_file949916_byte_verified_TLS_publication': True},
         'model_calls_by_promotion': 0, 'gpu_trials_by_promotion': 0,
         'new_registered_certificates_by_promotion': 0, 'new_cuda_model_proofs': 0,
         'original_paper_fully_reproduced': False}
write(OUT / 'progress.json', state)
write(OUT / 'update.json', {'sha': TARGET, 'force': False})
state['remote_update'] = json.loads(call(['gh', 'api', '--method', 'PATCH',
    'repos/harsh-nod/lark/git/refs/heads/main', '--input', str(OUT / 'update.json')]))
require(state['remote_update']['object']['sha'] == TARGET, 'Remote main update differs')
state['status'] = 'full-size-cuda-remote-main-fast-forwarded-local-pending'
write(OUT / 'progress.json', state)
state['local_merge'] = call(['git', 'merge', '--ff-only', TARGET], MAIN)
subprocess.run(['git', 'update-ref', 'refs/remotes/origin/main', TARGET, OLD], cwd=ROOT, check=True)
require(call(['git', 'rev-parse', 'HEAD'], MAIN) == TARGET
        and not call(['git', 'status', '--porcelain'], MAIN), 'Local main differs')
state.update(status='full-size-cuda-source-ci-main-fast-forward-complete',
             helper_sha256=sha(Path(__file__)))
write(OUT / 'results.json', state)
print(json.dumps({'status': state['status'], 'main': TARGET, 'source_ci_jobs': 18,
                  'new_cuda_model_proofs': 0}))
