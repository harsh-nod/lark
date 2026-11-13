import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path('/tmp/lark-full-shape-models-20261112')
MAIN = Path('/home/harsh/lark')
OLD = 'b62b3cc43e3edb0bd17368ebcb4fdfd4a4800e25'
SOURCE = 'bb114d8ae61183320242fa5f4463d0cfc727bcd1'
OUT = Path('/tmp/lark-full-shape-models-ci-main-v1-20261113')
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
    mf = read(folder / 'manifest.json')
    require(all(sha(folder / n) == digest for n, digest in mf.items()),
            'Frozen packet changed: ' + name)
    return read(folder / 'results.json')

parser = argparse.ArgumentParser()
parser.add_argument('--check-only', action='store_true')
args = parser.parse_args()
ci = json.loads(call(['gh', 'run', 'view', '43361208335', '--repo', 'harsh-nod/lark',
                      '--json', 'status,conclusion,headSha,jobs,url']))
previous = read(MAIN / 'reproduction/paper_results/snapshot-v22-ci-main-v1/results.json')
expected = {j['name'] for j in previous['source_ci']['jobs']}
require(ci['headSha'] == SOURCE and len(ci['jobs']) == len(expected) == 18
        and {j['name'] for j in ci['jobs']} == expected, 'Exact-source CI roster differs')
ready = ci['status'] == 'completed' and ci['conclusion'] == 'success' and all(
    j['status'] == 'completed' and j['conclusion'] == 'success' for j in ci['jobs'])
require(call(['git', 'rev-parse', 'HEAD']) == SOURCE
        and not call(['git', 'status', '--porcelain']), 'Candidate checkout changed')
require(call(['git', 'rev-parse', 'HEAD'], MAIN) == OLD
        and not call(['git', 'status', '--porcelain'], MAIN), 'Main checkout changed')
require(call(['git', 'rev-parse', 'refs/remotes/origin/main']) == OLD,
        'Tracking main changed')
subprocess.run(['git', 'merge-base', '--is-ancestor', OLD, SOURCE], cwd=ROOT, check=True)
require(not call(['git', 'diff', '--name-only', OLD, SOURCE, '--', 'lean-real', '.github']),
        'Legacy real proofs or workflows changed')
changed_lean = call(['git', 'diff', '--name-only', OLD, SOURCE, '--', 'lean']).splitlines()
require(changed_lean == ['lean/Lark/ProofSyntax.lean'], 'Unexpected legacy Lean changes')
syntax = (ROOT / changed_lean[0]).read_text()
require(syntax.count('set_option maxRecDepth 10000') == 1
        and syntax.count('set_option maxHeartbeats 2000000') == 1,
        'New proof parser resource settings differ')
prep = packet('full-shape-preparation-v2')
require(prep['sdk_positive_lean_checks'] == prep['masked_negative_lean_checks'] == 17
        and prep['additional_syntax_negatives'] == 9
        and prep['all_request_proof_slots_masked'] is True
        and prep['frozen_files'] == 267
        and prep['preparation_manifest_sha256'] ==
        '82f84eec835c0deb27e618ddd6e3d75d9b1d3b8827bd1a4f1982de0d4e029db8'
        and prep['original_paper_fully_reproduced'] is False,
        'Preparation control scope differs')
controller = packet('full-shape-controller-validation-v1')
require(controller['selected_sdk_and_model_regression_tests']['passed'] == 39,
        'Checker regression receipt differs')
runtime = packet('full-shape-runtime-glm53-v1')
require(runtime['context_preflight_cases'] == 17
        and runtime['checkpoint_weights_rehashed'] == 141
        and runtime['checkpoint_support_files_rehashed'] == 8
        and runtime['external_api_spend_usd'] == 0, 'Runtime evidence differs')
pilot = packet('full-shape-pilot-glm53-v1')
binding = read(BASE / 'full-shape-pilot-glm53-v1/binding.json')
require(pilot['status'] == 'finished' and pilot['selected_cases'] == ['relu']
        and pilot['complete_17_case_cohort'] is False
        and pilot['cases'][0]['status'] == 'verified-proof'
        and binding['model_requests'] == 4 and binding['library_reads'] == 3
        and binding['raw_response_to_both_checked_mains_identical'] is True
        and binding['reported_usage']['total_tokens'] == 37567
        and binding['original_paper_fully_reproduced'] is False,
        'Pilot evidence or scope differs')
with tarfile.open(BASE / 'full-shape-pilot-glm53-v1/pilot.tar.gz', 'r:gz') as archive:
    members = {m.name: m for m in archive.getmembers()}
    require(len(members) == 46 and all(m.isfile() for m in members.values()),
            'Pilot archive roster differs')
    request = json.load(archive.extractfile('cases/relu/call-04/model/response.json'))
    require(request['choices'][0]['message'].get('content'), 'Missing model proof response')
    first = archive.extractfile('cases/relu/call-04/proof-check/Main.lean').read()
    second = archive.extractfile('cases/relu/call-04/independent-recheck/Main.lean').read()
    require(first == second and hashlib.sha256(first).hexdigest() ==
            '727675f34646dad23bba96f3b005623c612f33edcc74f039aa2e3f0ef4f831c1',
            'Accepted model Main differs')
require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha']
        == OLD, 'Remote main changed')
require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/commits/' + SOURCE]))['sha']
        == SOURCE, 'Candidate is not published')
if args.check_only:
    print(json.dumps({'status': 'full-size-model-main-gate-preflight-checked',
                      'source_ci_ready': ready,
                      'passed_jobs': sum(j['conclusion'] == 'success' for j in ci['jobs']),
                      'pilot_model_proofs': 1, 'full_cohort_complete': False}))
    raise SystemExit(0)
require(ready, 'All eighteen exact-source CI jobs must pass; no mutation performed')
OUT.mkdir(exist_ok=False)
state = {'schema': 1, 'status': 'full-size-model-gates-passed-main-update-pending',
         'checked_at_utc': datetime.now(timezone.utc).isoformat(),
         'source_checkpoint': SOURCE, 'old_main': OLD, 'promoted_commit': SOURCE,
         'source_ci': ci, 'checks': {'all18_named_jobs_success': True,
          'clean_main_and_candidate': True, 'old_main_ancestor': True,
          'legacy_lean_real_and_workflows_unchanged': True,
          'preparation_positive17_negative17_and_syntax9': True,
          'published_pilot_one_model_proof_bound_to_two_checks': True},
         'pilot_actual_model_requests': 4, 'pilot_model_proofs': 1,
         'pilot_reported_total_tokens': 37567, 'full_17_case_cohort_complete': False,
         'new_registered_certificates_by_promotion': 0, 'model_calls_by_promotion': 0,
         'gpu_trials_by_promotion': 0, 'original_paper_fully_reproduced': False}
write(OUT / 'progress.json', state)
write(OUT / 'update.json', {'sha': SOURCE, 'force': False})
state['remote_update'] = json.loads(call(['gh', 'api', '--method', 'PATCH',
    'repos/harsh-nod/lark/git/refs/heads/main', '--input', str(OUT / 'update.json')]))
require(state['remote_update']['object']['sha'] == SOURCE, 'Remote main update differs')
state['status'] = 'full-size-model-remote-main-fast-forwarded-local-pending'
write(OUT / 'progress.json', state)
state['local_merge'] = call(['git', 'merge', '--ff-only', SOURCE], MAIN)
subprocess.run(['git', 'update-ref', 'refs/remotes/origin/main', SOURCE, OLD],
               cwd=ROOT, check=True)
require(call(['git', 'rev-parse', 'HEAD'], MAIN) == SOURCE
        and not call(['git', 'status', '--porcelain'], MAIN), 'Local main differs')
state.update(status='full-size-model-source-ci-main-fast-forward-complete',
             helper_sha256=sha(Path(__file__)))
write(OUT / 'results.json', state)
print(json.dumps({'status': state['status'], 'main': SOURCE, 'source_ci_jobs': 18,
                  'full_cohort_complete': False}))
