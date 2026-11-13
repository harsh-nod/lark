import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import tarfile

ROOT = Path('/tmp/lark-full-shape-deepseek-results-20261113')
MAIN = Path('/home/harsh/lark')
OLD = 'cd3185a32bc1611cb75229d90a955fe0c49a5c34'
SOURCE = '1b22551bc295431707dc81288a57ac9a2e6f9475'
TARGET = '8ae330eabe72a5384716f4c8fd63bb134c6a822b'
OUT = Path('/tmp/lark-deepseek-full-cohort-ci-main-v1-20261113')
BASE = ROOT / 'reproduction/local_models/results'

def require(value, message):
    if not value:
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
    root = BASE / name
    manifest = read(root / 'manifest.json')
    require({str(p.relative_to(root)) for p in root.rglob('*') if p.is_file()}
            == set(manifest) | {'manifest.json'}, 'Packet inventory differs: ' + name)
    require(all(sha(root / n) == h for n, h in manifest.items()), 'Packet bytes differ: ' + name)
    return read(root / 'results.json')

parser = argparse.ArgumentParser()
parser.add_argument('--check-only', action='store_true')
args = parser.parse_args()
prior = packet('full-shape-cuda-ci-main-v1')
ci = json.loads(call(['gh', 'run', 'view', '43366990885', '--repo', 'harsh-nod/lark',
                      '--json', 'status,conclusion,headSha,jobs,url']))
expected = {j['name'] for j in prior['source_ci']['jobs']}
require(ci['headSha'] == SOURCE and len(ci['jobs']) == len(expected) == 18
        and {j['name'] for j in ci['jobs']} == expected
        and ci['status'] == 'completed' and ci['conclusion'] == 'success'
        and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in ci['jobs']),
        'All eighteen exact-source CI jobs must pass')
require(call(['git', 'rev-parse', 'HEAD']) == TARGET
        and not call(['git', 'status', '--porcelain']), 'Candidate checkout changed')
require(call(['git', 'rev-parse', 'HEAD'], MAIN) == OLD
        and not call(['git', 'status', '--porcelain'], MAIN), 'Main checkout changed')
require(call(['git', 'rev-parse', 'refs/remotes/origin/main']) == OLD, 'Tracking main changed')
for ancestor in (OLD, SOURCE):
    subprocess.run(['git', 'merge-base', '--is-ancestor', ancestor, TARGET], cwd=ROOT, check=True)
changed = call(['git', 'diff', '--name-only', OLD, TARGET]).splitlines()
prefixes = tuple('reproduction/local_models/results/' + name + '/' for name in (
    'full-shape-cohort-deepseek-v1', 'full-shape-cohort-deepseek-publication-v1',
    'full-shape-cuda-ci-main-v1'))
require(changed and all(n == 'reproduction/local_models/README.md' or n.startswith(prefixes)
                        for n in changed), 'Candidate is not cohort evidence, receipts and README')
require(not call(['git', 'diff', '--name-only', OLD, TARGET, '--', 'lark_kernels', 'lean',
                  'lean-real', 'tests', '.github', 'pyproject.toml',
                  'reproduction/local_models/full_shape.py',
                  'reproduction/local_models/full_shape_run.py',
                  'reproduction/local_models/audit_full_shape.py']), 'Checked source changed')
report = packet('full-shape-cohort-deepseek-v1')
root = BASE / 'full-shape-cohort-deepseek-v1'
counts = report['counts']
require(report['complete_17_case_cohort'] is True and report['test_stub'] is False
        and counts == {'cases':17,'verified_within_budget':16,'budget_exhausted':1,
          'first_response_verified':0,'first_actual_lean_check_verified':14,
          'actual_lean_checks':21,'model_requests':175,'response_files':175,
          'raw_files':1426,'audit_files':459,'additional_fresh_kernel_checks':32}
        and report['reported_usage'] == {'prompt_tokens':3361778,'completion_tokens':482540,
                                        'total_tokens':3844318}
        and report['usage_incomplete'] is False and report['external_api_spend_usd'] == 0
        and report['new_registered_source_certificates'] == report['gpu_trials'] == 0,
        'Complete model cohort scope differs')
raw = read(root / 'raw-results.json')
audit = read(root / 'audit-results.json')
require(raw['status'] == 'finished' and raw['complete_17_case_cohort'] is True
        and len(raw['cases']) == 17 and raw['verified_model_proofs'] == 16
        and audit['complete_17_case_cohort'] is True
        and audit['freshly_verified_model_proofs'] == 16
        and len(audit['bound_model_requests']) == 175
        and len(audit['fresh_accepted_proof_kernel_checks']) == 32
        and audit['model_calls_by_audit'] == 0, 'Recorded/fresh replay counts differ')
for archive_name, manifest_name in (('cohort.tar.gz', 'cohort-files.json'),
                                    ('audit.tar.gz', 'audit-files.json')):
    manifest = read(root / manifest_name)
    with tarfile.open(root / archive_name, 'r:gz') as archive:
        members = archive.getmembers()
        require(len(members) == len(manifest) and {m.name for m in members} == set(manifest)
                and all(m.isfile() for m in members), 'Archive member inventory differs')
        for member in members:
            require(hashlib.sha256(archive.extractfile(member).read()).hexdigest()
                    == manifest[member.name], 'Archive file differs: ' + member.name)
stop = read(root / 'lifecycle/stop.json')
require(stop['container_id'] == 'a8c5b078b9fc7ea4c74685cbf6cef3f8eb99150ba3fcfd205a252896be3b81b3'
        and stop['running'] is False and stop['container_exit_code'] == 0
        and stop['other_containers_stopped'] == 0, 'Owned service lifecycle differs')
publication = packet('full-shape-cohort-deepseek-publication-v1')
require(publication['source_commit'] == '375941b4a71e08bc560be05741e2c87d0d10b261'
        and len(publication['downloaded_files']) == 14
        and publication['total_downloaded_bytes'] == 7704181
        and publication['tls_verification'] is True and publication['authorization_header'] is False
        and publication['all_downloads_match_committed_bytes'] is True
        and all(x['curl_ssl_verify_result'] == 0 and x['tls_verification'] is True
                and x['authorization_header'] is False and sha(ROOT / x['path']) == x['sha256']
                for x in publication['downloaded_files']), 'Anonymous publication differs')
require(all(r['original_paper_fully_reproduced'] is False for r in (report, raw, audit, publication)),
        'Unsupported original-paper completion claim')
require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha']
        == OLD, 'Remote main changed')
require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/commits/' + TARGET]))['sha']
        == TARGET, 'Candidate is not published')
if args.check_only:
    print(json.dumps({'status':'deepseek-full-cohort-main-gate-preflight-checked',
                      'source_ci_jobs':18,'requests':175,'verified':16,'fresh_kernel_checks':32}))
    raise SystemExit(0)
OUT.mkdir(exist_ok=False)
state = {'schema':1,'status':'deepseek-cohort-main-gates-passed-update-pending',
         'checked_at_utc':datetime.now(timezone.utc).isoformat(), 'source_checkpoint':SOURCE,
         'old_main':OLD,'promoted_commit':TARGET,'source_ci':ci,'metadata_paths':changed,
         'checks':{'all18_source_jobs_success':True,'checked_implementation_unchanged':True,
                   'all175_protocol_requests_and_two_fresh_checks_per_success':True,
                   'complete_archive_file_hashes':True,'anonymous14_file7704181_bytes_TLS':True,
                   'clean_main_and_candidate':True,'ancestry_verified':True},
         'model_calls_by_promotion':0,'gpu_trials_by_promotion':0,
         'new_registered_certificates_by_promotion':0,'original_paper_fully_reproduced':False}
write(OUT / 'progress.json', state)
write(OUT / 'update.json', {'sha':TARGET,'force':False})
state['remote_update'] = json.loads(call(['gh','api','--method','PATCH',
    'repos/harsh-nod/lark/git/refs/heads/main','--input',str(OUT/'update.json')]))
require(state['remote_update']['object']['sha'] == TARGET, 'Remote main update differs')
state['status'] = 'deepseek-cohort-remote-main-fast-forwarded-local-pending'
write(OUT / 'progress.json', state)
state['local_merge'] = call(['git','merge','--ff-only',TARGET], MAIN)
subprocess.run(['git','update-ref','refs/remotes/origin/main',TARGET,OLD],cwd=ROOT,check=True)
require(call(['git','rev-parse','HEAD'],MAIN) == TARGET and
        not call(['git','status','--porcelain'],MAIN), 'Local main differs')
state.update(status='deepseek-full-cohort-source-ci-main-fast-forward-complete',
             helper_sha256=sha(Path(__file__)))
write(OUT / 'results.json',state)
print(json.dumps({'status':state['status'],'main':TARGET,'verified':16,'requests':175}))
