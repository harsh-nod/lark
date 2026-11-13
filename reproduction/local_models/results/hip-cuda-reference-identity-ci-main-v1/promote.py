import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess
import sys
import tarfile

ROOT = Path('/tmp/lark-cuda-reference-identity-20261113')
MAIN = Path('/home/harsh/lark')
OLD = '8ae330eabe72a5384716f4c8fd63bb134c6a822b'
SOURCE = 'b9631e80c612da2cee82ac37be32b56e8174d16f'
TARGET = '5255bc1ed16c5b8ee6c419ad9700e53dba0e99b0'
OUT = Path('/tmp/lark-reference-identity-ci-main-v1-20261113')
BASE = ROOT / 'reproduction/local_models/results'
sys.path.insert(0, str(ROOT))
from reproduction.local_models import reference_identity as identity


def require(value, message):
    if not value:
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
    require(all(sha(root / p) == h for p, h in manifest.items()), 'Packet bytes differ: ' + name)
    return read(root / 'results.json')


parser = argparse.ArgumentParser()
parser.add_argument('--check-only', action='store_true')
args = parser.parse_args()
prior = packet('full-shape-deepseek-ci-main-v1')
ci = json.loads(call(['gh', 'run', 'view', '43373934797', '--repo', 'harsh-nod/lark',
                      '--json', 'status,conclusion,headSha,jobs,url']))
expected = {j['name'] for j in prior['source_ci']['jobs']} | {'reference-identity'}
require(ci['headSha'] == SOURCE and len(ci['jobs']) == len(expected) == 19
        and {j['name'] for j in ci['jobs']} == expected
        and ci['status'] == 'completed' and ci['conclusion'] == 'success'
        and all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in ci['jobs']),
        'All nineteen exact-source CI jobs must pass')
require(call(['git', 'rev-parse', 'HEAD']) == TARGET
        and not call(['git', 'status', '--porcelain']), 'Candidate checkout changed')
require(call(['git', 'rev-parse', 'HEAD'], MAIN) == OLD
        and not call(['git', 'status', '--porcelain'], MAIN), 'Main checkout changed')
require(call(['git', 'rev-parse', 'refs/remotes/origin/main']) == OLD, 'Tracking main changed')
for ancestor in (OLD, SOURCE):
    subprocess.run(['git', 'merge-base', '--is-ancestor', ancestor, TARGET], cwd=ROOT, check=True)
metadata = call(['git', 'diff', '--name-only', SOURCE, TARGET]).splitlines()
require(metadata and all(n == 'reproduction/local_models/README.md'
                        or n.startswith('reproduction/local_models/results/') for n in metadata),
        'Checked source/workflow/tests differ; post-source changes must be evidence/README only')
report = packet('hip-cuda-reference-identity-v1')
root = BASE / 'hip-cuda-reference-identity-v1'
binding = read(root / 'binding.json')
require(report['status'] == 'all-seventeen-hip-cuda-specifications-identical-and-control-refused'
        and report['specification_identity_theorems'] == len(report['cases']) == 17
        and report['axiom_audit_occurrences'] == 221
        and report['limits'] == {'maxRecDepth':10000,'maxHeartbeats':2000000,
                                 'lean_timeout_seconds':180}
        and all(report[k] == 0 for k in ('model_calls','gpu_trials','new_registered_certificates',
                                        'new_numerical_samples'))
        and report['original_paper_fully_reproduced'] is False,
        'Specification identity scope differs')
require(binding['driver_sha256'] == report['driver_sha256'] == sha(ROOT / 'reproduction/local_models/reference_identity.py')
        and binding['test_sha256'] == sha(ROOT / 'tests/test_reference_identity.py')
        and binding['cases'] == binding['identity_theorems'] == 17
        and binding['axiom_audits'] == 221 and binding['source_files'] == 213
        and binding['frozen_files'] == 270
        and binding['negative_semantic_counterexample_proved'] is False,
        'Driver/test/source binding differs')
with tarfile.open(root / 'identity.tar.gz', 'r:gz') as archive:
    members = archive.getmembers()
    require(len(members) == 270 and len({m.name for m in members}) == 270
            and all(m.isfile() and not PurePosixPath(m.name).is_absolute()
                    and '..' not in PurePosixPath(m.name).parts for m in members),
            'Identity archive inventory differs')
    data = {m.name:archive.extractfile(m).read() for m in members}
manifest = json.loads(data['manifest.json'])
require(set(data) == set(manifest) | {'manifest.json'}
        and all(hashlib.sha256(data[p]).hexdigest() == h for p, h in manifest.items()),
        'Identity archive member hashes differ')
require(json.loads(data['results.json']) == report, 'Archive and external reports differ')
source = json.loads(data['source-manifest.json'])
require(len(source) == 213 and {p[len('source/'):] for p in data if p.startswith('source/')} == set(source)
        and all(hashlib.sha256(data['source/'+p]).hexdigest() == h for p,h in source.items()),
        'Frozen source inventory differs')
hip = Path('/tmp/lark-full-shape-model-preflight-v2-20261112')
cuda = Path('/tmp/lark-full-shape-cuda-model-preflight-v1-20261113')
for row in report['cases']:
    name = row['hip_case']
    require(row['cuda_case'] == name and row['accepted'] is True
            and row['torch_reference_bytes_identical'] is True
            and row['lean_exit_code'] == 0, 'Recorded positive identity differs')
    main = data['cases/'+name+'/Main.lean'].decode()
    expected_main = identity.main_source((hip/'cases'/name/'sdk-block.lean.txt').read_text(),
                                        (cuda/'cases'/name/'sdk-block.lean.txt').read_text())
    require(main == expected_main and identity.log_audits(data['cases/'+name+'/lean.log'].decode()),
            'Positive identity Main or axiom audits differ: '+name)
control = report['wrong_operator_control']
require(control['accepted'] is False and control['lean_exit_code'] == 1
        and control['semantic_counterexample_proved'] is False
        and control['rejection_reason'] == identity.wrong_operator_refusal(
            data['wrong-operator-control/Main.lean'].decode(),
            data['wrong-operator-control/lean.log'].decode()) == 'fixed-recursion-limit',
        'Recorded wrong-operator resource refusal differs')
publication = packet('hip-cuda-reference-identity-publication-v1')
require(publication['source_commit'] == SOURCE and len(publication['downloaded_files']) == 4
        and publication['total_downloaded_bytes'] == 249551
        and publication['tls_verification'] is True and publication['authorization_header'] is False
        and publication['all_downloads_match_committed_bytes'] is True
        and all(x['curl_ssl_verify_result'] == 0 and x['tls_verification'] is True
                and x['authorization_header'] is False and sha(ROOT / x['path']) == x['sha256']
                for x in publication['downloaded_files'])
        and publication['original_paper_fully_reproduced'] is False,
        'Anonymous reference identity publication differs')
require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/main']))['object']['sha'] == OLD,
        'Remote main changed')
require(json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/commits/'+TARGET]))['sha'] == TARGET,
        'Candidate is not published')
if args.check_only:
    print(json.dumps({'status':'reference-identity-main-gate-preflight-checked',
                      'source_ci_jobs':19,'identity_theorems':17,'axiom_audits':221,
                      'archive_files':270,'anonymous_files':4}))
    raise SystemExit(0)
OUT.mkdir(exist_ok=False)
state = {'schema':1,'status':'reference-identity-main-gates-passed-update-pending',
         'checked_at_utc':datetime.now(timezone.utc).isoformat(), 'source_checkpoint':SOURCE,
         'old_main':OLD,'promoted_commit':TARGET,'source_ci':ci,'post_source_metadata_paths':metadata,
         'checks':{'all19_source_jobs_success':True,'checked_implementation_workflow_tests_unchanged':True,
                   'all17_identity_mains_and221_axiom_audits_bound':True,'all270_archive_files_bound':True,
                   'wrong_operator_refusal_is_resource_bound_not_semantic_inequality':True,
                   'anonymous4_file249551_bytes_TLS':True,'clean_main_and_candidate':True,
                   'ancestry_verified':True},
         'model_calls_by_promotion':0,'gpu_trials_by_promotion':0,
         'new_registered_certificates_by_promotion':0,'original_paper_fully_reproduced':False}
write(OUT/'progress.json',state)
write(OUT/'update.json',{'sha':TARGET,'force':False})
state['remote_update'] = json.loads(call(['gh','api','--method','PATCH',
    'repos/harsh-nod/lark/git/refs/heads/main','--input',str(OUT/'update.json')]))
require(state['remote_update']['object']['sha'] == TARGET, 'Remote main update differs')
state['status'] = 'reference-identity-remote-main-fast-forwarded-local-pending'
write(OUT/'progress.json',state)
state['local_merge'] = call(['git','merge','--ff-only',TARGET],MAIN)
subprocess.run(['git','update-ref','refs/remotes/origin/main',TARGET,OLD],cwd=ROOT,check=True)
require(call(['git','rev-parse','HEAD'],MAIN) == TARGET
        and not call(['git','status','--porcelain'],MAIN),'Local main differs')
state.update(status='reference-identity-source-ci-main-fast-forward-complete',
             helper_sha256=sha(Path(__file__)))
write(OUT/'results.json',state)
print(json.dumps({'status':state['status'],'main':TARGET,'identities':17,'source_ci_jobs':19}))
