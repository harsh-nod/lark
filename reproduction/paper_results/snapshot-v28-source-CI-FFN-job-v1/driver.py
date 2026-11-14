"""Capture the successful original FFN certificate job and its actual limits."""
from pathlib import Path
import hashlib
import json
import os
import subprocess

OUT = Path('/tmp/lark-paper-v28-FFN-source-CI-job-v1-20261114')
JOB, RUN = 132463737373, 43600411242
HEAD = '24288a0460f811f3e0ca5e8b28b64a3a4489503c'
assert not OUT.exists()
OUT.mkdir()
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
env = dict(os.environ, HTTPS_PROXY='socks5://127.0.0.1:19089')
for name, suffix in [('job.json',''),('logs.raw','/logs')]:
    r = subprocess.run(['gh','api',f'repos/harsh-nod/lark/actions/jobs/{JOB}'+suffix],
                       env=env,capture_output=True,timeout=90)
    (OUT/name).write_bytes(r.stdout)
    (OUT/(name+'.stderr')).write_bytes(r.stderr)
    assert r.returncode == 0, r.stderr
job = json.loads((OUT/'job.json').read_text())
assert job['run_id']==RUN and job['head_sha']==HEAD and job['id']==JOB
assert job['status']=='completed' and job['conclusion']=='success' and job['name']=='ptx-matrix'
required = {
    'Export the source-bound full FFN pipeline certificate',
    'Rebuild the FFN certificate and refuse four direct Lean dependency changes',
    'Refuse 31 coherently rehashed FFN recordings before fresh Lean work',
    'Retain FFN certificate and control reports and Lean logs',
    'Verify every member of the complete retained FFN certificate payloads',
}
steps=[s for s in job['steps'] if s['name'] in required]
assert len(steps)==5 and all(s['status']=='completed' and s['conclusion']=='success' for s in steps)
evidence={}
for line in (OUT/'logs.raw').read_text().splitlines():
    start=line.find('{"FFN_evidence":')
    if start>=0:
        data=json.loads(line[start:]);n=data['FFN_evidence']
        assert n not in evidence
        evidence[n]=data['text']
        path=OUT/'dumped-evidence'/n
        path.parent.mkdir(parents=True,exist_ok=True)
        path.write_text(data['text'])
positive=[]
for n in ['lark-ptx-ffn-ci-export/results.json','lark-ptx-ffn-ci-source-controls/positive-source-only-replay/results.json']:
    p=json.loads(evidence[n]);positive.append(p)
    assert p['status']=='verified-source-bound-full-PTX-FFN-pipeline' and p['source_bound_proof_accepted'] is True
    assert p['original_stack_limits']==[8388608,-1]
    assert p['owned_Lean_modules_freshly_compiled']==14 and p['old_owned_olean_cache_used'] is False
    assert len(p['module_checks'])==14 and all(c['exit_code']==0 and c['timed_out'] is False for c in p['module_checks'])
    assert p['main_check']['exit_code']==0 and p['main_check']['timed_out'] is False
    assert len(p['library_axiom_audits'])+len(p['axiom_audits'])==256
    assert set(a for values in [*p['library_axiom_audits'].values(),*p['axiom_audits'].values()] for a in values)<={'propext','Quot.sound','Classical.choice'}
    assert p['limits']=={'maxRecDepth':10000,'maxHeartbeats':2000000,'per_Lean_process_seconds':180,'source_import_build_seconds':600}
    assert p['lean_binary_sha256']=='92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023'
    assert p['model_calls']==p['gpu_trials']==p['new_registered_source_certificates']==0
    assert p['original_paper_fully_reproduced'] is False
direct=json.loads(evidence['lark-ptx-ffn-ci-source-controls/results.json'])
assert direct['direct_Lean_negative_controls']==4 and direct['timeouts']==direct['resource_limit_failures']==0
assert all(r['expected_rejection_verified'] is True for r in direct['negative_controls'])
forged=json.loads(evidence['lark-ptx-ffn-ci-recording-controls/results.json'])
assert forged['negative_controls']==31 and forged['fresh_Lean_checks']==0
assert all(r['status']=='rejected-before-fresh-Lean-work' and r['output_created'] is False for r in forged['checks'])
integrity=[]
for line in (OUT/'logs.raw').read_text().splitlines():
    start=line.find('{"status": "complete-FFN-publication-payload-integrity-passed"')
    if start>=0:integrity.append(json.loads(line[start:]))
assert len(integrity)==1 and integrity[0]['archive_members_checked']==4416 and integrity[0]['uncompressed_member_bytes_checked']==940266976
result={'status':'integrated-source-FFN-certificate-all35controls-and4416payload-members-passed-at8MiB',
        'source_commit':HEAD,'run_id':RUN,'job_id':JOB,'required_steps':steps,
        'certificate_positive_source_builds':2,'certificate_stack_limits':[8388608,-1],
        'certificate_build_seconds':[p['total_seconds'] for p in positive],
        'axiom_audits_per_build':256,'fresh_owned_libraries_per_build':14,
        'direct_Lean_negative_controls':4,'rehashed_recording_negative_controls':31,
        'payload_integrity':integrity[0], 'dumped_evidence_files':len(evidence),'whole_workflow_success_claim':False,
        'CI_reruns':0,'model_calls':0,'GPU_trials':0,'new_registered_source_certificates':0,
        'original_paper_fully_reproduced':False}
(OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'manifest.json').write_text(json.dumps({p.relative_to(OUT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
    for p in sorted(OUT.rglob('*')) if p.is_file()},indent=2)+'\n')
print(json.dumps(result),flush=True)
