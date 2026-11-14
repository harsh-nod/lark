"""Capture the original successful full FFN pipeline proof job, without reruns."""
from pathlib import Path
import hashlib
import json
import os
import subprocess

OUT = Path('/tmp/lark-ffn-pipeline-source-CI-job-pass-v2-20261114')
JOB, RUN = 132415417414, 43584309142
HEAD = '9245d455db3a70117a60df9873213a89d2a73f7c'
assert not OUT.exists()
OUT.mkdir()
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
env = dict(os.environ, HTTPS_PROXY='socks5://127.0.0.1:19089')
for filename, suffix in [('job.json', ''), ('logs.raw', '/logs')]:
    p = subprocess.run(['gh','api',f'repos/harsh-nod/lark/actions/jobs/{JOB}'+suffix],
                       env=env,capture_output=True,timeout=90)
    (OUT/filename).write_bytes(p.stdout)
    (OUT/(filename+'.stderr')).write_bytes(p.stderr)
    assert p.returncode==0,p.stderr
job=json.loads((OUT/'job.json').read_text())
assert job['run_id']==RUN and job['head_sha']==HEAD
assert job['name']=='ptx-matrix' and job['status']=='completed' and job['conclusion']=='success'
steps=[s for s in job['steps'] if s['name']=='Prove both FFN stages and the actual shared-intermediate pipeline']
assert len(steps)==1 and steps[0]['conclusion']=='success'
records=[]
for line in (OUT/'logs.raw').read_text().splitlines():
    start=line.find('{"status": "exact-full-size-FFN-two-launch-pipeline-passed"')
    if start>=0: records.append(json.loads(line[start:]))
assert len(records)==1
r=records[0]
assert len(r['module_checks'])==15 and all(c['exit_code']==0 and not c['timed_out'] for c in r['module_checks'])
assert len(r['axiom_audits'])==256
assert set(a for values in r['axiom_audits'].values() for a in values)<={'propext','Quot.sound','Classical.choice'}
assert r['limits']=={'maxRecDepth':10000,'maxHeartbeats':2000000,'per_Lean_process_seconds':180,'source_import_build_seconds':600}
assert r['original_stack_limits']==[8388608,-1] and r['all_own_modules_fresh'] is True
assert r['Lean_sha256']=='92c3d35b5bfaa5e0fea413a775d504cf46cd95e1345df61c2274f76779e7e023'
assert all(r[k]==1 for k in ['compiled_FFN_up_stage_correctness_proofs','compiled_FFN_down_stage_correctness_proofs','compiled_FFN_pipeline_correctness_proofs'])
assert all(r[k]==0 for k in ['new_registered_source_certificates','GPU_trials','model_calls'])
assert r['original_paper_fully_reproduced'] is False
(OUT/'pipeline-checker-result.json').write_text(json.dumps(r,indent=2)+'\n')
result={'status':'exact-source-complete-FFN-pipeline-CI-job-passed','source_commit':HEAD,
        'run_id':RUN,'job_id':JOB,'pipeline_step':steps[0],'checker_seconds':r['total_seconds'],
        'axiom_audits':256,'fresh_owned_libraries':14,'fresh_Main':1,
        'whole_workflow_success_claim':False,'CI_reruns':0,'model_calls':0,'GPU_trials':0,
        'new_registered_source_certificates':0,'original_paper_fully_reproduced':False}
(OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'manifest.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest()
    for p in sorted(OUT.iterdir()) if p.is_file()},indent=2)+'\n')
print(json.dumps(result),flush=True)
