"""Capture the original successful full98 CI ledger job without rerunning it."""
from pathlib import Path
import hashlib
import json
import os
import re
import subprocess

OUT=Path('/tmp/lark-paper-v27-source-ci-ledger-passed-v10-20261114')
JOB,RUN=132423707907,43587053488
SOURCE='0911ad6ec09aea6bc9dd37ae4526165a531e62c1'
assert not OUT.exists();OUT.mkdir()
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
env=dict(os.environ,HTTPS_PROXY='socks5://127.0.0.1:19089')
for name,suffix in [('job.json',''),('logs.raw','/logs')]:
 r=subprocess.run(['gh','api',f'repos/harsh-nod/lark/actions/jobs/{JOB}'+suffix],env=env,capture_output=True,timeout=90)
 (OUT/name).write_bytes(r.stdout);(OUT/(name+'.stderr')).write_bytes(r.stderr)
 assert r.returncode==0,r.stderr
job=json.loads((OUT/'job.json').read_text());assert job['id']==JOB and job['run_id']==RUN and job['head_sha']==SOURCE
assert job['name']=='paper-ledger' and job['status']=='completed' and job['conclusion']=='success'
logs={};summaries=[]
for line in (OUT/'logs.raw').read_text().splitlines():
 i=line.find('{"control_log":')
 if i>=0:
  record=json.loads(line[i:]);name=record['control_log']
  assert re.fullmatch(r'[A-Za-z0-9_.-]+\.log',name) and name not in logs
  logs[name]=record['text'];p=OUT/'control-logs'/name;p.parent.mkdir(exist_ok=True);p.write_text(record['text'])
 i=line.find('{"status": "passed", "outside_checkout_without_git":')
 if i>=0:summaries.append(json.loads(line[i:]))
assert len(logs)==98 and len(summaries)==1
assert summaries[0]['positive_replays']==9 and summaries[0]['negative_controls']==89
raw=(OUT/'logs.raw').read_text()
diagnostics=[line for line in raw.splitlines() if any(marker in line for marker in ['Elapsed (wall clock)','User time (seconds)','System time (seconds)','Maximum resident set size','Exit status:'])]
result={'status':'exact-source-full98-ledger-CI-job-passed-within-existing300second-cap',
 'source_commit':SOURCE,'run_id':RUN,'job_id':JOB,'completed_control_logs':98,
 'positive_replays':9,'negative_controls':89,'summary':summaries[0],
 'per_replay_seconds':120,'aggregate_seconds':300,'max_independent_replayers':2,
 'job_steps':job['steps'],'resource_diagnostics':diagnostics,
 'whole_workflow_success_claim':False,'CI_reruns':0,'model_calls':0,'GPU_trials':0,
 'original_paper_fully_reproduced':False}
(OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
(OUT/'manifest.json').write_text(json.dumps({p.relative_to(OUT).as_posix():hashlib.sha256(p.read_bytes()).hexdigest()
 for p in sorted(OUT.rglob('*')) if p.is_file()},indent=2)+'\n')
print(json.dumps({k:result[k] for k in ['status','source_commit','job_id','completed_control_logs','resource_diagnostics']}),flush=True)
