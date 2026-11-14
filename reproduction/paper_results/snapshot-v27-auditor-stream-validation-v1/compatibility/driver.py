"""Replay immutable v25/v26 copies with new helpers outside Git; no experiment reruns."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT=Path('/tmp/lark-paper-v27-20261113')
OUT=Path('/tmp/lark-v27-auditor-buffer-compat-v1-20261114')
OUT.mkdir(exist_ok=False)
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
work=OUT/'isolated'
(work/'bin').mkdir(parents=True)
for name in ['replay_snapshot.py','snapshot_archives.py']:
    shutil.copyfile(ROOT/'reproduction/paper_results'/name,work/'bin'/name)
source=Path('/tmp/lark-reproduction-paper-source.tar')
assert hashlib.sha256(source.read_bytes()).hexdigest()=='095aae393369d4e8459e5c4c46af73b83ee9765ce786f4ebb870d2cd0cdf20d2'
shutil.copyfile(source,work/'paper-source.tar')
for version in ['20261113-v25','20261113-v26']:
    shutil.copytree(ROOT/'reproduction/paper_results/snapshots'/version,work/version,copy_function=os.link)
env=dict(os.environ,PATH='/nonexistent',PYTHONNOUSERSITE='1')
for name in ['PYTHONPATH','LEAN_PATH']:env.pop(name,None)

def check(version):
    command=[sys.executable,str(work/'bin/replay_snapshot.py'),'--snapshot',str(work/version),
             '--source-archive',str(work/'paper-source.tar')]
    began=time.monotonic()
    result=subprocess.run(command,cwd=work,env=env,text=True,capture_output=True,timeout=120)
    (OUT/(version+'.stdout')).write_text(result.stdout)
    (OUT/(version+'.stderr')).write_text(result.stderr)
    record={'version':version,'command':command,'exit_code':result.returncode,'seconds':time.monotonic()-began,
            'snapshot_manifest_sha256':hashlib.sha256((work/version/'manifest.json').read_bytes()).hexdigest()}
    (OUT/(version+'.json')).write_text(json.dumps(record,indent=2)+'\n')
    assert result.returncode==0 and 'frozen-snapshot-replayed' in result.stdout,result.stderr
    return record

with ThreadPoolExecutor(max_workers=2) as pool:
    records=list(pool.map(check,['20261113-v25','20261113-v26']))
record={'status':'both-immutable-v25-v26-full-replays-passed-outside-Git','checks':records,
        'per_replay_seconds':120,'max_independent_replayers':2,'PATH':'/nonexistent',
        'helper_sha256':{p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (work/'bin').glob('*.py')},
        'fresh_Lean_GPU_model_experiments':0,'original_paper_fully_reproduced':False}
(OUT/'results.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
