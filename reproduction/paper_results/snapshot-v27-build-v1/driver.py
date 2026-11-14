from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import time

ROOT=Path('/tmp/lark-paper-v27-20261113')
OUT=Path('/tmp/lark-build-paper-v27-v1-20261113')
OUT.mkdir(exist_ok=False)
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
assert commit.startswith('3d90539')
command=[sys.executable,'reproduction/paper_results/prepare_ptx_rotary_snapshot.py',
         '--evidence-commit',commit,'--source-archive','/tmp/lark-reproduction-paper-source.tar',
         '--snapshot','reproduction/paper_results/snapshots/20261113-v27']
started=time.monotonic()
record={'status':'running','source_commit':commit,'command':command,'started_at_utc':datetime.now(timezone.utc).isoformat(),'model_calls':0,'GPU_trials':0,'Lean_checks':0,'original_paper_fully_reproduced':False}
(OUT/'progress.json').write_text(json.dumps(record,indent=2)+'\n')
with (OUT/'stdout.log').open('w') as stdout,(OUT/'stderr.log').open('w') as stderr:
    child=subprocess.Popen(command,cwd=ROOT,stdout=stdout,stderr=stderr)
    record['child_pid']=child.pid
    (OUT/'progress.json').write_text(json.dumps(record,indent=2)+'\n')
    code=child.wait()
record.update(status='passed' if code==0 else 'failed',exit_code=code,seconds=time.monotonic()-started,finished_at_utc=datetime.now(timezone.utc).isoformat())
(OUT/'results.json').write_text(json.dumps(record,indent=2)+'\n')
(OUT/'progress.json').write_text(json.dumps(record,indent=2)+'\n')
(OUT/'manifest.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.iterdir()) if p.is_file()},indent=2)+'\n')
print(json.dumps(record),flush=True)
raise SystemExit(code)
