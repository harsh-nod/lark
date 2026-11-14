"""Publish one concrete v27 source branch non-force; observe this exact push."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import subprocess
import time

ROOT=Path('/tmp/lark-paper-v27-20261113')
OUT=Path('/tmp/lark-paper-v27-source-push-v1-20261113')
SOURCE='87845d0bbeb8e6876a6536fad827e1c0a1b86680'
OUT.mkdir(exist_ok=False)
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()==SOURCE
assert not subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True).strip()
command=['git','-c','http.proxy=socks5h://127.0.0.1:19089','-c','http.postBuffer=536870912',
         '-c','http.version=HTTP/1.1','push','--porcelain','origin',SOURCE+':refs/heads/reproduction/paper-v27']
started=time.monotonic()
record={'status':'running','source_commit':SOURCE,'command':command,'force':False,
        'at_utc':datetime.now(timezone.utc).isoformat(),'main_changed':False,'CI_reruns':0}
with (OUT/'stdout.log').open('w') as stdout,(OUT/'stderr.log').open('w') as stderr:
    child=subprocess.Popen(command,cwd=ROOT,stdout=stdout,stderr=stderr)
    record['pid']=child.pid
    (OUT/'progress.json').write_text(json.dumps(record,indent=2)+'\n')
    code=child.wait()
record.update(status='push-completed' if code==0 else 'push-failed-inspect-remote-before-any-retry',
              exit_code=code,seconds=time.monotonic()-started,at_utc=datetime.now(timezone.utc).isoformat())
(OUT/'results.json').write_text(json.dumps(record,indent=2)+'\n')
(OUT/'progress.json').write_text(json.dumps(record,indent=2)+'\n')
(OUT/'manifest.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.iterdir()) if p.is_file()},indent=2)+'\n')
print(json.dumps(record),flush=True)
raise SystemExit(code)
