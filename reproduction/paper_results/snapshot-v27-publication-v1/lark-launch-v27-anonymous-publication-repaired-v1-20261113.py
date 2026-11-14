"""Repair the local bootstrap serialization; launch only if no remote attempt exists."""
import hashlib,json,re
from pathlib import Path
import subprocess

OUT=Path('/tmp/lark-v27-publication-launch-repaired-v1-20261113')
OUT.mkdir(exist_ok=False)
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
driver=Path('/tmp/lark-run-v27-anonymous-publication-v1-20261113.py').read_bytes()
descriptor=Path('/tmp/lark-v27-publication-inputs-v1-20261113/descriptor.json').read_bytes()
compile(driver,'authored-publication-driver','exec')
assert json.loads(descriptor)['source_commit']=='8eae2cd8bf4230f2f71d7257b37e36588599397e'
template=r'''
import hashlib,json,subprocess
from pathlib import Path
base=Path('/tmp/lark-paper-v27-publication-observer-v1-20261113')
view=Path('/tmp/lark-paper-v27-publication-git-view-v1-20261113')
public=Path('/tmp/lark-paper-v27-publication-mi350-v1-20261113')
assert not base.exists() and not view.exists() and not public.exists(),'Inspect original job; never restart due observation expiry'
driver=__LARK_DRIVER_BYTES__
descriptor=__LARK_DESCRIPTOR_BYTES__
base.mkdir()
(base/'driver.py').write_bytes(driver)
(base/'descriptor.json').write_bytes(descriptor)
with (base/'stdout.log').open('xb') as stdout,(base/'stderr.log').open('xb') as stderr:
 child=subprocess.Popen(['python3',str(base/'driver.py')],cwd=base,stdin=subprocess.DEVNULL,stdout=stdout,stderr=stderr,start_new_session=True)
value={'pid':child.pid,'observer':str(base),'Git_view':str(view),'public_output':str(public),
 'source_commit':'8eae2cd8bf4230f2f71d7257b37e36588599397e',
 'driver_sha256':hashlib.sha256(driver).hexdigest(),'descriptor_sha256':hashlib.sha256(descriptor).hexdigest()}
(base/'launch.json').write_text(json.dumps(value,indent=2)+'\n')
print(json.dumps(value),flush=True)
'''
values={'DRIVER':driver,'DESCRIPTOR':descriptor}
code=re.sub(r'__LARK_(DRIVER|DESCRIPTOR)_BYTES__',lambda match:repr(values[match[1]]),template)
compile(code,'publication-bootstrap','exec')
(OUT/'remote-launch.py').write_text(code)
r=subprocess.run(['ssh','-S','/tmp/lark-glm-cuda-cohort-publication-forward-20261113.sock','-o','BatchMode=yes','-o','ConnectTimeout=15','mi350','python3','-'],input=code,text=True,capture_output=True,timeout=45)
(OUT/'stdout.log').write_text(r.stdout);(OUT/'stderr.log').write_text(r.stderr)
assert r.returncode==0,r.stderr
(OUT/'results.json').write_text(json.dumps(json.loads(r.stdout),indent=2)+'\n')
(OUT/'manifest.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.iterdir()) if p.is_file()},indent=2)+'\n')
print(r.stdout,end='')
