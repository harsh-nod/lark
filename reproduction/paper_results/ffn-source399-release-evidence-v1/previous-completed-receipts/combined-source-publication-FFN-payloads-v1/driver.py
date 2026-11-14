"""Return terminal FFN publication metadata; retain all actual payloads on MI350."""
from pathlib import Path,PurePosixPath
import hashlib
import io
import json
import subprocess
import tarfile

OUT=Path('/tmp/lark-ffn-payload-publication-return-v1-20261114')
SOCKET='/tmp/lark-glm-cuda-cohort-publication-forward-20261113.sock'
REMOTE=r'''
from pathlib import Path
import hashlib,io,json,tarfile
base=Path('/tmp/lark-ffn-payload-publication-mi350-v1-20261114')
out=Path('/tmp/lark-ffn-payload-publication-capture-v1-20261114')
assert not out.exists() and not Path('/proc/1929757').exists()
result=json.loads((base/'results.json').read_text())
assert result['status']=='anonymous-exact-source-FFN-download-and-complete-payload-integrity-passed'
assert result['source_commit']=='3991812f0170ef73a174eff7be1dcaabb80d46fa'
assert result['downloaded_files']==34 and result['archives_checked']==15 and result['archive_members_checked']==4416
descriptor=json.loads((base/'descriptor.json').read_text())
def sha(p):
 d=hashlib.sha256()
 with p.open('rb')as f:
  while b:=f.read(1024*1024):d.update(b)
 return d.hexdigest()
for row in descriptor['files']:
 p=base/row['local'];assert not p.is_symlink()and p.is_file()
 assert p.stat().st_size==row['bytes']and sha(p)==row['sha256']
files={}
for p in sorted(base.rglob('*')):
 if not p.is_file():continue
 assert not p.is_symlink()
 n=p.relative_to(base).as_posix()
 if n.startswith('packet/')or n.endswith('.part'):continue
 files[n]=p
capture={'status':'terminal-publication-capture-only','original_result':result,
 'actual34_anonymous_downloaded_files_rehashed_on_capture':True,
 'actual_complete_downloaded_payloads_retained_on_MI350':descriptor['files'],
 'download_or_integrity_reruns':0,
 'captured_files':{n:{'bytes':p.stat().st_size,'sha256':sha(p)}for n,p in files.items()}}
out.mkdir();data=(json.dumps(capture,indent=2)+'\n').encode();archive=out/'receipt.tar.gz'
with tarfile.open(archive,'w:gz')as stream:
 for n,p in files.items():stream.add(p,arcname=n,recursive=False)
 info=tarfile.TarInfo('capture.json');info.size=len(data);stream.addfile(info,io.BytesIO(data))
r={'archive':str(archive),'bytes':archive.stat().st_size,'sha256':sha(archive),'capture_sha256':hashlib.sha256(data).hexdigest(),'files':len(files)+1}
(out/'transport.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r),flush=True)
'''

OUT.mkdir(exist_ok=False)
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
r=subprocess.run(['ssh','-S',SOCKET,'-o','BatchMode=yes','mi350','python3','-'],input=REMOTE,text=True,capture_output=True,timeout=180)
(OUT/'capture.stdout').write_text(r.stdout);(OUT/'capture.stderr').write_text(r.stderr);assert r.returncode==0,r.stderr
record=json.loads(r.stdout)
r=subprocess.run(['scp','-q','-o','ControlPath='+SOCKET,'-o','BatchMode=yes','mi350:'+record['archive'],str(OUT/'receipt.tar.gz')],capture_output=True,timeout=180)
(OUT/'download.stdout').write_bytes(r.stdout);(OUT/'download.stderr').write_bytes(r.stderr);assert r.returncode==0,r.stderr
raw=(OUT/'receipt.tar.gz').read_bytes();assert len(raw)==record['bytes']and hashlib.sha256(raw).hexdigest()==record['sha256']
with tarfile.open(fileobj=io.BytesIO(raw))as stream:
 members=stream.getmembers();assert len(members)==len({m.name for m in members})==record['files']
 assert all(m.isfile()and not PurePosixPath(m.name).is_absolute()and '..'not in PurePosixPath(m.name).parts for m in members)
 entries={m.name:stream.extractfile(m).read()for m in members}
capture=json.loads(entries['capture.json']);assert hashlib.sha256(entries['capture.json']).hexdigest()==record['capture_sha256']
assert set(entries)==set(capture['captured_files'])|{'capture.json'}
for n,b in capture['captured_files'].items():assert len(entries[n])==b['bytes']and hashlib.sha256(entries[n]).hexdigest()==b['sha256']
for n,data in entries.items():
 p=OUT/'verified'/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
(OUT/'results.json').write_text(json.dumps({'status':'FFN-publication-return-independently-byte-verified',**record,'downloaded_files':34,'archive_members_checked':4416,'no_reruns':True},indent=2)+'\n')
print((OUT/'results.json').read_text(),flush=True)
