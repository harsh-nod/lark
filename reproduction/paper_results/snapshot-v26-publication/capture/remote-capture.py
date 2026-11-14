
from datetime import datetime,timezone
import hashlib,io,json,tarfile
from pathlib import Path
out=Path('/tmp/lark-paper-v26-publication-capture-v2-20261113')
public=Path('/tmp/lark-paper-v26-publication-mi350-v2-20261113')
observer=Path('/tmp/lark-paper-v26-publication-mi350-observer-v2-20261113')
view=Path('/tmp/lark-paper-v26-publication-git-view-v2-20261113')
source='ce5611655946a0a8cca76f97beb8f85bf8f4fc2b'
result=json.loads((observer/'observer/results.json').read_text())
assert result['status']=='anonymous17-file-source-exact-v26-download-and-all89-controls-passed'
assert result['source_commit']==source and result['exit_code']==0 and not result['timed_out']
report=json.loads((public/'results.json').read_text())
assert report['source_commit']==source and len(report['downloaded_files'])==17
assert report['total_downloaded_bytes']==238899106
assert report['positive_replays']==8 and report['negative_controls']==81
assert len(list((public/'validation').glob('*.log')))==89
assert report['validation']==json.loads((public/'validation/results.json').read_text())
assert not out.exists(),'Inspect already captured evidence; never repeat capture blindly'
files={}
for label,folder in [('public',public),('public/validation',public/'validation'),
 ('launch',observer),('observer',observer/'observer'),('git-view',view)]:
 for p in sorted(folder.iterdir()):
  assert not p.is_symlink()
  if p.is_file():
   assert p.stat().st_size<1000000,(label,p)
   name=label+'/'+p.name
   assert name not in files
   files[name]=p
for folder in [public,public/'validation',observer/'observer']:
 actual={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in folder.iterdir() if p.is_file() and p.name!='manifest.json'}
 assert actual==json.loads((folder/'manifest.json').read_text()),str(folder)
records=[{'path':name,'remote_path':str(p),'bytes':p.stat().st_size,
 'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for name,p in sorted(files.items())]
inventory={'schema':1,'at_utc':datetime.now(timezone.utc).isoformat(),'source_commit':source,
 'status':'terminal-evidence-capture-only','public_result':result,'files':records,
 'downloaded_payloads_remain_on_host':True,'new_model_GPU_Lean_or_replay_calls':0}
data=(json.dumps(inventory,indent=2)+'\n').encode()
out.mkdir()
(out/'capture.json').write_bytes(data)
tar=out/'receipt.tar'
with tarfile.open(tar,'w') as archive:
 for name,p in sorted(files.items()):
  archive.add(p,arcname=name,recursive=False)
 info=tarfile.TarInfo('capture.json');info.size=len(data);info.mtime=0
 archive.addfile(info,io.BytesIO(data))
receipt={'source_commit':source,'tar':str(tar),'bytes':tar.stat().st_size,
 'sha256':hashlib.sha256(tar.read_bytes()).hexdigest(),'files':len(files),
 'capture_sha256':hashlib.sha256(data).hexdigest()}
(out/'transport.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt),flush=True)
