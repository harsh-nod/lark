"""Capture the terminal failed v27 suite, retaining every remote input/workspace."""
import hashlib
import io
import json
from pathlib import Path,PurePosixPath
import shlex
import subprocess
import tarfile

OUT=Path('/tmp/lark-paper-v27-mi350-success-return-v3-20261113')
SOCKET='/tmp/lark-glm-cuda-cohort-publication-forward-20261113.sock'
SSH=['ssh','-S',SOCKET,'-o','BatchMode=yes','-o','ConnectTimeout=15','mi350']
REMOTE_CODE=r'''
import hashlib,io,json,tarfile
from pathlib import Path
root=Path('/tmp/lark-paper-v27-controls-mi350-v3-20261113')
out=Path('/tmp/lark-paper-v27-mi350-success-capture-v3-20261113')
assert not out.exists()
result=json.loads((root/'observer/results.json').read_text())
assert result['timed_out'] is False and result['completed_logs']==98 and result['status']=='complete-control-suite-passed'
assert not (Path('/proc')/'1018992').exists() and not (Path('/proc')/'1019000').exists()
def sha(path):
 d=hashlib.sha256()
 with path.open('rb') as source:
  while data:=source.read(1024*1024):d.update(data)
 return d.hexdigest()
files={}
for p in sorted(root.rglob('*')):
 if not p.is_file():continue
 n=p.relative_to(root).as_posix()
 if n.startswith('temporary/') or n.startswith('source/reproduction/paper_results/snapshots/') or n=='paper-source.tar':continue
 assert not p.is_symlink()
 files[n]=p
workspace={p.relative_to(root).as_posix():{'bytes':p.stat().st_size,'sha256':sha(p)}
 for p in sorted((root/'temporary').rglob('*')) if p.is_file()}
logs={p.name:{'bytes':p.stat().st_size,'sha256':sha(p),'mtime_ns':p.stat().st_mtime_ns}
 for p in sorted((root/'validation').glob('*.log'))}
capture={'schema':1,'status':'terminal-complete-suite-capture-only','original_result':result,
 'source_snapshot_and_original_transport_archive_retained_on_MI350':True,
 'interrupted_workspace_files':workspace,'interrupted_workspace_files_deleted':0,
 'all98_completed_logs':logs,'experiment_or_control_reruns':0,
 'captured_files':{n:{'bytes':p.stat().st_size,'sha256':sha(p)} for n,p in files.items()}}
out.mkdir()
data=(json.dumps(capture,indent=2)+'\n').encode()
(out/'capture.json').write_bytes(data)
archive=out/'receipt.tar.gz'
with tarfile.open(archive,'w:gz') as stream:
 for n,p in sorted(files.items()):stream.add(p,arcname=n,recursive=False)
 info=tarfile.TarInfo('capture.json');info.size=len(data)
 stream.addfile(info,io.BytesIO(data))
record={'archive':str(archive),'bytes':archive.stat().st_size,'sha256':sha(archive),
 'capture_sha256':hashlib.sha256(data).hexdigest(),'files':len(files)+1,
 'workspace_files_retained':len(workspace),'completed_logs':len(logs)}
(out/'transport.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
'''


def sha(path):
 return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
 OUT.mkdir(exist_ok=False)
 (OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
 result=subprocess.run(SSH+['python3','-'],input=REMOTE_CODE,text=True,capture_output=True,timeout=180)
 (OUT/'capture.stdout').write_text(result.stdout);(OUT/'capture.stderr').write_text(result.stderr)
 assert result.returncode==0,result.stderr
 record=json.loads(result.stdout)
 (OUT/'transport.json').write_text(json.dumps(record,indent=2)+'\n')
 result=subprocess.run(['scp','-q','-o','ControlPath='+SOCKET,'-o','BatchMode=yes','mi350:'+record['archive'],str(OUT/'receipt.tar.gz')],capture_output=True,text=True,timeout=180)
 (OUT/'download.stdout').write_text(result.stdout);(OUT/'download.stderr').write_text(result.stderr)
 assert result.returncode==0,result.stderr
 assert (OUT/'receipt.tar.gz').stat().st_size==record['bytes'] and sha(OUT/'receipt.tar.gz')==record['sha256']
 with tarfile.open(OUT/'receipt.tar.gz') as archive:
  members=archive.getmembers()
  assert len(members)==len({m.name for m in members})==record['files']
  assert all(m.isfile() and not PurePosixPath(m.name).is_absolute() and '..' not in PurePosixPath(m.name).parts for m in members)
  entries={m.name:archive.extractfile(m).read() for m in members}
 assert hashlib.sha256(entries['capture.json']).hexdigest()==record['capture_sha256']
 capture=json.loads(entries['capture.json'])
 assert set(entries)==set(capture['captured_files'])|{'capture.json'}
 assert all(len(entries[n])==r['bytes'] and hashlib.sha256(entries[n]).hexdigest()==r['sha256'] for n,r in capture['captured_files'].items())
 target=OUT/'verified'
 target.mkdir()
 for n,data in entries.items():
  p=target/n;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(data)
 print(json.dumps(record),flush=True)


if __name__=='__main__':main()
