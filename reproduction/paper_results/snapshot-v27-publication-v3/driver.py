"""Capture a terminal publication; never rerun downloads or controls."""
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import subprocess
import tarfile

OUT = Path('/tmp/lark-v27-anonymous-publication-return-v3-20261114')
SOCKET = '/tmp/lark-glm-cuda-cohort-publication-forward-20261113.sock'
REMOTE = r'''
import hashlib,io,json,tarfile
from pathlib import Path
base=Path('/tmp/lark-paper-v27-publication-observer-v3-20261114')
public=Path('/tmp/lark-paper-v27-publication-mi350-v3-20261114')
out=Path('/tmp/lark-v27-publication-capture-v3-20261114')
assert not out.exists()
assert not Path('/proc/1265782').exists() and not Path('/proc/1265873').exists()
result=json.loads((base/'results.json').read_text())
assert result['status']=='anonymous20-file-source-exact-v27-download-and-all98-controls-passed'
descriptor=json.loads((base/'descriptor.json').read_text())
report=json.loads((public/'results.json').read_text())
controls=json.loads((public/'validation/results.json').read_text())
assert controls['checks']==descriptor['expected_98_check_records']
assert len(list((public/'validation').glob('*.log')))==98
def sha(p):
 d=hashlib.sha256()
 with p.open('rb') as f:
  while b:=f.read(1024*1024):d.update(b)
 return d.hexdigest()
downloaded={row['path']:row for row in report['downloaded_files']}
assert len(downloaded)==20
for name,row in downloaded.items():
 p=public/'download'/name
 assert p.is_file() and not p.is_symlink()
 assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256']
files={}
for label,root in [('observer',base),('public',public)]:
 for p in sorted(root.rglob('*')):
  if not p.is_file():continue
  name=p.relative_to(root).as_posix()
  if label=='public' and name.startswith('download/'):continue
  assert not p.is_symlink()
  files[label+'/'+name]=p
capture={'schema':1,'status':'terminal-success-publication-capture-only',
 'source_commit':result['source_commit'],'original_result':result,
 'all20_downloaded_files_rehashed_on_capture':True,
 'all20_complete_downloaded_files_retained_on_MI350':downloaded,
 'complete_public_inputs_already_committed_at_source':True,
 'all98_control_logs_returned':True,
 'expected_Git_objects_seeded_from_verified_MI350_inputs':True,
 'expected_Git_object_seed_did_not_replace_actual_anonymous_URL_downloads':True,
 'publication_or_control_reruns':0,
 'captured_files':{n:{'bytes':p.stat().st_size,'sha256':sha(p)} for n,p in files.items()}}
out.mkdir()
data=(json.dumps(capture,indent=2)+'\n').encode()
archive=out/'receipt.tar.gz'
with tarfile.open(archive,'w:gz') as stream:
 for n,p in sorted(files.items()):stream.add(p,arcname=n,recursive=False)
 info=tarfile.TarInfo('capture.json');info.size=len(data);stream.addfile(info,io.BytesIO(data))
record={'archive':str(archive),'bytes':archive.stat().st_size,'sha256':sha(archive),
 'files':len(files)+1,'capture_sha256':hashlib.sha256(data).hexdigest()}
(out/'transport.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
'''


def main():
    OUT.mkdir(exist_ok=False)
    (OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
    proc = subprocess.run(['ssh','-S',SOCKET,'-o','BatchMode=yes','mi350','python3','-'],
                          input=REMOTE,text=True,capture_output=True,timeout=180)
    (OUT/'capture.stdout').write_text(proc.stdout)
    (OUT/'capture.stderr').write_text(proc.stderr)
    assert proc.returncode == 0, proc.stderr
    record=json.loads(proc.stdout)
    (OUT/'transport.json').write_text(json.dumps(record,indent=2)+'\n')
    proc=subprocess.run(['scp','-q','-o','ControlPath='+SOCKET,'-o','BatchMode=yes',
                         'mi350:'+record['archive'],str(OUT/'receipt.tar.gz')],
                        text=True,capture_output=True,timeout=180)
    (OUT/'download.stdout').write_text(proc.stdout)
    (OUT/'download.stderr').write_text(proc.stderr)
    assert proc.returncode==0,proc.stderr
    raw=(OUT/'receipt.tar.gz').read_bytes()
    assert len(raw)==record['bytes'] and hashlib.sha256(raw).hexdigest()==record['sha256']
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        members=archive.getmembers()
        assert len(members)==len({m.name for m in members})==record['files']
        assert all(m.isfile() and not PurePosixPath(m.name).is_absolute()
                   and '..' not in PurePosixPath(m.name).parts for m in members)
        entries={m.name:archive.extractfile(m).read() for m in members}
    capture=json.loads(entries['capture.json'])
    assert hashlib.sha256(entries['capture.json']).hexdigest()==record['capture_sha256']
    assert set(entries)==set(capture['captured_files'])|{'capture.json'}
    for name,row in capture['captured_files'].items():
        data=entries[name]
        assert len(data)==row['bytes'] and hashlib.sha256(data).hexdigest()==row['sha256']
    target=OUT/'verified';target.mkdir()
    for name,data in entries.items():
        path=target/name;path.parent.mkdir(parents=True,exist_ok=True);path.write_bytes(data)
    (OUT/'results.json').write_text(json.dumps({'status':'complete-return-archive-independently-verified',
        **record,'downloaded_files':20,'returned_control_logs':98,'publication_reruns':0},indent=2)+'\n')
    print((OUT/'results.json').read_text(),flush=True)


if __name__=='__main__':main()
