"""Recover terminal public-validation evidence without repeating any experiment."""

from datetime import datetime, timezone
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import subprocess
import tarfile

OUT = Path('/tmp/lark-paper-v26-publication-return-v2-20261113')
REMOTE = '/tmp/lark-paper-v26-publication-capture-v2-20261113'
SOURCE = 'ce5611655946a0a8cca76f97beb8f85bf8f4fc2b'

REMOTE_CODE = r'''
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
'''


def run(name, command, *, data=None, timeout=90):
    result = subprocess.run(command, input=data, capture_output=True, timeout=timeout)
    (OUT / (name + '.stdout')).write_bytes(result.stdout)
    (OUT / (name + '.stderr')).write_bytes(result.stderr)
    assert result.returncode == 0, (name, result.returncode)
    return result.stdout


def main():
    assert not OUT.exists(), 'Inspect the original recovery instead of repeating it'
    OUT.mkdir()
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    (OUT / 'remote-capture.py').write_text(REMOTE_CODE)
    response = run('capture', ['ssh', '-o', 'BatchMode=yes', '-o', 'ConnectTimeout=20',
                             'mi350', '/usr/bin/python3', '-'], data=REMOTE_CODE.encode())
    transport = json.loads(response)
    assert transport['source_commit'] == SOURCE and transport['tar'] == REMOTE + '/receipt.tar'
    (OUT / 'transport.json').write_text(json.dumps(transport, indent=2) + '\n')
    run('download', ['scp', '-q', '-o', 'BatchMode=yes', '-o', 'ConnectTimeout=20',
                     'mi350:' + transport['tar'], str(OUT / 'receipt.tar')])
    raw = (OUT / 'receipt.tar').read_bytes()
    assert len(raw) == transport['bytes'] and hashlib.sha256(raw).hexdigest() == transport['sha256']
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        members = archive.getmembers()
        assert len({m.name for m in members}) == len(members) == transport['files'] + 1
        assert all(m.isfile() and not PurePosixPath(m.name).is_absolute()
                   and '..' not in PurePosixPath(m.name).parts for m in members)
        entries = {m.name: archive.extractfile(m).read() for m in members}
    inventory_bytes = entries.pop('capture.json')
    assert hashlib.sha256(inventory_bytes).hexdigest() == transport['capture_sha256']
    inventory = json.loads(inventory_bytes)
    assert inventory['source_commit'] == SOURCE
    assert set(entries) == {r['path'] for r in inventory['files']}
    for record in inventory['files']:
        data = entries[record['path']]
        assert len(data) == record['bytes'] and hashlib.sha256(data).hexdigest() == record['sha256']
    for name, data in {**entries, 'capture.json': inventory_bytes}.items():
        target = OUT / 'verified' / name
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(data)
    result = {'status': 'all-terminal-publication-receipt-bytes-recovered-and-verified',
              'source_commit': SOURCE, 'files': len(entries), 'tar_bytes': len(raw),
              'capture_sha256': transport['capture_sha256'],
              'observed_at_utc': datetime.now(timezone.utc).isoformat(),
              'new_model_GPU_Lean_or_replay_calls': 0}
    (OUT / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
