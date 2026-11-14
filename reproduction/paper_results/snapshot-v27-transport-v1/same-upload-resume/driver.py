"""Resume the verified existing upload, then launch its one original CPU suite."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shlex
import subprocess
import time

OUT=Path('/tmp/lark-paper-v27-controls-mi350-transport-resume-v2-20261113')
ARCHIVE=Path('/tmp/lark-paper-v27-controls-mi350-input-v1-20261113.tar')
REMOTE='/tmp/lark-paper-v27-controls-mi350-v1-20261113'
EXPECTED='dc5fe389c383ccd73d8f22573fd939f089d6b2db8a7f4ddbd70f2d478a68021f'
SSH=['ssh','-S','/tmp/lark-glm-cuda-cohort-publication-forward-20261113.sock','-o','BatchMode=yes','-o','ConnectTimeout=15','mi350']


def write(name,value):
    path=OUT/(name+'.next')
    path.write_text(json.dumps(value,indent=2)+'\n')
    path.replace(OUT/name)


def sha(path,limit=None):
    digest=hashlib.sha256()
    left=limit
    with path.open('rb') as source:
        while left is None or left:
            data=source.read(1024*1024 if left is None else min(left,1024*1024))
            if not data: break
            digest.update(data)
            if left is not None: left-=len(data)
    assert left in (None,0)
    return digest.hexdigest()


def call(name,code):
    command=SSH+[shlex.join(['python3','-c',code])]
    result=subprocess.run(command,text=True,capture_output=True,timeout=120)
    (OUT/(name+'.stdout')).write_text(result.stdout)
    (OUT/(name+'.stderr')).write_text(result.stderr)
    write(name+'.json',{'command':command,'exit_code':result.returncode})
    assert result.returncode==0,result.stderr
    return json.loads(result.stdout)


def main():
    OUT.mkdir(exist_ok=False)
    (OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
    assert sha(ARCHIVE)==EXPECTED
    preflight=call('prefix-preflight',r'''
import hashlib,json
from pathlib import Path
root=Path(REMOTE)
assert not root.exists(), 'Observe the existing job rather than resuming an upload'
path=root.with_suffix('.tar')
before=path.stat()
digest=hashlib.sha256()
with path.open('rb') as source:
    while data:=source.read(1024*1024): digest.update(data)
after=path.stat()
assert (before.st_size,before.st_mtime_ns)==(after.st_size,after.st_mtime_ns)
print(json.dumps({'bytes':after.st_size,'sha256':digest.hexdigest(),'mtime_ns':after.st_mtime_ns}))
'''.replace('REMOTE',repr(REMOTE)))
    offset=preflight['bytes']
    assert 0<offset<ARCHIVE.stat().st_size
    assert sha(ARCHIVE,offset)==preflight['sha256']
    write('verified-prefix.json',{**preflight,'matches_local_prefix':True,'local_complete_sha256':EXPECTED,
                                  'local_complete_bytes':ARCHIVE.stat().st_size,
                                  'original_launcher_session':26692,'original_launcher_exit_code':1,
                                  'original_failure':'SCP TimeoutExpired after180transportseconds; no scientific suite launched'})
    code=r'''
import hashlib,json,sys
from pathlib import Path
root=Path(REMOTE)
assert not root.exists()
path=root.with_suffix('.tar')
assert path.stat().st_size==OFFSET
with path.open('ab') as target:
    while data:=sys.stdin.buffer.read(1024*1024): target.write(data)
assert path.stat().st_size==COMPLETE_BYTES
digest=hashlib.sha256()
with path.open('rb') as source:
    while data:=source.read(1024*1024): digest.update(data)
assert digest.hexdigest()==EXPECTED
print(json.dumps({'status':'same-partial-upload-resumed-and-completely-verified','bytes':path.stat().st_size,'sha256':digest.hexdigest()}),flush=True)
'''.replace('REMOTE',repr(REMOTE)).replace('OFFSET',str(offset)).replace('COMPLETE_BYTES',str(ARCHIVE.stat().st_size)).replace('EXPECTED',repr(EXPECTED))
    command=SSH+[shlex.join(['python3','-c',code])]
    started=time.monotonic()
    with ARCHIVE.open('rb') as source,(OUT/'append.stdout').open('w') as stdout,(OUT/'append.stderr').open('w') as stderr:
        source.seek(offset)
        child=subprocess.Popen(command,stdin=source,stdout=stdout,stderr=stderr,start_new_session=True)
        write('progress.json',{'stage':'resuming-exact-existing-upload','pid':child.pid,
                               'offset':offset,'command':command,'at_utc':datetime.now(timezone.utc).isoformat()})
        status=child.wait()
    write('append.json',{'command':command,'exit_code':status,'seconds':time.monotonic()-started})
    assert status==0,(OUT/'append.stderr').read_text()
    launch=call('launch',r'''
import hashlib,json,subprocess,tarfile
from pathlib import Path,PurePosixPath
root=Path(REMOTE)
archive=root.with_suffix('.tar')
digest=hashlib.sha256()
with archive.open('rb') as source:
    while data:=source.read(1024*1024): digest.update(data)
assert digest.hexdigest()==EXPECTED
assert not root.exists()
root.mkdir()
with tarfile.open(archive,'r:') as stream:
    names=set()
    for member in stream:
        name=PurePosixPath(member.name)
        assert member.isfile() and not name.is_absolute() and '..' not in name.parts and str(name)==member.name
        assert member.name not in names
        names.add(member.name)
        target=root/member.name
        target.parent.mkdir(parents=True,exist_ok=True)
        with stream.extractfile(member) as source,target.open('xb') as output:
            while data:=source.read(1024*1024): output.write(data)
bindings=json.loads((root/'bundle-manifest.json').read_text())
assert names==set(bindings)|{'bundle-manifest.json'}
for name,value in bindings.items():
    digest=hashlib.sha256()
    with (root/name).open('rb') as source:
        while data:=source.read(1024*1024): digest.update(data)
    assert digest.hexdigest()==value
with (root/'driver.stdout').open('xb') as stdout,(root/'driver.stderr').open('xb') as stderr:
    child=subprocess.Popen(['python3',str(root/'driver.py')],cwd=root,stdin=subprocess.DEVNULL,stdout=stdout,stderr=stderr,start_new_session=True)
record={'pid':child.pid,'remote':str(root),'archive_sha256':EXPECTED,'files':len(names),'stage':'launched-one-owned-CPU-control-suite'}
(root/'launch.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
'''.replace('REMOTE',repr(REMOTE)).replace('EXPECTED',repr(EXPECTED)))
    write('results.json',launch)
    write('progress.json',{'stage':'terminal-original-suite-launched','launch':launch})
    write('manifest.json',{p.name:sha(p) for p in sorted(OUT.iterdir()) if p.is_file()})
    print(json.dumps(launch),flush=True)


if __name__=='__main__':
    main()
