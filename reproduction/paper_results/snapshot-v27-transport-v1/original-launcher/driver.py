"""Ship complete standalone v27 inputs and launch exactly one owned CPU suite."""
import hashlib
import io
import json
from pathlib import Path
import shlex
import subprocess
import tarfile
import time

ROOT=Path('/tmp/lark-paper-v27-20261113')
OUT=Path('/tmp/lark-paper-v27-controls-mi350-launch-v1-20261113')
REMOTE='/tmp/lark-paper-v27-controls-mi350-v1-20261113'
ARCHIVE=Path('/tmp/lark-paper-v27-controls-mi350-input-v1-20261113.tar')
SOCKET='/tmp/lark-glm-cuda-cohort-publication-forward-20261113.sock'
SSH=['ssh','-S',SOCKET,'-o','BatchMode=yes','-o','ConnectTimeout=15','mi350']


def sha(path):
    value=hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda:stream.read(1024*1024),b''):
            value.update(data)
    return value.hexdigest()


def write(name,value):
    (OUT/name).write_text(json.dumps(value,indent=2)+'\n')


def call(name,command,timeout=180):
    started=time.monotonic()
    result=subprocess.run(command,text=True,capture_output=True,timeout=timeout)
    (OUT/(name+'.stdout')).write_text(result.stdout)
    (OUT/(name+'.stderr')).write_text(result.stderr)
    write(name+'.json',{'command':command,'returncode':result.returncode,'seconds':time.monotonic()-started})
    assert result.returncode==0,name+': '+result.stderr
    return result.stdout


def main():
    OUT.mkdir(exist_ok=False)
    (OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
    assert not ARCHIVE.exists()
    relative=Path('reproduction/paper_results')
    snap=relative/'snapshots/20261113-v27'
    bindings=json.loads((ROOT/snap/'manifest.json').read_text())
    paths={p.relative_to(ROOT/snap).as_posix() for p in (ROOT/snap).rglob('*') if p.is_file()}
    assert paths==set(bindings)|{'manifest.json'}
    assert all(sha(ROOT/snap/name)==value for name,value in bindings.items())
    helpers=[relative/name for name in ('replay_snapshot.py','check_snapshot_controls.py','snapshot_archives.py','snapshot_control_archives.py')]
    files={'source/'+p.as_posix():ROOT/p for p in [*helpers,*[snap/name for name in sorted(paths)]]}
    files.update({'driver.py':Path('/tmp/lark-run-paper-v27-controls-mi350-v1-20261113.py'),
                  'previous-v26-controls.json':ROOT/'reproduction/ptx/results/full-size-rotary-proof-io-mi350-v1/validation/results.json',
                  'paper-source.tar':Path('/tmp/lark-reproduction-paper-source.tar')})
    expected={'source_checkpoint':'3d90539b12c1024ace08756b942706d23dff0e5d',
              'snapshot_manifest_sha256':sha(ROOT/snap/'manifest.json'),
              'baseline_snapshot_manifest_sha256':'251d9b381282f54cc721587bc88d78e0f344a44eaeaf03f112fb6f6556baf6ed'}
    write('expected.json',expected)
    files['expected.json']=OUT/'expected.json'
    manifest={name:sha(path) for name,path in sorted(files.items())}
    write('bundle-manifest.json',manifest)
    files['bundle-manifest.json']=OUT/'bundle-manifest.json'
    with tarfile.open(ARCHIVE,'w',format=tarfile.PAX_FORMAT) as archive:
        for name,path in sorted(files.items()):
            assert path.is_file() and not path.is_symlink()
            info=tarfile.TarInfo(name)
            info.size=path.stat().st_size
            info.mode=0o644
            with path.open('rb') as stream:
                archive.addfile(info,stream)
    digest=sha(ARCHIVE)
    write('transport.json',{'archive':str(ARCHIVE),'sha256':digest,'bytes':ARCHIVE.stat().st_size,
                            'complete_files':len(files),'remote':REMOTE})
    code="from pathlib import Path; assert not Path(%r).exists() and not Path(%r).exists(), 'Observe existing inputs or job instead of replacing them'"%(REMOTE,REMOTE+'.tar')
    call('remote-fresh-preflight',SSH+[shlex.join(['python3','-c',code])])
    call('transport',['scp','-q','-o','ControlPath='+SOCKET,'-o','BatchMode=yes',str(ARCHIVE),'mi350:'+REMOTE+'.tar'])
    code=r'''
import hashlib,json,subprocess,tarfile
from pathlib import Path,PurePosixPath
root=Path(REMOTE)
archive=root.with_suffix('.tar')
assert hashlib.sha256(archive.read_bytes()).hexdigest()==EXPECTED
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
'''.replace('REMOTE',repr(REMOTE)).replace('EXPECTED',repr(digest))
    launched=call('launch',SSH+[shlex.join(['python3','-c',code])])
    write('results.json',json.loads(launched))
    write('manifest.json',{p.name:sha(p) for p in sorted(OUT.iterdir()) if p.is_file()})
    print(launched,flush=True)


if __name__=='__main__':
    main()
