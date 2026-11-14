from datetime import datetime,timezone
import hashlib,io,json,os,shutil,subprocess,sys,tarfile
from pathlib import Path,PurePosixPath
BASE=Path('/tmp/lark-paper-v26-controls-mi350-v2-20261113')
OLD=Path('/tmp/lark-paper-v26-controls-mi350-v1-20261113')
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for b in iter(lambda:f.read(1024*1024),b''):h.update(b)
 return h.hexdigest()
assert not BASE.exists(),'Inspect the existing version-two launch/PID instead of restarting'
payload=sys.stdin.buffer.read()
assert hashlib.sha256(payload).hexdigest()=='f2d908ceb9df66877147a695b4a80f05f8ea249927288535d2cdbf10ddf8283b'
entries={}
with tarfile.open(fileobj=io.BytesIO(payload),mode='r:') as archive:
 for member in archive:
  path=PurePosixPath(member.name)
  assert member.isfile() and member.size<=10000000 and not path.is_absolute() and '..' not in path.parts and str(path)==member.name and member.name not in entries
  entries[member.name]=archive.extractfile(member).read()
assert hashlib.sha256(entries['delta-manifest.json']).hexdigest()=='74d13a85eb4cf56687aa397afb6b283dfb7868b48bd97e81ce85f47573cd813d'
delta=json.loads(entries['delta-manifest.json'])
assert set(entries)==set(delta)|{'delta-manifest.json'}
assert all(hashlib.sha256(entries[n]).hexdigest()==h for n,h in delta.items())
assert sha(OLD/'bundle-manifest.json')=='404cab8ad340203c3af2e874278e440bd9fd39f84711db8b3e9c4964490fc386'
old=json.loads((OLD/'bundle-manifest.json').read_text())
assert all(sha(OLD/n)==h for n,h in old.items())
assert json.loads((OLD/'observer/results.json').read_text())['all_89_checks_completed'] is True
BASE.mkdir(mode=0o700)
selected=[n for n in old if n.startswith('source/') or n=='paper-source.tar']
for name in selected:
 target=BASE/name;target.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(OLD/name,target)
for name,data in entries.items():
 target=BASE/name;target.parent.mkdir(parents=True,exist_ok=True);target.write_bytes(data)
complete={name:sha(BASE/name) for name in sorted(set(selected)|set(delta))}
assert len(complete)==19
(BASE/'bundle-manifest.json').write_text(json.dumps(complete,indent=2)+'\n')
loaded={'at_utc':datetime.now(timezone.utc).isoformat(),'delta_tar_sha256':hashlib.sha256(payload).hexdigest(),
 'all_delta_bytes_verified':True,'all19_input_files_verified':True,
 'prior_verified_input_manifest_sha256':sha(OLD/'bundle-manifest.json'),
 'new_input_manifest_sha256':sha(BASE/'bundle-manifest.json'),'immutable_snapshot_reused':True,
 'snapshot_manifest_sha256':sha(BASE/'source/reproduction/paper_results/snapshots/20261113-v26/manifest.json')}
(BASE/'load.json').write_text(json.dumps(loaded,indent=2)+'\n')
with (BASE/'launch.json').open('x') as lock:
 lock.write('{"stage":"launching"}\n');lock.flush();os.fsync(lock.fileno())
 with (BASE/'launch.stdout').open('w') as stdout,(BASE/'launch.stderr').open('w') as stderr:
  child=subprocess.Popen(['/usr/bin/python3',str(BASE/'run-controls.py')],cwd=BASE,stdin=subprocess.DEVNULL,stdout=stdout,stderr=stderr,start_new_session=True)
 launch={'stage':'launched-once','pid':child.pid,'at_utc':datetime.now(timezone.utc).isoformat(),
 'host':'mi350','base':str(BASE),'source_checkpoint':'8f8c83ade2966bdc16af6e1ec49febbe0aa70e94',
 'aggregate_seconds':300,'per_replay_seconds':120,'max_independent_replayers':2,
 'GPU_jobs_started':0,'model_calls':0,'load':loaded}
 lock.seek(0);lock.truncate();lock.write(json.dumps(launch,indent=2)+'\n');lock.flush();os.fsync(lock.fileno())
print(json.dumps(launch),flush=True)
