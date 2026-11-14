"""Compare the complete old and emitted-digest producer inputs, including every byte."""
import hashlib,json,os,shutil,sys,time
from pathlib import Path
ROOT=Path('/tmp/lark-paper-v27-20261113')
BASE=Path('/tmp/lark-v27-ram-input-equivalence-v1-20261113/ssd')
OUT=Path('/tmp/lark-v27-producer-equivalence-v1-20261113')
assert not OUT.exists()
OUT.mkdir()
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
sys.path.insert(0,str(ROOT))
from reproduction.paper_results.check_snapshot_controls import file_set,rehash
target=OUT/'input'
def copy(source,destination):
 if Path(source).name.startswith('evidence-part-'):
  os.link(source,destination)
 else:shutil.copyfile(source,destination)
 return destination
shutil.copytree(BASE,target,copy_function=copy)
layout=json.loads((target/'evidence-layout.json').read_text())
started=time.monotonic()
rehash(target,archive_changed=True,emitted_archives=layout['archives'])
elapsed=time.monotonic()-started
assert file_set(BASE)==file_set(target)
bindings={}
for name in sorted(file_set(BASE)):
 digest=hashlib.sha256();size=0
 with (BASE/name).open('rb') as left,(target/name).open('rb') as right:
  while True:
   a,b=left.read(1024*1024),right.read(1024*1024)
   assert a==b,name
   if not a:break
   size+=len(a);digest.update(a)
 bindings[name]={'bytes':size,'sha256':digest.hexdigest()}
record={'status':'complete-original-and-emitted-digest-control-inputs-byte-identical',
 'baseline':str(BASE),'revised':str(target),'logical_files':len(layout['logical_files']),
 'physical_files':len(bindings),'compared_bytes':sum(r['bytes'] for r in bindings.values()),
 'all_file_bindings':bindings,'new_producer_manifest_seconds':elapsed,
 'scope':'Producer-only input equivalence. No independent reader hash check is removed; full98 still required.',
 'new_replays':0,'Lean_checks':0,'GPU_trials':0,'model_calls':0,'original_paper_fully_reproduced':False}
(OUT/'results.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='all_file_bindings'}),flush=True)
