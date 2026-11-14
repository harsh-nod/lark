"""Compare every byte of the same complete false input on disk and RAM."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

ROOT=Path('/tmp/lark-paper-v27-20261113')
OUT=Path('/tmp/lark-v27-ram-input-equivalence-v1-20261113')
RAM=Path('/dev/shm/lark-v27-ram-input-equivalence-v1-20261113')
assert not OUT.exists() and not RAM.exists()
assert shutil.disk_usage(RAM.parent).free>4*1024**3
OUT.mkdir()
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
sys.path.insert(0,str(ROOT))
from reproduction.paper_results import check_snapshot_controls as controls

SNAPSHOT=ROOT/'reproduction/paper_results/snapshots/20261113-v27'
SOURCE='ceb5eb799fc9f803dcd425b24a3806e85f741806'
for name in ['replay_snapshot.py','snapshot_archives.py','snapshot_control_archives.py','check_snapshot_controls.py']:
 path=ROOT/'reproduction/paper_results'/name
 assert path.read_bytes()==subprocess.check_output(['git','show',SOURCE+':reproduction/paper_results/'+name],cwd=ROOT)
start=time.monotonic()
packed=controls.control_archive(SNAPSHOT)
entries=packed.entries.copy()
targets=json.loads((SNAPSHOT/'targets.json').read_text())
controls.mutate_rotary_evidence(entries,targets,'rotary-rechecks-counted-as-kernels')
copies=controls.ControlSnapshotCopies(SNAPSHOT)
ssd=OUT/'ssd'
for path in [ssd,RAM]:
 copies.copy(path,rewrite_archive=True)
 packed.write(path,entries)
 controls.rehash(path,archive_changed=True)
left=controls.file_set(ssd);right=controls.file_set(RAM)
assert left==right
bindings={}
for name in sorted(left):
 digest=hashlib.sha256();size=0
 with (ssd/name).open('rb') as a,(RAM/name).open('rb') as b:
  while True:
   first,second=a.read(1024*1024),b.read(1024*1024)
   assert first==second,name
   if not first:break
   digest.update(first);size+=len(first)
 bindings[name]={'bytes':size,'sha256':digest.hexdigest()}
packed.close()
record={'status':'complete-disk-and-RAM-false-inputs-byte-identical','source_commit':SOURCE,
 'source_snapshot_manifest_sha256':controls.sha(SNAPSHOT/'manifest.json'),
 'case':'rotary-rechecks-counted-as-kernels','logical_files_retained':len(entries),
 'physical_files':len(bindings),'all_file_bindings':bindings,
 'total_complete_input_bytes_compared':sum(x['bytes'] for x in bindings.values()),
 'seconds':time.monotonic()-start,'disk_path':str(ssd),'RAM_path':str(RAM),
 'both_complete_inputs_retained':True,'replays':0,'Lean_checks':0,'GPU_trials':0,'model_calls':0,
 'scope':'Storage-equivalence check only. Does not replace any of the required98 cases or establish a CI pass.',
 'original_paper_fully_reproduced':False}
(OUT/'results.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k!='all_file_bindings'}),flush=True)
