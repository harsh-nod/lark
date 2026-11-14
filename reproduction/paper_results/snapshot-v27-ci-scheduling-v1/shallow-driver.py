"""Reproduce the historical-blob ancestry guard with isolated shallow/full views."""
import hashlib
import json
from pathlib import Path
import subprocess
import sys

ROOT=Path('/tmp/lark-paper-v27-20261113')
OUT=Path('/tmp/lark-v27-shallow-history-v1-20261113')
OUT.mkdir(exist_ok=False)
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
sys.path.insert(0,str(ROOT))
from reproduction.paper_results.replay_snapshot import committed_evidence
name='reproduction/paper_results/replay_snapshot.py'
base=ROOT/'reproduction/paper_results/snapshots/20261113-v26'
origin=json.loads((base/'provenance.json').read_text())['sources'][name]
digest=json.loads((base/'evidence-manifest.json').read_text())[name]
binding={name:{'commit':origin['commit'],'sha256':digest}}
current=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
common=Path(subprocess.check_output(['git','rev-parse','--git-common-dir'],cwd=ROOT,text=True).strip())
common=(ROOT/common).resolve() if not common.is_absolute() else common
records=[]
for mode in ['full','shallow']:
 repo=OUT/(mode+'.git')
 subprocess.run(['git','init','--bare','--quiet',str(repo)],check=True)
 (repo/'objects/info/alternates').write_text(str(common/'objects')+'\n')
 subprocess.run(['git','--git-dir='+str(repo),'update-ref','refs/heads/fixture',current],check=True)
 if mode=='shallow':(repo/'shallow').write_text(current+'\n')
 is_shallow=subprocess.check_output(['git','--git-dir='+str(repo),'rev-parse','--is-shallow-repository'],text=True).strip()
 subprocess.run(['git','--git-dir='+str(repo),'cat-file','-e',origin['commit']],check=True)
 try:
  data,actual_origin=committed_evidence(name,current,binding,root=repo)
 except ValueError as exc:
  assert mode=='shallow' and 'not an ancestor' in str(exc)
  records.append({'mode':mode,'is_shallow':is_shallow,'status':'correctly-rejected','detail':str(exc)})
 else:
  assert mode=='full' and hashlib.sha256(data).hexdigest()==digest and actual_origin['commit']==origin['commit']
  records.append({'mode':mode,'is_shallow':is_shallow,'status':'original-ancestor-bytes-verified','sha256':digest})
record={'status':'shallow-ancestry-failure-reproduced-full-ancestry-passed','source':current,
 'original_commit':origin['commit'],'logical_path':name,'checks':records,
 'original_repository_objects_read_only':True,'original_paper_fully_reproduced':False,
 'fresh_Lean_GPU_model_experiments':0}
(OUT/'results.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
