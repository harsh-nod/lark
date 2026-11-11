from pathlib import Path
import hashlib,json,shutil,sys,zipfile
root=Path('/tmp/lark-native-softmax-exp-prefix-20261111');sys.path.insert(0,str(root))
from reproduction.production_softmax import check_exp_prefix as m
out=Path('/tmp/lark-native-softmax-exp-prefix-packaging-v1-20261111');out.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
closure=set()
for target in (m.TARGET,m.base.TARGET,m.prefix.TARGET):m.base.modules(target,closure)
wheel,=Path('/tmp/lark-softmax-exp-prefix-wheel-v2-20261111').glob('*.whl')
matched={}
with zipfile.ZipFile(wheel) as z:
 for module in sorted(closure):
  relative=module.replace('.','/')+'.lean'
  entries=[n for n in z.namelist() if n.endswith('/share/lark/lean/'+relative)]
  assert len(entries)==1,relative
  content=z.read(entries[0]);assert content==(root/'lean'/relative).read_bytes(),relative
  matched[relative]=hashlib.sha256(content).hexdigest()
 assert z.read('lark_kernels/native_softmax.py')==(root/'lark_kernels/native_softmax.py').read_bytes()
report={'schema':1,'status':'wheel-reader-and-exp-prefix-proof-closure-bytes-checked','wheel_file':wheel.name,'wheel_bytes':wheel.stat().st_size,'wheel_sha256':sha(wheel),'packaged_proof_modules':len(closure),'matched_source_sha256':matched,'reader_sha256':sha(root/'lark_kernels/native_softmax.py'),'source_certificates':0,'whole_kernel_execution_proved':False,'original_paper_fully_reproduced':False}
(out/'results.json').write_text(json.dumps(report,indent=2)+'\n')
shutil.copyfile('/tmp/lark-softmax-exp-prefix-wheel-build-v2-20261111.log',out/'build.log')
shutil.copyfile(__file__,out/'checker.py')
(out/'manifest.json').write_text(json.dumps({p.name:sha(p) for p in sorted(out.iterdir()) if p.is_file()},indent=2)+'\n')
print(json.dumps({k:report[k] for k in ('status','wheel_bytes','packaged_proof_modules')}))
