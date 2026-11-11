from pathlib import Path
import hashlib,json,shutil,subprocess,sys,zipfile
root=Path('/tmp/lark-native-softmax-exp-block-20261111');sys.path.insert(0,str(root))
from reproduction.production_softmax import check_native_real as m
out=Path('/tmp/lark-native-softmax-grid-real-packaging-v1-20261111');out.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ci='a23a5da395470876ab8a72a2ed0a04f2f58c6747'
git=lambda *args:subprocess.check_output(['git','-C',str(root),*args])
closure=set()
for target in (m.TARGET,m.grid.base.TARGET,m.grid.prefix.TARGET):m.modules(target,closure)
wheel,=Path('/tmp/lark-softmax-grid-real-wheel-v1-20261111').glob('*.whl')
matched={}
with zipfile.ZipFile(wheel) as z:
 for module in sorted(closure):
  relative=('lean-real/' if module.startswith('LarkReal.') else 'lean/')+module.replace('.','/')+'.lean'
  entries=[n for n in z.namelist() if n.endswith('/share/lark/'+relative)]
  assert len(entries)==1,relative
  content=z.read(entries[0]);assert content==(root/relative).read_bytes()==git('show',ci+':'+relative),relative
  matched[relative]=hashlib.sha256(content).hexdigest()
 assert z.read('lark_kernels/native_softmax.py')==(root/'lark_kernels/native_softmax.py').read_bytes()==git('show',ci+':lark_kernels/native_softmax.py')
old=git('show',ci+':pyproject.toml').decode();new=(root/'pyproject.toml').read_text()
assert new==old.replace('"lean-real/LarkReal/OnlineSoftmax.lean"]','"lean-real/LarkReal/OnlineSoftmax.lean", "lean-real/LarkReal/NativeSoftmax*.lean"]')
assert len(closure)==134 and sum(n.startswith('LarkReal.') for n in closure)==5
report={'schema':1,'status':'wheel-reader-and-softmax-grid-real-proof-closure-bytes-checked',
 'wheel_file':wheel.name,'wheel_bytes':wheel.stat().st_size,'wheel_sha256':sha(wheel),
 'packaged_proof_modules':134,'standard_proof_modules':129,'real_proof_modules':5,
 'matched_source_sha256':matched,'reader_sha256':sha(root/'lark_kernels/native_softmax.py'),
 'proof_source_commit':ci,'all_selected_proof_and_reader_bytes_match_ci_source':True,
 'pyproject_sha256':sha(root/'pyproject.toml'),'ci_pyproject_sha256':hashlib.sha256(old.encode()).hexdigest(),
 'packaging_change':'Only add lean-real/LarkReal/NativeSoftmax*.lean to wheel data files; four new modules now included. Proof, reader and checker implementation bytes are unchanged from the CI source commit.',
 'source_certificates':0,'ieee_equivalence_proved':False,'original_paper_fully_reproduced':False}
(out/'results.json').write_text(json.dumps(report,indent=2)+'\n')
shutil.copyfile('/tmp/lark-softmax-grid-real-wheel-build-v1-20261111.log',out/'build.log')
shutil.copyfile(__file__,out/'checker.py')
(out/'manifest.json').write_text(json.dumps({p.name:sha(p) for p in sorted(out.iterdir()) if p.is_file()},indent=2)+'\n')
print(json.dumps({k:report[k] for k in ('status','wheel_bytes','packaged_proof_modules','real_proof_modules')}))
