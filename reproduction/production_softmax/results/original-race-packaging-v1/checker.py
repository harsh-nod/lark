from pathlib import Path
import hashlib,json,shutil,subprocess,sys,zipfile
root=Path('/tmp/lark-native-softmax-race-reachability-20261111');sys.path.insert(0,str(root))
from reproduction.production_softmax import check_native_real as real,check_original_race as race
out=Path('/tmp/lark-native-softmax-original-race-packaging-v1-20261111');out.mkdir()
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
ci='817ef958bd8347e190e5229d993242561c4d8b7d'
git=lambda *args:subprocess.check_output(['git','-C',str(root),*args])
closure=set()
for target in (real.TARGET,race.TARGET,race.grid.TARGET,race.base.TARGET,race.prefix.TARGET):real.modules(target,closure)
wheel,=Path('/tmp/lark-softmax-original-race-wheel-v1-20261111').glob('*.whl')
matched={}
with zipfile.ZipFile(wheel) as z:
 for module in sorted(closure):
  relative=('lean-real/' if module.startswith('LarkReal.') else 'lean/')+module.replace('.','/')+'.lean'
  entries=[n for n in z.namelist() if n.endswith('/share/lark/'+relative)];assert len(entries)==1,relative
  blob=z.read(entries[0]);assert blob==(root/relative).read_bytes()==git('show',ci+':'+relative),relative
  matched[relative]=hashlib.sha256(blob).hexdigest()
 assert z.read('lark_kernels/native_softmax.py')==(root/'lark_kernels/native_softmax.py').read_bytes()==git('show',ci+':lark_kernels/native_softmax.py')
assert len(closure)==143 and sum(n.startswith('LarkReal.') for n in closure)==5
assert (root/'pyproject.toml').read_bytes()==git('show',ci+':pyproject.toml')
report={'schema':1,'status':'wheel-reader-and-softmax-reached-race-real-proof-closure-bytes-checked',
 'wheel_file':wheel.name,'wheel_bytes':wheel.stat().st_size,'wheel_sha256':sha(wheel),
 'packaged_proof_modules':143,'standard_proof_modules':138,'real_proof_modules':5,
 'matched_source_sha256':matched,'reader_sha256':sha(root/'lark_kernels/native_softmax.py'),
 'source_commit':ci,'all_selected_proof_reader_and_packaging_bytes_match_ci_source':True,
 'pyproject_sha256':sha(root/'pyproject.toml'),'source_certificates':0,
 'original_paper_fully_reproduced':False}
(out/'results.json').write_text(json.dumps(report,indent=2)+'\n')
shutil.copyfile('/tmp/lark-softmax-original-race-wheel-build-v1-20261111.log',out/'build.log')
shutil.copyfile(__file__,out/'checker.py')
(out/'manifest.json').write_text(json.dumps({p.name:sha(p) for p in sorted(out.iterdir()) if p.is_file()},indent=2)+'\n')
print(json.dumps({k:report[k] for k in ('status','wheel_bytes','packaged_proof_modules')}))
