from pathlib import Path
import hashlib,json,shutil,subprocess,sys,zipfile
root=Path('/tmp/lark-native-rope-20261111');sys.path.insert(0,str(root))
from reproduction.production_rope import check_program as rope
from reproduction.production_softmax import check_native_real as real,check_original_race as race
out=Path('/tmp/lark-native-rope-packaging-v2-20261111');out.mkdir()
commit='84d0ef6ea3e87ac306e21cfbd1f17f164bf804bb'
git=lambda *args:subprocess.check_output(['git','-C',str(root),*args])
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
closure=set()
for target in (real.TARGET,race.TARGET,race.grid.TARGET,race.base.TARGET,race.prefix.TARGET):real.modules(target,closure)
owned={};rope.modules('Lark.NativeRopeAddress',owned);closure.update(owned)
assert len(closure)==146 and len(owned)==4
wheel,=Path('/tmp/lark-native-rope-wheel-v3-20261111').glob('*.whl')
matched={}
with zipfile.ZipFile(wheel) as z:
 for name in sorted(closure):
  path=('lean-real/' if name.startswith('LarkReal.') else 'lean/')+name.replace('.','/')+'.lean'
  entries=[n for n in z.namelist() if n.endswith('/share/lark/'+path)];assert len(entries)==1,path
  blob=z.read(entries[0]);assert blob==(root/path).read_bytes()==git('show',commit+':'+path),path
  matched[path]=hashlib.sha256(blob).hexdigest()
 for path in ('lark_kernels/native_rope.py','lark_kernels/native_softmax.py'):
  blob=z.read(path);assert blob==(root/path).read_bytes()==git('show',commit+':'+path),path
  matched[path]=hashlib.sha256(blob).hexdigest()
 assert (root/'pyproject.toml').read_bytes()==git('show',commit+':pyproject.toml')
report={'schema':1,'status':'wheel-native-rope-and-earlier-softmax-proof-closure-bytes-checked',
 'source_commit':commit,'wheel_bytes':wheel.stat().st_size,'wheel_sha256':sha(wheel),
 'packaged_proof_modules':len(closure),'native_rope_required_modules':len(owned),'earlier_softmax_required_modules':143,
 'matched_source_sha256':matched,'all_selected_proof_reader_packaging_bytes_match_source_commit':True,
 'pyproject_sha256':sha(root/'pyproject.toml'),'native_rope_source_certificates':0,
 'native_rope_complete_launch_proved':False,'original_paper_fully_reproduced':False}
(out/'results.json').write_text(json.dumps(report,indent=2)+'\n')
shutil.copyfile('/tmp/lark-native-rope-wheel-build-v3-20261111.log',out/'build.log')
shutil.copyfile(__file__,out/'checker.py')
(out/'manifest.json').write_text(json.dumps({p.name:sha(p) for p in sorted(out.iterdir())},indent=2)+'\n')
print(json.dumps({k:report[k] for k in ('status','wheel_bytes','packaged_proof_modules')}))
