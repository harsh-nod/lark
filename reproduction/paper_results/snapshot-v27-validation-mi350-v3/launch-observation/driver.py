"""Launch a new-code full suite against the same unchanged frozen v27 bytes."""
import hashlib
import json
from pathlib import Path
import subprocess

ROOT=Path('/tmp/lark-paper-v27-20261113')
OUT=Path('/tmp/lark-paper-v27-controls-mi350-launch-v3-20261113')
OUT.mkdir(exist_ok=False)
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
commit=subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()
assert commit.startswith('20f5f77') and not subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True).strip()
helpers={name:(ROOT/'reproduction/paper_results'/name).read_bytes() for name in (
    'replay_snapshot.py','check_snapshot_controls.py','snapshot_archives.py','snapshot_control_archives.py')}
driver=Path('/tmp/lark-run-paper-v27-controls-mi350-v1-20261113.py').read_bytes()
code=r'''
import hashlib,json,os,shutil,subprocess
from pathlib import Path
old=Path('/tmp/lark-paper-v27-controls-mi350-v2-20261113')
root=Path('/tmp/lark-paper-v27-controls-mi350-v3-20261113')
assert not root.exists()
assert json.loads((old/'observer/results.json').read_text())['timed_out'] is True
assert not Path('/proc/992133').exists() and not Path('/proc/992134').exists()
root.mkdir()
relative=Path('reproduction/paper_results')
source=root/'source'/relative
source.mkdir(parents=True)
snapshot=source/'snapshots/20261113-v27'
shutil.copytree(old/'source'/relative/'snapshots/20261113-v27',snapshot,copy_function=os.link)
for name,data in HELPERS.items():(source/name).write_bytes(data)
for name in ['paper-source.tar','previous-v26-controls.json']:
 os.link(old/name,root/name)
(root/'driver.py').write_bytes(DRIVER)
expected=json.loads((old/'expected.json').read_text())
expected['source_checkpoint']=COMMIT
(root/'expected.json').write_text(json.dumps(expected,indent=2)+'\n')
def sha(path):
 d=hashlib.sha256()
 with path.open('rb') as stream:
  while data:=stream.read(1024*1024):d.update(data)
 return d.hexdigest()
assert sha(snapshot/'manifest.json')=='aa23c786cf8a7c2ca059c76beddcb86dc148dc03e3d70096e0bd2f930044fea0'
manifest={p.relative_to(root).as_posix():sha(p) for p in sorted(root.rglob('*')) if p.is_file()}
(root/'bundle-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
with (root/'driver.stdout').open('xb') as stdout,(root/'driver.stderr').open('xb') as stderr:
 child=subprocess.Popen(['python3',str(root/'driver.py')],cwd=root,stdin=subprocess.DEVNULL,stdout=stdout,stderr=stderr,start_new_session=True)
record={'pid':child.pid,'root':str(root),'source_checkpoint':COMMIT,'complete_input_files':len(manifest)+1,
 'same_snapshot_manifest_sha256':expected['snapshot_manifest_sha256'],
 'complete_original_snapshot_files_copied_as_immutable_regular_hardlinks':True,
 'old_failed_workspace_untouched':True,'new_code_not_same_job_restart':True}
(root/'launch.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
'''.replace('HELPERS',repr(helpers)).replace('DRIVER',repr(driver)).replace('COMMIT',repr(commit))
(OUT/'remote-launch.py').write_text(code)
result=subprocess.run(['ssh','-S','/tmp/lark-glm-cuda-cohort-publication-forward-20261113.sock','-o','BatchMode=yes','mi350','python3','-'],input=code,text=True,capture_output=True,timeout=60)
(OUT/'stdout.log').write_text(result.stdout);(OUT/'stderr.log').write_text(result.stderr)
assert result.returncode==0,result.stderr
(OUT/'results.json').write_text(json.dumps(json.loads(result.stdout),indent=2)+'\n')
(OUT/'manifest.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.iterdir()) if p.is_file()},indent=2)+'\n')
print(result.stdout,end='')
