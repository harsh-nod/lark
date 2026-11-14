"""Launch one fresh full suite for the changed producer at an exact Git commit."""
import ast
import base64
import hashlib
import json
from pathlib import Path
import subprocess

ROOT=Path('/tmp/lark-paper-v27-20261113')
OUT=Path('/tmp/lark-paper-v27-controls-mi350-launch-v5-20261114')
SOURCE='f305b2acea0beb858164d9c379a61effedee42a0'
REMOTE=r'''
import base64,hashlib,json,os,shutil,subprocess
from pathlib import Path
old=Path('/tmp/lark-paper-v27-controls-mi350-v4-20261113')
root=Path('/tmp/lark-paper-v27-controls-mi350-v5-20261114')
assert not root.exists()
assert json.loads((old/'observer/results.json').read_text())['status']=='complete-control-suite-passed'
assert not Path('/proc/1089515').exists() and not Path('/proc/1089516').exists()
root.mkdir()
relative=Path('reproduction/paper_results')
source=root/'source'/relative;source.mkdir(parents=True)
snapshot=source/'snapshots/20261113-v27'
shutil.copytree(old/'source'/relative/'snapshots/20261113-v27',snapshot,copy_function=os.link)
for name,value in payload['helpers'].items():
 data=base64.b64decode(value['base64']);assert hashlib.sha256(data).hexdigest()==value['sha256']
 (source/name).write_bytes(data)
for name in ['paper-source.tar','previous-v26-controls.json']:os.link(old/name,root/name)
(root/'driver.py').write_bytes(base64.b64decode(payload['driver_base64']))
expected=json.loads((old/'expected.json').read_text());expected['source_checkpoint']=payload['commit']
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
 child=subprocess.Popen(['python3',str(root/'driver.py')],cwd=root,stdin=subprocess.DEVNULL,
                        stdout=stdout,stderr=stderr,start_new_session=True)
record={'pid':child.pid,'root':str(root),'source_checkpoint':payload['commit'],
 'complete_input_files':len(manifest)+1,'snapshot_manifest_sha256':expected['snapshot_manifest_sha256'],
 'old_suite_and_inputs_untouched':True,'new_code_not_same_job_restart':True}
(root/'launch.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps(record),flush=True)
'''


def main():
    assert subprocess.check_output(['git','rev-parse','HEAD'],cwd=ROOT,text=True).strip()==SOURCE
    assert not subprocess.check_output(['git','status','--porcelain'],cwd=ROOT,text=True).strip()
    OUT.mkdir(exist_ok=False)
    (OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
    helpers={}
    for name in ['replay_snapshot.py','check_snapshot_controls.py','snapshot_archives.py','snapshot_control_archives.py']:
        data=(ROOT/'reproduction/paper_results'/name).read_bytes()
        assert data==subprocess.check_output(['git','show',SOURCE+':reproduction/paper_results/'+name],cwd=ROOT)
        helpers[name]={'base64':base64.b64encode(data).decode(),'sha256':hashlib.sha256(data).hexdigest()}
    payload={'commit':SOURCE,'helpers':helpers,'driver_base64':base64.b64encode(Path('/tmp/lark-run-paper-v27-controls-mi350-v1-20261113.py').read_bytes()).decode()}
    code='import json\npayload=json.loads('+repr(json.dumps(payload))+')\n'+REMOTE
    ast.parse(code)
    (OUT/'remote-launch.py').write_text(code)
    proc=subprocess.run(['ssh','-S','/tmp/lark-glm-cuda-cohort-publication-forward-20261113.sock',
                         '-o','BatchMode=yes','mi350','python3','-'],input=code,text=True,capture_output=True,timeout=60)
    (OUT/'stdout.log').write_text(proc.stdout);(OUT/'stderr.log').write_text(proc.stderr)
    assert proc.returncode==0,proc.stderr
    (OUT/'results.json').write_text(json.dumps(json.loads(proc.stdout),indent=2)+'\n')
    (OUT/'manifest.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.iterdir()) if p.is_file()},indent=2)+'\n')
    print(proc.stdout,end='')


if __name__=='__main__':main()
