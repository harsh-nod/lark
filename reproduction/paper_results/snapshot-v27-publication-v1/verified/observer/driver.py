"""Observe one exact-source anonymous snapshot publication and full98 replay."""
from datetime import datetime,timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time
import traceback

BASE=Path(__file__).resolve().parent
VIEW=Path('/tmp/lark-paper-v27-publication-git-view-v1-20261113')
PUBLIC=Path('/tmp/lark-paper-v27-publication-mi350-v1-20261113')
DESCRIPTOR=BASE/'descriptor.json'

def sha(path):
 value=hashlib.sha256()
 with path.open('rb') as stream:
  while data:=stream.read(1024*1024):value.update(data)
 return value.hexdigest()

def write(name,value):
 temporary=BASE/(name+'.next')
 temporary.write_text(json.dumps(value,indent=2)+'\n')
 temporary.replace(BASE/name)

def stage(name,**fields):
 write('progress.json',{'pid':os.getpid(),'stage':name,'at_utc':datetime.now(timezone.utc).isoformat(),**fields})

def stop_owned_group(pid):
 try:os.killpg(pid,signal.SIGTERM)
 except ProcessLookupError:return
 time.sleep(1)
 try:os.killpg(pid,signal.SIGKILL)
 except ProcessLookupError:pass

def call(name,command,env):
 started=time.monotonic()
 with (BASE/(name+'.stdout')).open('xb') as stdout,(BASE/(name+'.stderr')).open('xb') as stderr:
  child=subprocess.Popen(command,env=env,cwd=BASE,stdout=stdout,stderr=stderr,start_new_session=True)
  while True:
   logs=list((PUBLIC/'validation').glob('*.log')) if (PUBLIC/'validation').exists() else []
   stage(name,child_pid=child.pid,process_group=child.pid,seconds=time.monotonic()-started,
         completed_control_logs=len(logs),command=command)
   try:
    code=child.wait(timeout=5)
    break
   except subprocess.TimeoutExpired:continue
 if code:stop_owned_group(child.pid)
 write(name+'.json',{'command':command,'exit_code':code,'seconds':time.monotonic()-started})
 if code:raise RuntimeError(name+' failed; retain original logs/state before any next action')
 return (BASE/(name+'.stdout')).read_text().strip()

def main():
 assert not VIEW.exists() and not PUBLIC.exists() and not (BASE/'started.json').exists(),'Inspect original publication instead of restarting'
 descriptor=json.loads(DESCRIPTOR.read_text())
 source=descriptor['source_commit']
 assert len(source)==40 and all(c in '0123456789abcdef' for c in source)
 assert len(descriptor['files'])==20 and len({r['path'] for r in descriptor['files']})==20
 assert descriptor['limits']=={'aggregate_seconds':300,'per_replay_seconds':120,'max_independent_replayers':2}
 paper=Path('/tmp/lark-paper-v27-controls-mi350-v1-20261113/paper-source.tar')
 assert sha(paper)==descriptor['manuscript_sha256']
 write('started.json',{'pid':os.getpid(),'source_commit':source,'descriptor_sha256':sha(DESCRIPTOR),'at_utc':datetime.now(timezone.utc).isoformat()})
 env=dict(os.environ,GIT_CONFIG_GLOBAL='/dev/null',GIT_CONFIG_NOSYSTEM='1',GIT_TERMINAL_PROMPT='0')
 for key in ['PYTHONPATH','LEAN_PATH']:env.pop(key,None)
 git=['git','-c','http.sslVerify=true','-c','http.proxy=','-c','credential.helper=','-c','http.extraHeader=']
 call('clone-real-Git-object-view',git+['clone','--filter=blob:none','--no-checkout','--depth=1','--single-branch',
      '--branch','reproduction/paper-v27','https://github.com/harsh-nod/lark.git',str(VIEW)],env)
 for key,value in [('http.sslVerify','true'),('http.proxy',''),('credential.helper',''),('http.extraHeader',''),
                   ('http.lowSpeedLimit','1024'),('http.lowSpeedTime','120'),('gc.auto','0')]:
  subprocess.run(['git','-C',str(VIEW),'config',key,value],env=env,check=True)
 present=subprocess.run(['git','-C',str(VIEW),'cat-file','-e',source+'^{commit}'],env=env,capture_output=True)
 if present.returncode:
  call('fetch-exact-published-commit',git+['-C',str(VIEW),'fetch','--depth=1','--filter=blob:none','origin',source],env)
 assert subprocess.check_output(['git','-C',str(VIEW),'rev-parse',source+'^{commit}'],env=env,text=True).strip()==source
 checker=VIEW/'reproduction/paper_results/check_public_snapshot.py'
 checker.parent.mkdir(parents=True,exist_ok=True)
 data=subprocess.check_output(['git','-C',str(VIEW),'show',source+':reproduction/paper_results/check_public_snapshot.py'],env=env)
 assert hashlib.sha256(data).hexdigest()==descriptor['checker_sha256']
 checker.write_bytes(data)
 ram=Path('/dev/shm')
 mem=dict(line.split(':',1) for line in Path('/proc/meminfo').read_text().splitlines())
 available=int(mem['MemAvailable'].split()[0])*1024
 ram_free=__import__('shutil').disk_usage(ram).free
 if ram_free>=4*1024**3 and available>=6*1024**3:env['TMPDIR']=str(ram)
 write('environment.json',{'TMPDIR':env.get('TMPDIR'),'RAM_free_bytes':ram_free,'memory_available_bytes':available,
                          'Git_view_is_real_Git_objects':True,'source_commit':source,'source_authentication_headers_configured':False})
 command=[sys.executable,str(checker),'--commit',source,'--snapshot','20261113-v27','--source-archive',str(paper),
          '--output',str(PUBLIC),'--proxy','']
 call('anonymous20-files-and-complete98-controls',command,env)
 report=json.loads((PUBLIC/'results.json').read_text())
 validation=json.loads((PUBLIC/'validation/results.json').read_text())
 assert report['source_commit']==source and report['snapshot']=='20261113-v27'
 assert report['authenticated_download_requests'] is False and report['tls_verification'] is True
 assert report['all_downloads_match_committed_bytes'] is True
 assert report['positive_replays']==9 and report['negative_controls']==89
 assert report['total_downloaded_bytes']==descriptor['bytes']
 expected={r['path']:r for r in descriptor['files']}
 actual=report['downloaded_files']
 assert len(actual)==len({r['path'] for r in actual})==20 and {r['path'] for r in actual}==set(expected)
 for row in actual:
  bound=expected[row['path']]
  assert row['bytes']==bound['bytes'] and row['sha256']==bound['sha256']
  assert row['http_status']==200 and row['tls_verification'] is True and row['authorization_header'] is False
 assert validation['checks']==descriptor['expected_98_check_records']
 assert len(list((PUBLIC/'validation').glob('*.log')))==98
 assert validation['source_snapshot_manifest_sha256']==descriptor['snapshot_manifest_sha256']
 result={'status':'anonymous20-file-source-exact-v27-download-and-all98-controls-passed',
         'source_commit':source,'downloaded_files':20,'downloaded_bytes':descriptor['bytes'],
         'positive_replays':9,'negative_controls':89,'all98_records_identical_to_MI350_pass':True,
         'download_TLS_verified':True,'anonymous_downloads':True,'original_paper_fully_reproduced':False,
         'descriptor_sha256':sha(DESCRIPTOR),'checker_sha256':descriptor['checker_sha256'],
         'fresh_Lean_checks':0,'model_calls':0,'GPU_trials':0,'CI_reruns':0,
         'publication_result':str(PUBLIC/'results.json')}
 write('results.json',result)
 stage('terminal-success',result=result)
 write('manifest.json',{p.name:sha(p) for p in sorted(BASE.iterdir()) if p.is_file() and p.name!='manifest.json'})
 print(json.dumps(result),flush=True)

if __name__=='__main__':
 try:main()
 except Exception:
  (BASE/'exception.txt').write_text(traceback.format_exc())
  stage('terminal-failure-inspect-original-artifacts')
  raise
