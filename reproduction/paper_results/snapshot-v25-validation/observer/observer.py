"""Run the complete new frozen ledger suite under the unchanged 300-second cap."""
from pathlib import Path
import subprocess,os,signal,time,json,datetime
ROOT=Path('/tmp/lark-paper-v25-20261113')
OUT=Path('/tmp/lark-paper-v25-controls-observer-v2-20261113')
VALIDATION=Path('/tmp/lark-paper-v25-controls-v2-20261113')

def write(name,value):
 (OUT/name).write_text(json.dumps(value,indent=2)+'\n')

def main():
 assert not OUT.exists() and not VALIDATION.exists()
 OUT.mkdir();(OUT/'observer.py').write_bytes(Path(__file__).read_bytes())
 command=['/usr/bin/python3','reproduction/paper_results/check_snapshot_controls.py','--snapshot','reproduction/paper_results/snapshots/20261113-v25','--source-archive','/tmp/lark-reproduction-paper-source.tar','--output',str(VALIDATION)]
 start=time.monotonic()
 with (OUT/'stdout.log').open('w')as stdout,(OUT/'stderr.log').open('w')as stderr:
  child=subprocess.Popen(command,cwd=ROOT,stdout=stdout,stderr=stderr,start_new_session=True)
  write('progress.json',{'pid':os.getpid(),'child_pid':child.pid,'process_group':child.pid,'command':command,'started_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'aggregate_seconds':300,'per_replay_seconds':120,'maximum_independent_replayers':2})
  timed_out=False
  try:code=child.wait(timeout=300)
  except subprocess.TimeoutExpired:
   timed_out=True;os.killpg(child.pid,signal.SIGTERM)
   try:code=child.wait(timeout=5)
   except subprocess.TimeoutExpired:
    os.killpg(child.pid,signal.SIGKILL);code=child.wait(timeout=5)
 report={'schema':1,'status':'complete-control-suite-passed'if code==0 and not timed_out else 'complete-control-suite-failed-or-hit-existing-aggregate-cap','exit_code':code,'timed_out':timed_out,'seconds':time.monotonic()-start,'limits':{'aggregate_seconds':300,'per_replay_seconds':120,'max_independent_replayers':2},'validation_output':str(VALIDATION),'model_calls':0,'Lean_checks':0,'GPU_trials':0,'original_paper_fully_reproduced':False}
 if code==0:
  result=json.loads((VALIDATION/'results.json').read_text());assert result['positive_replays']==6 and result['negative_controls']==65
  report.update(positive_replays=6,negative_controls=65)
 write('results.json',report);print(json.dumps(report),flush=True)
 raise SystemExit(0 if code==0 and not timed_out else 1)

if __name__=='__main__':main()
