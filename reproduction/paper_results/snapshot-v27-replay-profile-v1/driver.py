"""Diagnose one complete frozen replay after its real300second suite failure."""
from datetime import datetime, timezone
import cProfile
import hashlib
import io
import json
import os
from pathlib import Path
import pstats
import subprocess
import sys
import time

OUT=Path(__file__).resolve().parent
BASE=Path('/tmp/lark-paper-v27-controls-mi350-v1-20261113')
SOURCE=BASE/'source/reproduction/paper_results'
SNAPSHOT=SOURCE/'snapshots/20261113-v27'
assert not (OUT/'started.json').exists(), 'Observe original profile instead of restarting'
assert json.loads((BASE/'observer/results.json').read_text())['timed_out'] is True
sys.path.insert(0,str(SOURCE))
import replay_snapshot

actual_run=subprocess.run
commands=[]

def traced_run(command,*args,**kwargs):
    if len(command)>1 and str(command[1]).endswith('/reproduction/paper_results/audit.py'):
        profiled=[command[0],'-m','cProfile','-o',str(OUT/'auditor.prof'),*command[1:]]
        commands.append({'original':command,'profiled':profiled,'timeout_seconds':kwargs.get('timeout')})
        return actual_run(profiled,*args,**kwargs)
    return actual_run(command,*args,**kwargs)

subprocess.run=traced_run
(OUT/'started.json').write_text(json.dumps({'pid':os.getpid(),'at_utc':datetime.now(timezone.utc).isoformat(),
    'purpose':'profile-one-complete-recorded-replay-after-actual-suite-cap-failure',
    'source_snapshot_manifest_sha256':hashlib.sha256((SNAPSHOT/'manifest.json').read_bytes()).hexdigest(),
    'fresh_Lean_GPU_model_experiments':0,'not_a_completed_control_suite_claim':True},indent=2)+'\n')
started=time.monotonic()
profiler=cProfile.Profile()
code=0
try:
    profiler.runcall(replay_snapshot.replay,SNAPSHOT,BASE/'paper-source.tar')
except BaseException:
    code=1
    raise
finally:
    profiler.dump_stats(str(OUT/'replay.prof'))
    for name in ['replay','auditor']:
        if (OUT/(name+'.prof')).exists():
            report=io.StringIO()
            pstats.Stats(str(OUT/(name+'.prof')),stream=report).sort_stats('cumulative').print_stats(65)
            (OUT/(name+'-stats.txt')).write_text(report.getvalue())
    result={'status':'profile-completed' if code==0 else 'profile-failed','exit_code':code,
            'seconds':time.monotonic()-started,'commands':commands,
            'fresh_Lean_GPU_model_experiments':0,'new_control_suite_claim':False,
            'original_paper_fully_reproduced':False}
    (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result),flush=True)
