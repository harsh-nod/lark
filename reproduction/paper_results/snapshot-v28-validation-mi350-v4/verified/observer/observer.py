"""Run all frozen v28 controls outside Git on MI350 CPU under unchanged limits."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import time

BASE=Path(__file__).resolve().parent
SOURCE=BASE/'source'
OBSERVER=BASE/'observer'
VALIDATION=BASE/'validation'
SNAPSHOT=SOURCE/'reproduction/paper_results/snapshots/20261114-v28'


def sha(path):
    digest=hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda:stream.read(1024*1024),b''):
            digest.update(data)
    return digest.hexdigest()


def write(name,value):
    path=OBSERVER/(name+'.next')
    path.write_text(json.dumps(value,indent=2)+'\n')
    path.replace(OBSERVER/name)


def main():
    assert not OBSERVER.exists() and not VALIDATION.exists(), 'Observe existing job; never restart it'
    assert not any((p/'.git').exists() for p in (BASE,*BASE.parents))
    bindings=json.loads((BASE/'bundle-manifest.json').read_text())
    assert all(sha(BASE/name)==expected for name,expected in bindings.items())
    expected=json.loads((BASE/'expected.json').read_text())
    assert sha(SNAPSHOT/'manifest.json')==expected['snapshot_manifest_sha256']
    assert sha(BASE/'paper-source.tar')=='095aae393369d4e8459e5c4c46af73b83ee9765ce786f4ebb870d2cd0cdf20d2'
    assert shutil.disk_usage(BASE).free>30*1024**3
    OBSERVER.mkdir()
    (OBSERVER/'observer.py').write_bytes(Path(__file__).read_bytes())
    temporary=BASE/'temporary'
    temporary.mkdir()
    env={k:v for k,v in os.environ.items() if k not in ('PYTHONPATH','LEAN_PATH')}
    env.update(PATH='/nonexistent',PYTHONNOUSERSITE='1',TMPDIR=str(temporary))
    command=[sys.executable,str(SOURCE/'reproduction/paper_results/check_snapshot_controls.py'),
             '--snapshot',str(SNAPSHOT),'--source-archive',str(BASE/'paper-source.tar'),
             '--output',str(VALIDATION)]
    started=time.monotonic()
    timed_out=False
    with (OBSERVER/'stdout.log').open('w') as stdout,(OBSERVER/'stderr.log').open('w') as stderr:
        child=subprocess.Popen(command,cwd=SOURCE,env=env,stdout=stdout,stderr=stderr,start_new_session=True)
        while True:
            elapsed=time.monotonic()-started
            logs=sorted(VALIDATION.glob('*.log'),key=lambda p:p.stat().st_mtime)
            write('progress.json',{'pid':os.getpid(),'child_pid':child.pid,'process_group':child.pid,
                'command':command,'stage':'complete-v28-controls','seconds':elapsed,
                'completed_logs':len(logs),'latest_log':logs[-1].name if logs else None,
                'at_utc':datetime.now(timezone.utc).isoformat(),'limits':{
                'aggregate_seconds':300,'per_replay_seconds':120,'max_independent_replayers':2}})
            try:
                code=child.wait(timeout=max(0.001,min(5,300-elapsed)))
                break
            except subprocess.TimeoutExpired:
                if time.monotonic()-started<300:
                    continue
                timed_out=True
                os.killpg(child.pid,signal.SIGTERM)
                try:
                    code=child.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid,signal.SIGKILL)
                    code=child.wait(timeout=5)
                break
    result={'schema':1,'status':'complete-control-suite-passed' if code==0 and not timed_out
            else 'complete-control-suite-failed-or-hit-existing-aggregate-cap',
            'exit_code':code,'timed_out':timed_out,'seconds':time.monotonic()-started,
            'host':'mi350','CPU_only':True,'Python':sys.version.split()[0],
            'limits':{'aggregate_seconds':300,'per_replay_seconds':120,'max_independent_replayers':2},
            'source_checkpoint':expected['source_checkpoint'],
            'source_snapshot_manifest_sha256':sha(SNAPSHOT/'manifest.json'),
            'transport_manifest_sha256':sha(BASE/'bundle-manifest.json'),
            'observer_sha256':sha(Path(__file__)),
            'completed_logs':len(list(VALIDATION.glob('*.log'))),
            'input_source_sha256':{p.name:sha(p) for p in sorted((SOURCE/'reproduction/paper_results').glob('*.py'))},
            'model_calls':0,'Lean_checks':0,'GPU_trials':0,
            'original_paper_fully_reproduced':False,'source_CI_or_publication_claim':False}
    # Record actual termination before any result assertions, including a failed
    # outcome. Unexpected assertions remain failures with all raw logs retained.
    write('process-result.json',result)
    if code==0 and not timed_out:
        controls=json.loads((VALIDATION/'results.json').read_text())
        previous=json.loads((BASE/'previous-v27-controls.json').read_text())
        old={r['name']:r for r in previous['checks']}
        new={r['name']:r for r in controls['checks']}
        assert len(old)==98
        assert controls['positive_replays']==10 and controls['negative_controls']==98
        assert len(controls['checks'])==len(new)==108
        assert all(new[name]==value for name,value in old.items()), 'Keep every earlier case and outcome'
        assert [r for r in controls['checks'] if r['name'] in old] == previous['checks'], 'Keep all earlier cases in their original order'
        assert len(controls['released_completed_temporary_control_copies'])==97
        assert controls['all_control_payloads_complete_during_replay'] is True
        assert controls['source_snapshot_manifest_sha256']==result['source_snapshot_manifest_sha256']
        result.update(positive_replays=10,negative_controls=98,all_108_checks_completed=True,
                      all98_earlier_check_records_identical=True,all_control_payloads_complete_during_replay=True)
    write('results.json',result)
    write('progress.json',{'pid':os.getpid(),'child_pid':child.pid,'stage':'terminal','exit_code':code,
                          'timed_out':timed_out,'at_utc':datetime.now(timezone.utc).isoformat()})
    write('validation-files.json',{p.relative_to(VALIDATION).as_posix():sha(p)
                                  for p in sorted(VALIDATION.rglob('*')) if p.is_file()})
    write('manifest.json',{p.name:sha(p) for p in sorted(OBSERVER.iterdir())
                           if p.is_file() and p.name!='manifest.json'})
    print(json.dumps(result),flush=True)
    raise SystemExit(0 if code==0 and not timed_out else 1)


if __name__=='__main__':
    main()
