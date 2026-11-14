"""Freshly replay the unchanged v26/v27 artifacts with the new authored reader."""
from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time

OUT=Path('/tmp/lark-paper-v28-older-ledger-compatibility-v1-20261114')
BASE=Path('/tmp/lark-paper-v28-controls-mi350-v3-20261114')
HELPER=BASE/'source/reproduction/paper_results/replay_snapshot.py'
SNAPSHOTS=[
 ('v26','/tmp/lark-paper-v26-controls-mi350-v3-20261113/source/reproduction/paper_results/snapshots/20261113-v26',
  '251d9b381282f54cc721587bc88d78e0f344a44eaeaf03f112fb6f6556baf6ed'),
 ('v27','/tmp/lark-paper-v27-controls-mi350-v8-20261114/source/reproduction/paper_results/snapshots/20261113-v27',
  'aa23c786cf8a7c2ca059c76beddcb86dc148dc03e3d70096e0bd2f930044fea0'),
]


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    assert not OUT.exists()
    assert not Path('/proc/2303632').exists() and not Path('/proc/2303639').exists()
    assert sha(HELPER)=='cb1d815521990c5ca30092260e745fe5b02669529013316c91d075c708530336'
    OUT.mkdir();(OUT/'temporary').mkdir();shutil.copyfile(__file__,OUT/'driver.py')
    env={k:v for k,v in os.environ.items() if k not in ('PYTHONPATH','LEAN_PATH')}
    env.update(PATH='/nonexistent',PYTHONNOUSERSITE='1',TMPDIR=str(OUT/'temporary'))
    (OUT/'started.json').write_text(json.dumps({'pid':os.getpid(),'max_independent_replayers':2})+'\n')

    def check(row):
        label,path,expected=row;snapshot=Path(path)
        assert sha(snapshot/'manifest.json')==expected
        start=time.monotonic()
        completed=subprocess.run([sys.executable,str(HELPER),'--snapshot',str(snapshot),
            '--source-archive',str(BASE/'paper-source.tar')],cwd=OUT,env=env,capture_output=True,timeout=120)
        (OUT/(label+'.stdout')).write_bytes(completed.stdout)
        (OUT/(label+'.stderr')).write_bytes(completed.stderr)
        result={'snapshot':label,'snapshot_manifest_sha256':expected,'exit_code':completed.returncode,
                'seconds':time.monotonic()-start,'manifest_unchanged':sha(snapshot/'manifest.json')==expected}
        assert completed.returncode==0 and b'frozen-snapshot-replayed' in completed.stdout, result
        assert result['manifest_unchanged']
        return result

    with ThreadPoolExecutor(max_workers=2) as pool:rows=list(pool.map(check,SNAPSHOTS))
    result={'status':'both-unchanged-older-ledgers-replayed-with-new-reader','checks':rows,
        'source_checkpoint':'d3952fcadf8f12d81535ae4f592a24f51bf809cf','reader_sha256':sha(HELPER),
        'per_replay_seconds':120,'max_independent_replayers':2,'reader_success_cache_used':False,
        'scope':'Two complete positive compatibility replays, with fresh physical/logical byte checks and unchanged frozen auditors. This does not claim separate full older control suites or new paper results.',
        'fresh_Lean_checks':0,'GPU_trials':0,'model_calls':0,'original_paper_fully_reproduced':False}
    (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    (OUT/'manifest.json').write_text(json.dumps({p.name:sha(p) for p in OUT.iterdir() if p.is_file()},indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__=='__main__':main()
