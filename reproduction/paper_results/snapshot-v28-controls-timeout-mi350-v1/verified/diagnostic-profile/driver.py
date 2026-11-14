"""Profile one fresh complete positive replay after the full-suite timeout.

This diagnostic does not replace the required 108-check release gate. Every
archive and logical byte is freshly decoded and checked; no reader cache is used.
"""
import hashlib
import importlib.util
import io
import json
import os
from pathlib import Path
import pstats
import shutil
import sys
import time

BASE = Path('/tmp/lark-paper-v28-controls-mi350-v1-20261114')
OUT = Path('/tmp/lark-paper-v28-positive-profile-mi350-v1-20261114')


def main():
    assert not OUT.exists()
    OUT.mkdir()
    shutil.copyfile(__file__, OUT/'driver.py')
    (OUT/'temporary').mkdir()
    os.environ['TMPDIR'] = str(OUT/'temporary')
    os.environ['PATH'] = '/nonexistent'
    os.environ.pop('PYTHONPATH', None)
    os.environ.pop('LEAN_PATH', None)
    helper = BASE/'source/reproduction/paper_results/replay_snapshot.py'
    assert hashlib.sha256(helper.read_bytes()).hexdigest() == '7e244add0304d298ca78e920fe08cb38b6b42680f367ee6a6b7a1a8601f057cf'
    sys.path.insert(0, str(helper.parent))
    spec = importlib.util.spec_from_file_location('authored_fresh_profile_replay', helper)
    replay = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(replay)
    original = replay.subprocess.run
    (OUT/'started.json').write_text(json.dumps({'pid':os.getpid(),'scope':'fresh-complete-positive-replay-performance-diagnostic'})+'\n')

    def profiled(command, *args, **kwargs):
        assert command[:3] == [sys.executable, '-I', str(helper)]
        assert command[3] == '--_frozen-auditor'
        return original([command[0], '-I', '-m', 'cProfile', '-o', str(OUT/'auditor.prof'), *command[2:]],
                        *args, **kwargs)

    replay.subprocess.run = profiled
    started = time.monotonic()
    try:
        replay.replay(BASE/'source/reproduction/paper_results/snapshots/20261114-v28', BASE/'paper-source.tar')
    finally:
        replay.subprocess.run = original
    elapsed = time.monotonic()-started
    output = io.StringIO()
    stats = pstats.Stats(str(OUT/'auditor.prof'), stream=output)
    stats.strip_dirs().sort_stats('cumulative').print_stats(45)
    (OUT/'auditor-stats.txt').write_text(output.getvalue())
    result = {'status':'fresh-complete-positive-replay-profiled', 'seconds':elapsed,
              'source_checkpoint':'7697e926484e2ffc5106a9c80e57fec0c1006f89',
              'full108_release_gate_satisfied':False,'reader_success_cache_used':False,
              'fresh_Lean_checks':0,'GPU_trials':0,'model_calls':0,'original_paper_fully_reproduced':False}
    (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    (OUT/'manifest.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest()
        for p in OUT.iterdir() if p.is_file()},indent=2)+'\n')
    print(json.dumps(result),flush=True)


if __name__=='__main__':
    main()
