"""Run the complete frozen v26 controls on MI350 CPU within unchanged limits."""

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

BASE = Path(__file__).resolve().parent
SOURCE = BASE / 'source'
OBSERVER = BASE / 'observer'
VALIDATION = BASE / 'validation'
SNAPSHOT = Path('/tmp/lark-paper-v26-controls-mi350-v3-20261113/source/reproduction/paper_results/snapshots/20261113-v26')


def sha(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(data)
    return value.hexdigest()


def write(name, value):
    temporary = OBSERVER / (name + '.next')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(OBSERVER / name)


def main():
    assert not OBSERVER.exists() and not VALIDATION.exists(), 'Inspect original job instead of restarting'
    assert not any((p / '.git').exists() for p in (BASE, *BASE.parents))
    manifest = json.loads((BASE / 'bundle-manifest.json').read_text())
    assert all(sha(BASE / name) == digest for name, digest in manifest.items())
    assert sha(SNAPSHOT / 'manifest.json') == '251d9b381282f54cc721587bc88d78e0f344a44eaeaf03f112fb6f6556baf6ed'
    assert sha(BASE / 'paper-source.tar') == '095aae393369d4e8459e5c4c46af73b83ee9765ce786f4ebb870d2cd0cdf20d2'
    assert shutil.disk_usage(BASE).free > 30 * 1024**3, 'Insufficient room for complete copied controls'
    OBSERVER.mkdir()
    (OBSERVER / 'observer.py').write_bytes(Path(__file__).read_bytes())
    temporary = BASE / 'temporary'
    temporary.mkdir()
    env = {k: v for k, v in os.environ.items() if k not in ('PYTHONPATH', 'LEAN_PATH')}
    env.update(PATH='/nonexistent', PYTHONNOUSERSITE='1', TMPDIR=str(temporary))
    command = [sys.executable, str(SOURCE / 'reproduction/paper_results/check_snapshot_controls.py'),
               '--snapshot', str(SNAPSHOT), '--source-archive', str(BASE / 'paper-source.tar'),
               '--output', str(VALIDATION)]
    began = time.monotonic()
    timed_out = False
    with (OBSERVER / 'stdout.log').open('w') as stdout, (OBSERVER / 'stderr.log').open('w') as stderr:
        child = subprocess.Popen(command, cwd=SOURCE, env=env, stdout=stdout, stderr=stderr,
                                 start_new_session=True)
        counter = 0
        while True:
            elapsed = time.monotonic() - began
            logs = sorted(VALIDATION.glob('*.log'), key=lambda p: p.stat().st_mtime)
            row = {'pid': os.getpid(), 'child_pid': child.pid, 'process_group': child.pid,
                   'command': command, 'at_utc': datetime.now(timezone.utc).isoformat(),
                   'seconds': elapsed, 'stage': 'complete-v26-controls', 'completed_logs': len(logs),
                   'latest_log': logs[-1].name if logs else None,
                   'aggregate_seconds': 300, 'per_replay_seconds': 120,
                   'max_independent_replayers': 2, 'host': 'mi350', 'CPU_only': True}
            write('progress.json', row)
            if counter % 6 == 0:
                print(json.dumps({k: row[k] for k in ('seconds', 'completed_logs', 'latest_log')}), flush=True)
            counter += 1
            try:
                code = child.wait(timeout=max(0.001, min(5, 300 - elapsed)))
                break
            except subprocess.TimeoutExpired:
                if time.monotonic() - began < 300:
                    continue
                timed_out = True
                os.killpg(child.pid, signal.SIGTERM)
                try:
                    code = child.wait(timeout=5)
                except subprocess.TimeoutExpired:
                    os.killpg(child.pid, signal.SIGKILL)
                    code = child.wait(timeout=5)
                break
    seconds = time.monotonic() - began
    result = {'schema': 1, 'status': 'complete-control-suite-passed' if code == 0 and not timed_out
              else 'complete-control-suite-failed-or-hit-existing-aggregate-cap',
              'exit_code': code, 'timed_out': timed_out, 'seconds': seconds, 'host': 'mi350',
              'CPU_only': True, 'Python': sys.version.split()[0], 'CPU_threads_available': os.cpu_count(),
              'limits': {'aggregate_seconds': 300, 'per_replay_seconds': 120, 'max_independent_replayers': 2},
              'source_checkpoint': '898d54045af3a60367650bb56afcf0b7b3615ba1',
              'source_snapshot_manifest_sha256': sha(SNAPSHOT / 'manifest.json'),
              'transport_manifest_sha256': sha(BASE / 'bundle-manifest.json'),
              'observer_sha256': sha(Path(__file__)), 'validation_output': str(VALIDATION),
              'input_source_sha256': {name: sha(SOURCE / 'reproduction/paper_results' / name) for name in (
                  'check_snapshot_controls.py', 'replay_snapshot.py', 'snapshot_archives.py', 'snapshot_control_archives.py')},
              'completed_logs': len(list(VALIDATION.glob('*.log'))),
              'model_calls': 0, 'Lean_checks': 0, 'GPU_trials': 0,
              'original_paper_fully_reproduced': False, 'source_CI_or_publication_claim': False}
    if code == 0 and not timed_out:
        controls = json.loads((VALIDATION / 'results.json').read_text())
        assert controls['positive_replays'] == 8 and controls['negative_controls'] == 81
        assert len(controls['checks']) == len({r['name'] for r in controls['checks']}) == 89
        assert controls['source_snapshot_manifest_sha256'] == result['source_snapshot_manifest_sha256']
        result.update(positive_replays=8, negative_controls=81, all_89_checks_completed=True)
    write('results.json', result)
    write('progress.json', {'pid': os.getpid(), 'stage': 'terminal', 'exit_code': code,
                           'timed_out': timed_out, 'at_utc': datetime.now(timezone.utc).isoformat()})
    write('validation-files.json', {p.relative_to(VALIDATION).as_posix(): sha(p)
                                    for p in sorted(VALIDATION.rglob('*')) if p.is_file()})
    write('manifest.json', {p.name: sha(p) for p in sorted(OBSERVER.iterdir())
                            if p.is_file() and p.name != 'manifest.json'})
    print(json.dumps(result), flush=True)
    raise SystemExit(0 if code == 0 and not timed_out else 1)


if __name__ == '__main__':
    main()
