"""Replay the retained complete v25 schema-two prototype with the new reader."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

ROOT = Path('/tmp/lark-paper-v26-20261113')
OUT = Path('/tmp/lark-paper-v26-stream-compat-v1-20261113')
SNAPSHOT = Path('/tmp/lark-paper-v26-format-compat-v1-20261113/schema2-v25')
LEGACY = ROOT / 'reproduction/paper_results/snapshots/20261113-v25'
MANUSCRIPT = Path('/tmp/lark-reproduction-paper-source.tar')
COMMIT = 'd2c22842ce59c3ee07f101c6cf654da6cb00c35b'


def sha(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(data)
    return value.hexdigest()


def write(name, data):
    temporary = OUT / (name + '.next')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(OUT / name)


def inventory(path):
    return {p.relative_to(path).as_posix(): sha(p) for p in sorted(path.rglob('*')) if p.is_file()}


def main():
    assert not OUT.exists(), 'Inspect original output/process; do not restart'
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == COMMIT
    assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip()
    assert sha(MANUSCRIPT) == '095aae393369d4e8459e5c4c46af73b83ee9765ce786f4ebb870d2cd0cdf20d2'
    assert sha(LEGACY / 'manifest.json') == 'e90502aaaedfacbea8c0ded36ad8facd8adf1870c755c3b5a38de321dead572f'
    expected = json.loads((SNAPSHOT / 'evidence-manifest.json').read_text())
    layout = json.loads((SNAPSHOT / 'evidence-layout.json').read_text())
    assert len(expected) == 3625
    assert {name: row['sha256'] for name, row in layout['logical_files'].items()} == expected
    assert not any((p / '.git').exists() for p in (OUT, *OUT.parents))
    legacy_before, snapshot_before = inventory(LEGACY), inventory(SNAPSHOT)
    OUT.mkdir()
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    command = ['/usr/bin/python3', str(ROOT / 'reproduction/paper_results/replay_snapshot.py'),
               '--snapshot', str(SNAPSHOT), '--source-archive', str(MANUSCRIPT)]
    started = time.monotonic()
    timed_out = False
    with (OUT / 'replay.stdout').open('w') as stdout, (OUT / 'replay.stderr').open('w') as stderr:
        child = subprocess.Popen(command, cwd=OUT, stdout=stdout, stderr=stderr, start_new_session=True)
        write('progress.json', {'pid': os.getpid(), 'child_pid': child.pid, 'stage': 'replaying',
                               'at_utc': datetime.now(timezone.utc).isoformat(), 'command': command,
                               'per_replay_limit_seconds': 120, 'aggregate_limit_seconds': 300,
                               'max_independent_replayers': 1})
        try:
            code = child.wait(timeout=120)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(child.pid, signal.SIGTERM)
            try:
                code = child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                code = child.wait(timeout=5)
    seconds = time.monotonic() - started
    row = {'schema': 1, 'status': 'replay-terminal', 'source_revision': COMMIT,
           'source_files_sha256': {name: sha(ROOT / name) for name in (
               'reproduction/paper_results/replay_snapshot.py',
               'reproduction/paper_results/snapshot_archives.py', 'tests/test_snapshot_archives.py',
               'tests/test_paper_control_archive.py')},
           'command': command, 'exit_code': code, 'timed_out': timed_out, 'seconds': seconds,
           'all_frozen_logical_files': len(expected), 'all_original_evidence_files': 3623,
           'archive_parts': [{k: part[k] for k in ('path', 'bytes', 'sha256')} for part in layout['archives']],
           'logical_manifest_sha256': sha(SNAPSHOT / 'evidence-manifest.json'),
           'prototype_manifest_sha256': sha(SNAPSHOT / 'manifest.json'),
           'original_v25_snapshot_unchanged': inventory(LEGACY) == legacy_before,
           'retained_schema2_prototype_unchanged': inventory(SNAPSHOT) == snapshot_before,
           'max_tar_entry_bytes': 10000000, 'per_replay_limit_seconds': 120,
           'aggregate_limit_seconds': 300, 'independent_replayers': 1,
           'fresh_lean_checks': 0, 'gpu_trials': 0, 'model_calls': 0,
           'final_v26_snapshot_created': False, 'new_paper_results_reproduced': 0,
           'original_paper_fully_reproduced': False,
           'scope': 'One actual complete schema-two replay of the retained real-v25 prototype '
                    'with the updated trusted concatenated-gzip reader. No regeneration of '
                    'prototype data and no repeat of the earlier legacy replay. No BMM/Linear '
                    'ledger integration or additional paper-result claim.'}
    write('results.json', row)
    write('progress.json', {'pid': os.getpid(), 'stage': 'terminal', 'exit_code': code,
                           'timed_out': timed_out, 'at_utc': datetime.now(timezone.utc).isoformat()})
    write('manifest.json', {name: sha(OUT / name) for name in (
        'driver.py', 'progress.json', 'replay.stdout', 'replay.stderr', 'results.json')})
    assert code == 0 and not timed_out, 'Inspect original failure; do not restart'
    assert row['original_v25_snapshot_unchanged'] and row['retained_schema2_prototype_unchanged']
    print(json.dumps({'status': 'complete-real-v25-schema2-streaming-replay-passed',
                      'seconds': seconds, 'logical_files': len(expected), 'source_revision': COMMIT}), flush=True)


if __name__ == '__main__':
    main()
