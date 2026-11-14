"""Record the first complete five-PTX-proof frozen-ledger build without experiments."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import time

ROOT = Path('/tmp/lark-paper-v26-20261113')
OUT = Path('/tmp/lark-paper-v26-build-v1-20261113')
SNAPSHOT = ROOT / 'reproduction/paper_results/snapshots/20261113-v26'
BASELINE = ROOT / 'reproduction/paper_results/snapshots/20261113-v25'
MANUSCRIPT = Path('/tmp/lark-reproduction-paper-source.tar')
COMMIT = '784634ae3902539280c28e2ca2803a46d8fc918a'
sys.path.insert(0, str(ROOT))
from reproduction.paper_results import replay_snapshot as replay
from reproduction.paper_results import snapshot_archives as storage


def sha(path):
    value = hashlib.sha256()
    with path.open('rb') as source:
        for data in iter(lambda: source.read(1024 * 1024), b''):
            value.update(data)
    return value.hexdigest()


def write(name, value):
    temporary = OUT / (name + '.next')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(OUT / name)


def baseline_inventory():
    return {name: sha(BASELINE / name) for name in replay.file_set(BASELINE)}


def main():
    assert not OUT.exists() and not SNAPSHOT.exists(), 'Inspect original build/handle instead of restarting'
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == COMMIT
    assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip()
    assert sha(MANUSCRIPT) == '095aae393369d4e8459e5c4c46af73b83ee9765ce786f4ebb870d2cd0cdf20d2'
    assert sha(BASELINE / 'manifest.json') == 'e90502aaaedfacbea8c0ded36ad8facd8adf1870c755c3b5a38de321dead572f'
    before = baseline_inventory()
    OUT.mkdir()
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    command = ['/usr/bin/python3', str(ROOT / 'reproduction/paper_results/prepare_ptx_extended_snapshot.py'),
               '--evidence-commit', COMMIT, '--source-archive', str(MANUSCRIPT), '--snapshot', str(SNAPSHOT)]
    began = time.monotonic()
    timed_out = False
    with (OUT / 'build.stdout').open('w') as stdout, (OUT / 'build.stderr').open('w') as stderr:
        child = subprocess.Popen(command, cwd=ROOT, stdout=stdout, stderr=stderr, start_new_session=True)
        write('progress.json', {'pid': os.getpid(), 'child_pid': child.pid, 'stage': 'first-v26-build',
            'at_utc': datetime.now(timezone.utc).isoformat(), 'command': command, 'builder_limit_seconds': 600})
        try:
            code = child.wait(timeout=600)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(child.pid, signal.SIGTERM)
            try:
                code = child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                code = child.wait(timeout=5)
    record = {'schema': 1, 'status': 'build-terminal', 'source_revision': COMMIT, 'command': command,
              'exit_code': code, 'timed_out': timed_out, 'seconds': time.monotonic() - began,
              'builder_limit_seconds': 600, 'fresh_Lean_checks': 0, 'gpu_trials': 0, 'model_calls': 0,
              'original_paper_fully_reproduced': False, 'full_v26_control_suite_run': False,
              'original_v25_snapshot_unchanged': before == baseline_inventory()}
    write('results.json', record)
    write('progress.json', {'pid': os.getpid(), 'stage': 'terminal', 'exit_code': code,
                           'timed_out': timed_out, 'at_utc': datetime.now(timezone.utc).isoformat()})
    assert code == 0 and not timed_out, 'Inspect this actual failure; do not restart on observation loss'
    manifest = replay.read(SNAPSHOT / 'manifest.json')
    replay.verify_manifest(SNAPSHOT, manifest)
    assert replay.file_set(SNAPSHOT) == set(manifest) | {'manifest.json'}
    layout = storage.validate_layout(replay.read(SNAPSHOT / 'evidence-layout.json'),
                                     replay.read(SNAPSHOT / 'evidence-manifest.json'))
    original = replay.read(BASELINE / 'evidence-manifest.json')
    definitions = {'reproduction/paper_results/audit.py', 'reproduction/paper_results/targets.json'}
    assert len(original) == 3625 and sum(n not in definitions for n in original) == 3623
    assert all(layout['logical_files'][n]['sha256'] == value for n, value in original.items() if n not in definitions)
    report = replay.read(SNAPSHOT / 'results/audit.json')
    assert report['counts'] == {'tables': 17, 'outer_figure_groups': 7, 'narrative_anchors': 16}
    assert report['original_paper_fully_reproduced'] is False and report['completion_percentage'] is None
    assert report['ptx_batched_evidence_checks']['retained_positive_Main_checks'] == 5
    assert report['ptx_linear_evidence_checks']['retained_positive_Main_checks'] == 4
    assert record['original_v25_snapshot_unchanged']
    record.update(status='five-PTX-development-proof-schema2-ledger-built',
        snapshot=str(SNAPSHOT), snapshot_manifest_sha256=sha(SNAPSHOT / 'manifest.json'),
        logical_manifest_sha256=sha(SNAPSHOT / 'evidence-manifest.json'),
        layout_sha256=sha(SNAPSHOT / 'evidence-layout.json'),
        evidence_files=len(report['evidence_sha256']), frozen_files=len(layout['logical_files']),
        original_evidence_files_preserved=3623, both_old_frozen_definitions_retained=True,
        logical_bytes=sum(row['bytes'] for row in layout['logical_files'].values()),
        archive_parts=[{k: row[k] for k in ('path', 'bytes', 'sha256')} for row in layout['archives']],
        counts=report['counts'], independent_PTX_development_kernels=5,
        official_positive_Main_recordings={'BMM': 5, 'Linear': 4},
        source_files_sha256={name: sha(ROOT / 'reproduction/paper_results' / name) for name in (
            'prepare_ptx_extended_snapshot.py', 'ptx_extended_evidence.py', 'ptx_extended_protocols.json',
            'replay_snapshot.py', 'snapshot_archives.py', 'check_snapshot_controls.py', 'snapshot_control_archives.py')},
        scope='Frozen recorded evidence assembled without a new scientific experiment. All earlier '
              '3623 evidence paths and hashes, both old definitions, complete BMM/Linear proofs, '
              'failed histories, publication/source CI/main receipts and all six adapted model cohorts '
              'are retained. The complete new control suite, publication and new source CI/main gates '
              'remain separate requirements; the original paper is not fully reproduced.')
    write('results.json', record)
    write('manifest.json', {p.name: sha(p) for p in sorted(OUT.iterdir())
                            if p.is_file() and p.name != 'manifest.json'})
    print(json.dumps({'status': record['status'], 'evidence_files': record['evidence_files'],
                      'frozen_files': record['frozen_files'], 'seconds': record['seconds'],
                      'parts': len(record['archive_parts']), 'output': str(OUT)}), flush=True)


if __name__ == '__main__':
    main()
