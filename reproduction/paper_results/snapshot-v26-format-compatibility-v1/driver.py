"""Check both archive paths against every real frozen v25 evidence byte."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import sys
import tempfile
import time

ROOT = Path('/tmp/lark-paper-v26-20261113')
sys.path.insert(0, str(ROOT))
from reproduction.paper_results import replay_snapshot as replay
from reproduction.paper_results import snapshot_archives as storage

OUT = Path('/tmp/lark-paper-v26-format-compat-v1-20261113')
SOURCE = ROOT / 'reproduction/paper_results/snapshots/20261113-v25'
MANUSCRIPT = Path('/tmp/lark-reproduction-paper-source.tar')
COMMIT = 'b14f5c4b68b1b2d82d6d6eebdc7af480a922a1f5'


def sha(path):
    return storage.file_digest(path)


def write(name, data):
    temporary = OUT / (name + '.next')
    temporary.write_text(json.dumps(data, indent=2) + '\n')
    temporary.replace(OUT / name)


def run(label, snapshot, started):
    assert time.monotonic() - started < 300
    command = ['/usr/bin/python3', str(ROOT / 'reproduction/paper_results/replay_snapshot.py'),
               '--snapshot', str(snapshot), '--source-archive', str(MANUSCRIPT)]
    with (OUT / (label + '.stdout')).open('w') as stdout, (OUT / (label + '.stderr')).open('w') as stderr:
        child = subprocess.Popen(command, cwd=OUT, stdout=stdout, stderr=stderr, start_new_session=True)
        write('progress.json', {'pid': os.getpid(), 'child_pid': child.pid, 'stage': label,
            'at_utc': datetime.now(timezone.utc).isoformat(), 'command': command,
            'per_replay_limit': 120, 'aggregate_limit': 300, 'max_independent_replayers': 1})
        began = time.monotonic()
        timed_out = False
        try:
            code = child.wait(timeout=min(120, 300 - (began - started)))
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(child.pid, signal.SIGTERM)
            try:
                code = child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                code = child.wait(timeout=5)
    row = {'command': command, 'exit_code': code, 'timed_out': timed_out,
           'seconds': time.monotonic() - began}
    write(label + '.json', row)
    assert code == 0 and not timed_out, 'Inspect this original run; never restart on observation loss'
    return row


def main():
    assert not OUT.exists(), 'Inspect the existing original observer instead of restarting'
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == COMMIT
    assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip()
    assert sha(SOURCE / 'manifest.json') == 'e90502aaaedfacbea8c0ded36ad8facd8adf1870c755c3b5a38de321dead572f'
    assert sha(MANUSCRIPT) == '095aae393369d4e8459e5c4c46af73b83ee9765ce786f4ebb870d2cd0cdf20d2'
    assert not any((parent / '.git').exists() for parent in (OUT, *OUT.parents))
    original_hashes = {name: sha(SOURCE / name) for name in replay.file_set(SOURCE)}
    replay.verify_manifest(SOURCE, replay.read(SOURCE / 'manifest.json'))
    OUT.mkdir()
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    started = time.monotonic()
    legacy = OUT / 'legacy-v25'
    shutil.copytree(SOURCE, legacy)
    legacy_result = run('legacy-replay', legacy, started)
    chunked = OUT / 'schema2-v25'
    chunked.mkdir()
    for name in replay.file_set(SOURCE) - {'evidence.tar.gz', 'manifest.json', 'provenance.json'}:
        target = chunked / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(SOURCE / name, target)
    expected = replay.read(SOURCE / 'evidence-manifest.json')
    write('progress.json', {'pid': os.getpid(), 'stage': 'whole-v25-corpus-version2-encoding',
                           'at_utc': datetime.now(timezone.utc).isoformat(), 'logical_files': len(expected)})
    with tempfile.TemporaryDirectory(prefix='logical-evidence-', dir=OUT) as temporary:
        unpacked = Path(temporary)
        replay.unpack(SOURCE / 'evidence.tar.gz', unpacked)
        replay.verify_manifest(unpacked, expected, exact=True)
        content = {name: (unpacked / name).read_bytes() for name in sorted(expected)}
        layout = storage.build_parts(chunked, content)
        assert {name: row['sha256'] for name, row in layout['logical_files'].items()} == expected
        assert sum(len(data) for data in content.values()) == sum(row['bytes'] for row in layout['logical_files'].values())
    replay.write(chunked / 'evidence-layout.json', layout)
    provenance = replay.read(SOURCE / 'provenance.json')
    del provenance['evidence_archive_sha256']
    provenance.update(schema=2, evidence_layout_sha256=sha(chunked / 'evidence-layout.json'))
    replay.write(chunked / 'provenance.json', provenance)
    replay.write(chunked / 'manifest.json', {name: sha(chunked / name) for name in sorted(replay.file_set(chunked))})
    chunked_result = run('schema2-replay', chunked, started)
    assert original_hashes == {name: sha(SOURCE / name) for name in replay.file_set(SOURCE)}
    seconds = time.monotonic() - started
    assert seconds < 300
    result = {'schema': 1, 'status': 'whole-real-v25-corpus-legacy-and-chunked-storage-replays-passed',
        'source_revision': COMMIT, 'seconds': seconds,
        'legacy_replay': legacy_result, 'schema2_replay': chunked_result,
        'all_frozen_logical_files': len(expected), 'all_original_evidence_files': 3623,
        'all_frozen_logical_bytes_preserved': True, 'original_v25_snapshot_unchanged': True,
        'archive_parts': [{k: row[k] for k in ('path', 'bytes', 'sha256')} for row in layout['archives']],
        'logical_manifest_sha256': sha(SOURCE / 'evidence-manifest.json'),
        'original_v25_manifest_sha256': sha(SOURCE / 'manifest.json'),
        'max_tar_entry_bytes': storage.MAX_ENTRY_BYTES,
        'per_replay_limit_seconds': 120, 'aggregate_limit_seconds': 300,
        'independent_replayers': 1, 'fresh_lean_checks': 0, 'gpu_trials': 0, 'model_calls': 0,
        'final_v26_snapshot_created': False, 'new_paper_results_reproduced': 0,
        'original_paper_fully_reproduced': False,
        'scope': 'Full real frozen v25 corpus, all3625 logical members including all3623 original '
            'evidence files and both frozen definitions, passed unchanged legacy replay and the new '
            'multi-part/chunked storage replay. Every original logical byte/hash and all original '
            'snapshot bytes remain identical. This is storage compatibility, not a final v26 ledger, '
            'new scientific experiment or evidence for BMM/Linear integration.'}
    write('results.json', result)
    write('receipt-manifest.json', {name: sha(OUT / name) for name in (
        'driver.py', 'progress.json', 'legacy-replay.stdout', 'legacy-replay.stderr', 'legacy-replay.json',
        'schema2-replay.stdout', 'schema2-replay.stderr', 'schema2-replay.json', 'results.json')})
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
