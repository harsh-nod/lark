"""Exercise the complete real-v25 corpus through the new control writer/replayer."""

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

ROOT = Path('/tmp/lark-paper-v26-20261113')
OUT = Path('/tmp/lark-paper-v26-control-storage-v1-20261113')
PROTOTYPE = Path('/tmp/lark-paper-v26-format-compat-v1-20261113/schema2-v25')
LEGACY = ROOT / 'reproduction/paper_results/snapshots/20261113-v25'
MANUSCRIPT = Path('/tmp/lark-reproduction-paper-source.tar')
COMMIT = 'a559e40ab293237b40552aa81f59b2260e6bf554'
sys.path.insert(0, str(ROOT))
from reproduction.paper_results import replay_snapshot as replay
from reproduction.paper_results.check_snapshot_controls import control_archive, mutate_gemm_evidence, rehash


def sha(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(data)
    return value.hexdigest()


def write(name, value):
    target = OUT / (name + '.next')
    target.write_text(json.dumps(value, indent=2) + '\n')
    target.replace(OUT / name)


def inventory(path):
    return {p.relative_to(path).as_posix(): sha(p) for p in sorted(path.rglob('*')) if p.is_file()}


def run(label, snapshot, gate, accepted, began):
    elapsed = time.monotonic() - began
    assert elapsed < 300
    command = ['/usr/bin/python3', str(OUT / 'bin/replay_snapshot.py'), '--snapshot', str(snapshot),
               '--source-archive', str(MANUSCRIPT)]
    environment = {k: v for k, v in os.environ.items() if k != 'PYTHONPATH'}
    environment.update(PATH='/nonexistent', PYTHONNOUSERSITE='1')
    with (OUT / (label + '.stdout')).open('w') as stdout, (OUT / (label + '.stderr')).open('w') as stderr:
        child = subprocess.Popen(command, cwd=OUT, env=environment, stdout=stdout, stderr=stderr,
                                 start_new_session=True)
        write('progress.json', {'pid': os.getpid(), 'child_pid': child.pid, 'stage': label,
            'at_utc': datetime.now(timezone.utc).isoformat(), 'command': command,
            'per_replay_limit_seconds': 120, 'aggregate_limit_seconds': 300, 'independent_replayers': 1})
        start = time.monotonic()
        timed_out = False
        try:
            code = child.wait(timeout=min(120, 300 - elapsed))
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(child.pid, signal.SIGTERM)
            try:
                code = child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                code = child.wait(timeout=5)
    log = (OUT / (label + '.stdout')).read_text() + (OUT / (label + '.stderr')).read_text()
    result = {'command': command, 'exit_code': code, 'timed_out': timed_out,
              'seconds': time.monotonic() - start, 'expected_acceptance': accepted,
              'expected_gate': gate, 'expected_gate_observed': gate in log}
    write(label + '.json', result)
    assert not timed_out and (code == 0) == accepted and gate in log, 'Inspect original failure; never restart'
    return result


def main():
    assert not OUT.exists(), 'Inspect original output/handle; do not restart'
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == COMMIT
    assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip()
    assert sha(MANUSCRIPT) == '095aae393369d4e8459e5c4c46af73b83ee9765ce786f4ebb870d2cd0cdf20d2'
    assert sha(LEGACY / 'manifest.json') == 'e90502aaaedfacbea8c0ded36ad8facd8adf1870c755c3b5a38de321dead572f'
    before_legacy, before_prototype = inventory(LEGACY), inventory(PROTOTYPE)
    assert not any((p / '.git').exists() for p in (OUT, *OUT.parents))
    OUT.mkdir()
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    (OUT / 'bin').mkdir()
    for name in ('replay_snapshot.py', 'snapshot_archives.py'):
        shutil.copyfile(ROOT / 'reproduction/paper_results' / name, OUT / 'bin' / name)
    began = time.monotonic()
    write('progress.json', {'pid': os.getpid(), 'stage': 'whole-corpus-control-cache',
                           'at_utc': datetime.now(timezone.utc).isoformat()})
    packed = control_archive(PROTOTYPE)
    cache_seconds = time.monotonic() - began
    expected = json.loads((PROTOTYPE / 'evidence-manifest.json').read_text())
    assert len(packed.entries) == len(expected) == 3625
    assert {n: hashlib.sha256(v).hexdigest() for n, v in packed.entries.items()} == expected
    outcomes, descriptions = {}, {}
    for label, gate, accepted in (
        ('positive', 'frozen-snapshot-replayed', True),
        ('rehashed-gemm-kernel-overclaim', 'PTX matrix kernel/recheck/execution counters differ', False),
        ('retained-unsafe-control', 'Unsafe evidence path', False),
    ):
        target = OUT / 'cases' / label
        shutil.copytree(PROTOTYPE, target)
        entries = packed.entries.copy()
        if label == 'rehashed-gemm-kernel-overclaim':
            mutate_gemm_evidence(entries, json.loads((target / 'targets.json').read_text()),
                                 'gemm-rechecks-counted-as-kernels')
        elif label == 'retained-unsafe-control':
            entries['../lark-control-path-must-remain-data'] = b'complete retained unsafe control payload'
        assert set(packed.entries) <= set(entries)
        layout = packed.write(target, entries)
        rehash(target, archive_changed=True)
        original_unchanged = sum(entries[n] is value for n, value in packed.entries.items())
        descriptions[label] = {
            'logical_files': len(entries), 'original_logical_files_retained': len(packed.entries),
            'original_logical_files_unchanged': original_unchanged,
            'intentional_changed_metadata_files': sorted(n for n in packed.entries
                                                       if entries[n] is not packed.entries[n]),
            'layout_sha256': sha(target / 'evidence-layout.json'),
            'logical_manifest_sha256': sha(target / 'evidence-manifest.json'),
            'snapshot_manifest_sha256': sha(target / 'manifest.json'),
            'parts': [{k: row[k] for k in ('path', 'bytes', 'sha256')} for row in layout['archives']],
        }
        if label == 'positive':
            assert original_unchanged == 3625
        elif label == 'rehashed-gemm-kernel-overclaim':
            assert original_unchanged == 3623
        else:
            assert original_unchanged == 3625 and len(entries) == 3626
        outcomes[label] = run(label, target, gate, accepted, began)
    seconds = time.monotonic() - began
    assert seconds < 300 and inventory(LEGACY) == before_legacy and inventory(PROTOTYPE) == before_prototype
    write('results.json', {'schema': 1, 'status': 'complete-real-v25-control-storage-positive-and-two-negatives-passed',
        'source_revision': COMMIT,
        'source_sha256': {name: sha(ROOT / 'reproduction/paper_results' / name) for name in (
            'replay_snapshot.py', 'snapshot_archives.py', 'snapshot_control_archives.py', 'check_snapshot_controls.py')},
        'whole_corpus_cache_seconds': cache_seconds, 'seconds': seconds, 'outcomes': outcomes,
        'cases': descriptions, 'all_original_evidence_members': 3623, 'all_original_frozen_files': 3625,
        'raw_control_snapshots_retained_locally': str(OUT / 'cases'),
        'original_v25_and_retained_schema2_prototype_byte_identical': True,
        'per_replay_limit_seconds': 120, 'aggregate_limit_seconds': 300, 'independent_replayers': 1,
        'max_tar_entry_bytes': 10000000, 'fresh_Lean_checks': 0, 'gpu_trials': 0, 'model_calls': 0,
        'v26_snapshot_created': False, 'full_v26_control_suite_run': False,
        'original_paper_fully_reproduced': False,
        'scope': 'Three actual standalone standard-library replay checks of the complete real-v25 corpus '
                 'rewritten by the new schema-two concatenated-gzip control writer. Every original '
                 'logical file is retained; only the two explicitly selected GEMM metadata files '
                 'change in that false control. The unsafe control retains all baseline bytes plus '
                 'its malicious logical member for the trusted reader to reject. No new paper result, '
                 'Lean/GPU/model experiment, final v26 ledger or full-v26 control-suite claim.'})
    write('progress.json', {'pid': os.getpid(), 'stage': 'terminal', 'exit_code': 0,
                           'at_utc': datetime.now(timezone.utc).isoformat()})
    write('manifest.json', {p.name: sha(p) for p in sorted(OUT.iterdir())
                            if p.is_file() and p.name != 'manifest.json'})
    print(json.dumps({'status': 'whole-v25-control-writer-three-replays-passed', 'seconds': seconds,
                      'output': str(OUT), 'source_revision': COMMIT}), flush=True)


if __name__ == '__main__':
    main()
