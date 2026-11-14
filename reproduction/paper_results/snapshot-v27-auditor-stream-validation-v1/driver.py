"""Retain actual completed checks before testing the changed replay source."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

ROOT = Path('/tmp/lark-paper-v27-20261113')
BASE = ROOT / 'reproduction/paper_results'
OUT = BASE / 'snapshot-v27-auditor-stream-validation-v1'


def sha(path):
    digest = hashlib.sha256()
    with path.open('rb') as stream:
        while data := stream.read(1024 * 1024):
            digest.update(data)
    return digest.hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def manifest(root, name='complete-retained-manifest.json'):
    write(root / name, {p.relative_to(root).as_posix(): sha(p)
                       for p in sorted(root.rglob('*')) if p.is_file()
                       and p != root / name})


def collect_runtime(label, original):
    target = OUT / label
    target.mkdir()
    inventory = {p.relative_to(original).as_posix(): {'bytes': p.stat().st_size, 'sha256': sha(p)}
                 for p in sorted(original.rglob('*')) if p.is_file()}
    # Immutable full inputs remain in the original directory and public snapshot.
    # Copy every diagnostic plus the exact helpers; record all input bytes too.
    for name in inventory:
        if name.startswith('isolated/') and not name.startswith('isolated/bin/'):
            continue
        path = target / name
        path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(original / name, path)
    write(target / 'complete-original-inventory.json', {
        'original_directory_retained_in_full': str(original), 'files': inventory,
        'immutable_input_copies_retained_in_original_and_public_snapshots': True,
    })


def main():
    assert not OUT.exists()
    assert sha(BASE / 'replay_snapshot.py') == '0042d77512529bd4a6734903d8422ef04de6bcc415235cbb472c78c6fceb5cc8'
    for version, expected in [
        ('20261113-v26', '251d9b381282f54cc721587bc88d78e0f344a44eaeaf03f112fb6f6556baf6ed'),
        ('20261113-v27', 'aa23c786cf8a7c2ca059c76beddcb86dc148dc03e3d70096e0bd2f930044fea0'),
    ]:
        assert sha(BASE / 'snapshots' / version / 'manifest.json') == expected
    assert not subprocess.check_output(
        ['git', 'diff', 'HEAD', '--', '.github/workflows/ci.yml',
         'reproduction/paper_results/snapshots'], cwd=ROOT)
    OUT.mkdir()
    shutil.copy2(__file__, OUT / 'driver.py')
    guards = OUT / 'guards'
    guards.mkdir()
    for extension in ['stdout', 'stderr']:
        shutil.copy2(Path('/tmp') / ('lark-v27-auditor-stream-guards-v1-20261114.' + extension),
                     guards / ('unittest.' + extension))
    assert 'Ran 6 tests in 0.383s\n\nOK' in (guards / 'unittest.stderr').read_text()
    shutil.copy2(ROOT / 'tests/test_snapshot_auditor_streams.py', guards / 'test_snapshot_auditor_streams.py')
    shutil.copy2(BASE / 'replay_snapshot.py', OUT / 'replay-after.py')
    (OUT / 'replay-before.py').write_bytes(subprocess.check_output(
        ['git', 'show', 'HEAD:reproduction/paper_results/replay_snapshot.py'], cwd=ROOT))
    collect_runtime('compatibility', Path('/tmp/lark-v27-auditor-buffer-compat-v1-20261114'))
    collect_runtime('profile', Path('/tmp/lark-v27-auditor-buffer-profile-v1-20261114'))
    comparison = json.loads((OUT / 'profile/algorithmic-comparison.json').read_text())
    assert comparison['counters']['tar_member_reads'] == {'before': '13962', 'after': '13962'}
    assert comparison['counters']['sha256'] == {'before': '27738', 'after': '27739'}
    write(OUT / 'results.json', {
        'status': 'targeted-guards-two-legacy-full-replays-and-complete-v27-profile-passed',
        'stream_buffer_bytes': 1048576, 'guard_tests': 6,
        'frozen_auditor_bytes_unchanged_and_rehashed_in_child': True,
        'full_payload_hash_member_semantic_checks_retained': True,
        'success_or_decompression_cache': False, 'comparative_timing_claim': False,
        'limits': {'per_replay_seconds': 120, 'complete_controls_seconds': 300,
                   'max_independent_replayers': 2},
        'new_full98_suite_not_yet_run': True, 'new_source_CI_not_yet_run': True,
        'fresh_Lean_checks': 0, 'GPU_trials': 0, 'model_calls': 0,
        'original_paper_fully_reproduced': False,
    })
    manifest(OUT)
    for version in [6, 7, 8]:
        source = Path(f'/tmp/lark-paper-v27-source-ci-v{version}-20261114')
        target = BASE / f'snapshot-v27-source-ci-failed-v{version}'
        assert not target.exists()
        record = json.loads((source / 'results.json').read_text())
        assert record['status'] == 'exact-source-CI-terminal-non-success'
        shutil.copytree(source, target)
        manifest(target)
    for label, source_name in [
        ('snapshot-v27-paper-ci-timeout-v8', '/tmp/lark-paper-v27-source-ci-ledger-failed-v8-20261114'),
        ('snapshot-v27-source-ci-split-failed-v7', '/tmp/lark-paper-v27-source-ci-split-failed-v7-20261114'),
        ('snapshot-v27-publication-v5', '/tmp/lark-v27-anonymous-publication-return-v5-20261114'),
    ]:
        target = BASE / label
        assert not target.exists()
        shutil.copytree(source_name, target)
        manifest(target)
    print(json.dumps({'status': 'all-completed-evidence-packaged',
                      'runtime': str(OUT), 'old_or_frozen_evidence_changed': False}))


if __name__ == '__main__':
    main()
