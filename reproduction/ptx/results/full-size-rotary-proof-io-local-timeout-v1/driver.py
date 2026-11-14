"""Validate all89 unchanged ledger outcomes under the original aggregate cap."""

from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

REPO = Path('/tmp/lark-ptx-rotary-refinement-20261113')
OUT = Path('/tmp/lark-rotary-ledger-container-reuse-v1-20261113')
PAPER = Path('/tmp/lark-reproduction-paper-source.tar')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    assert not OUT.exists(), 'Inspect existing experiment/process; do not restart'
    head = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=REPO, text=True).strip()
    assert head.startswith('898d540') and not subprocess.check_output(['git', 'status', '--porcelain'], cwd=REPO).strip()
    snapshot = REPO / 'reproduction/paper_results/snapshots/20261113-v26'
    assert sha(snapshot / 'manifest.json') == '251d9b381282f54cc721587bc88d78e0f344a44eaeaf03f112fb6f6556baf6ed'
    assert sha(PAPER) == '095aae393369d4e8459e5c4c46af73b83ee9765ce786f4ebb870d2cd0cdf20d2'
    OUT.mkdir()
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    source_names = ['reproduction/paper_results/snapshot_control_archives.py',
                    'reproduction/paper_results/check_snapshot_controls.py', 'tests/test_snapshot_control_archives.py']
    for name in source_names:
        target = OUT / 'source' / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(REPO / name, target)
    for number in (1, 2):
        for suffix in ('stdout', 'stderr'):
            shutil.copyfile(Path(f'/tmp/lark-rotary-ledger-container-tests-v{number}-20261113.{suffix}'),
                            OUT / f'unit-tests-v{number}.{suffix}')
    command = ['timeout', '--kill-after=5s', '300s', sys.executable,
               'reproduction/paper_results/check_snapshot_controls.py', '--snapshot', str(snapshot),
               '--source-archive', str(PAPER), '--output', str(OUT / 'controls')]
    write(OUT / 'progress.json', {'status': 'all89-ledger-controls-running', 'source_commit': head,
          'started_at_utc': datetime.now(timezone.utc).isoformat(), 'aggregate_cap_seconds': 300,
          'per_replay_cap_seconds': 120, 'max_replay_workers': 2})
    start = time.monotonic()
    with (OUT / 'stdout.log').open('wb') as stdout, (OUT / 'stderr.log').open('wb') as stderr:
        proc = subprocess.run(command, cwd=REPO, stdout=stdout, stderr=stderr)
    elapsed = time.monotonic() - start
    controls_path = OUT / 'controls/results.json'
    controls = json.loads(controls_path.read_text()) if controls_path.exists() else None
    passed = (proc.returncode == 0 and controls is not None and controls['positive_replays'] == 8
              and controls['negative_controls'] == 81 and len(controls['checks']) == 89
              and len(controls['released_completed_temporary_control_copies']) == 80
              and controls['all_control_payloads_complete_during_replay'] is True)
    result = {'schema': 1, 'status': 'all89-ledger-controls-passed' if passed else 'ledger-validation-failed',
              'source_commit': head, 'exit_code': proc.returncode, 'seconds': elapsed,
              'aggregate_cap_seconds': 300, 'per_replay_cap_seconds': 120, 'max_replay_workers': 2,
              'positive_replays': controls['positive_replays'] if controls else None,
              'negative_controls': controls['negative_controls'] if controls else None,
              'frozen_v26_manifest_sha256': sha(snapshot / 'manifest.json'),
              'source_sha256': {n: sha(REPO / n) for n in source_names},
              'fresh_Lean_checks': 0, 'model_calls': 0, 'gpu_trials': 0,
              'CI_reruns': 0, 'original_paper_fully_reproduced': False}
    write(OUT / 'results.json', result)
    write(OUT / 'manifest.json', {p.relative_to(OUT).as_posix(): sha(p) for p in sorted(OUT.rglob('*'))
                                 if p.is_file() and p != OUT / 'manifest.json'})
    print(json.dumps(result), flush=True)
    if not passed:
        raise SystemExit(1)


if __name__ == '__main__':
    main()
