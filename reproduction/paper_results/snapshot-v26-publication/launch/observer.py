"""Record exact anonymous publication after the CI ledger job has completed."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import signal
import subprocess
import time

BASE = Path(__file__).resolve().parent
SOURCE = 'ce5611655946a0a8cca76f97beb8f85bf8f4fc2b'
VIEW = Path('/tmp/lark-paper-v26-publication-git-view-v2-20261113')
OUT = Path('/tmp/lark-paper-v26-publication-mi350-v2-20261113')
OBSERVER = BASE / 'observer'


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
    assert not OUT.exists() and not OBSERVER.exists(), 'Inspect existing publication/PID instead of restarting'
    ready = json.loads((VIEW / 'ready.json').read_text())
    assert ready['source_commit'] == SOURCE and ready['exact_Git_blobs_checked'] == 18
    root = Path(ready['source_view'])
    metadata = json.loads((VIEW / 'publication.json').read_text())
    checker = Path(ready['checker_path'])
    binding = next(r for r in metadata['files'] if r['path'].endswith('/check_public_snapshot.py'))
    assert sha(checker) == binding['sha256']
    job = json.loads((BASE / 'completed-paper-ledger-job.json').read_text())
    assert job['id'] == 132293060832 and job['run_id'] == 43544667567
    assert job['name'] == 'paper-ledger' and job['status'] == 'completed' and job['conclusion'] == 'success'
    OBSERVER.mkdir()
    (OBSERVER / 'observer.py').write_bytes(Path(__file__).read_bytes())
    command = ['/usr/bin/python3', str(checker), '--commit', SOURCE, '--snapshot', '20261113-v26',
               '--source-archive', '/tmp/lark-paper-v26-controls-mi350-v3-20261113/paper-source.tar',
               '--output', str(OUT), '--proxy', '']
    started = time.monotonic()
    timed_out = False
    with (OBSERVER / 'stdout.log').open('w') as stdout, (OBSERVER / 'stderr.log').open('w') as stderr:
        child = subprocess.Popen(command, cwd=root, stdout=stdout, stderr=stderr, start_new_session=True)
        write('progress.json', {'pid': os.getpid(), 'child_pid': child.pid, 'process_group': child.pid,
            'source_commit': SOURCE, 'stage': 'anonymous17-file-download-and-all89-controls',
            'at_utc': datetime.now(timezone.utc).isoformat(), 'command': command,
            'per_replay_seconds': 120, 'full_controls_seconds': 300, 'max_independent_replayers': 2,
            'completed_CI_ledger_job_before_start': job['id'], 'transport_and_validation_limit_seconds': 1200})
        try:
            code = child.wait(timeout=1200)
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(child.pid, signal.SIGTERM)
            try:
                code = child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                code = child.wait(timeout=5)
        if code != 0:
            # The checker's own 300-second control cap can end its direct
            # child before the child's replayers. Stop this owned group too.
            try:
                os.killpg(child.pid, signal.SIGTERM)
            except ProcessLookupError:
                pass
    result = {'schema': 1, 'status': 'anonymous-publication-terminal', 'source_commit': SOURCE,
        'exit_code': code, 'timed_out': timed_out, 'seconds': time.monotonic() - started,
        'host': 'mi350', 'CPU_only': True, 'model_calls': 0, 'GPU_trials': 0, 'Lean_checks': 0,
        'original_paper_fully_reproduced': False, 'all_source_CI_or_main_gate_claim': False,
        'completed_CI_ledger_job_before_start': job['id'], 'public_result_path': str(OUT / 'results.json'),
        'selected_Git_view_sha256': sha(VIEW / 'ready.json'), 'observer_sha256': sha(Path(__file__))}
    if code == 0 and not timed_out:
        public = json.loads((OUT / 'results.json').read_text())
        assert public['source_commit'] == SOURCE
        assert len(public['downloaded_files']) == 17 and public['total_downloaded_bytes'] == 238899106
        assert public['authenticated_download_requests'] is False and public['tls_verification'] is True
        assert public['all_downloads_match_committed_bytes'] is True
        assert public['positive_replays'] == 8 and public['negative_controls'] == 81
        assert len(public['validation']['checks']) == 89
        assert len(public['validation']['released_completed_temporary_control_copies']) == 80
        assert public['checker_sha256'] == binding['sha256']
        result.update(status='anonymous17-file-source-exact-v26-download-and-all89-controls-passed',
                      downloaded_files=17, downloaded_bytes=238899106, positive_replays=8, negative_controls=81,
                      authorization_header=False, TLS_verified=True, all_Git_bytes_match=True)
    write('results.json', result)
    write('progress.json', {'pid': os.getpid(), 'stage': 'terminal', 'exit_code': code,
                           'timed_out': timed_out, 'at_utc': datetime.now(timezone.utc).isoformat()})
    write('manifest.json', {p.name: sha(p) for p in sorted(OBSERVER.iterdir())
                            if p.is_file() and p.name != 'manifest.json'})
    print(json.dumps(result), flush=True)
    raise SystemExit(0 if code == 0 and not timed_out else 1)


if __name__ == '__main__':
    main()
