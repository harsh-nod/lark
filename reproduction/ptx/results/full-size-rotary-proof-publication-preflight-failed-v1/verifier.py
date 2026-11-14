"""Check anonymous immutable downloads and run only the trusted recorded-data reader."""

from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import time

REPO = Path('/tmp/lark-ptx-rotary-refinement-20261113')
OUT = Path('/tmp/lark-ptx-rotary-publication-v1-20261113')
BASE = '4a7616fa7a668fec2aad85c2989cf3b4b91e2764'
COMMIT = '9ffe009f5ff3a7635d6b3708efa1bf73a840b0c9'
PACKET = 'reproduction/ptx/results/full-size-rotary-proof-v1'


def write(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2) + '\n')


def sha(data):
    return hashlib.sha256(data).hexdigest()


def call(command):
    return subprocess.check_output(command, cwd=REPO, timeout=60)


def main():
    assert not OUT.exists(), 'Inspect existing output and original process; do not relaunch'
    assert call(['git', 'rev-parse', 'HEAD']).decode().strip() == COMMIT
    assert not call(['git', 'status', '--porcelain']).strip()
    remote = call(['git', 'ls-remote', 'origin', 'refs/heads/reproduction/ptx-rotary-refinement']).decode().split()
    assert remote[0] == COMMIT, 'Exact non-force source push must finish before verification'
    paths = call(['git', 'diff', '--name-only', BASE, COMMIT]).decode().splitlines()
    assert len(paths) == len(set(paths)) and all((REPO / n).is_file() for n in paths)
    for name in paths:
        p = PurePosixPath(name)
        assert not p.is_absolute() and '..' not in p.parts and str(p) == name
    OUT.mkdir()
    (OUT / 'verifier.py').write_bytes(Path(__file__).read_bytes())
    write(OUT / 'progress.json', {'status': 'anonymous-exact-source-downloads-running',
          'pid': os.getpid(), 'source_commit': COMMIT, 'files': len(paths)})
    start = time.monotonic()

    def fetch(relative):
        committed = call(['git', 'show', COMMIT + ':' + relative])
        destination = OUT / 'downloaded' / relative
        attempts = []
        for number in (1, 2, 3):
            payload = OUT / 'attempt-payloads' / relative / str(number)
            payload.parent.mkdir(parents=True, exist_ok=True)
            url = ('https://raw.githubusercontent.com/harsh-nod/lark/' + COMMIT + '/' + relative
                   + '?lark_rope_source=' + COMMIT + '&attempt=' + str(number))
            command = ['curl', '-q', '--proxy', 'socks5h://127.0.0.1:19089', '--noproxy', '',
                       '--proto', '=https', '--connect-timeout', '10', '--max-time', '60', '-fsS',
                       '--output', str(payload), '--write-out', '%{json}', url]
            proc = subprocess.run(command, capture_output=True, text=True, timeout=70)
            metadata = json.loads(proc.stdout) if proc.stdout.strip() else {}
            row = {'attempt': number, 'curl_exit_code': proc.returncode,
                   'http_status': metadata.get('http_code'), 'ssl_verify_result': metadata.get('ssl_verify_result'),
                   'stderr': proc.stderr, 'metadata': metadata}
            attempts.append(row)
            write(OUT / 'attempts' / (relative + '.json'), attempts)
            if proc.returncode == 0 and metadata.get('http_code') == 200 and metadata.get('ssl_verify_result') == 0:
                data = payload.read_bytes()
                assert data == committed, 'Anonymous bytes differ from exact committed source: ' + relative
                destination.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(payload, destination)
                return {'path': relative, 'bytes': len(data), 'sha256': sha(data), 'http_status': 200,
                        'tls_verification': True, 'authorization_header': False,
                        'matches_committed_bytes': True, 'download_attempts': attempts}
            if number < 3:
                time.sleep(2 * number)
        raise RuntimeError('Three bounded download attempts failed: ' + relative)

    with ThreadPoolExecutor(max_workers=3) as pool:
        rows = list(pool.map(fetch, paths))
    write(OUT / 'binding.json', {'source_commit': COMMIT, 'base_main': BASE, 'files': rows})
    write(OUT / 'progress.json', {'status': 'standalone-recorded-reader-running',
          'pid': os.getpid(), 'source_commit': COMMIT, 'files_downloaded': len(rows)})
    root = OUT / 'downloaded'
    assert not any((p / '.git').exists() for p in (root, *root.parents))
    script = root / 'reproduction/paper_results/ptx_rotary_evidence.py'
    command = [sys.executable, '-I', str(script), '--packet', str(root / PACKET),
               '--output', str(OUT / 'reader-results.json')]
    proc = subprocess.run(command, cwd=OUT, text=True, capture_output=True, timeout=120)
    (OUT / 'reader.stdout').write_text(proc.stdout)
    (OUT / 'reader.stderr').write_text(proc.stderr)
    assert proc.returncode == 0, 'Downloaded recorded-data reader failed; inspect retained logs'
    checked = json.loads((OUT / 'reader-results.json').read_text())
    assert checked['archive_members_checked'] == 4414 and checked['archives_checked'] == 18
    assert checked['retained_positive_Main_checks'] == 4
    assert checked['original_paper_fully_reproduced'] is checked['captured_code_executed'] is False
    result = {'schema': 1, 'status': 'anonymous-exact-source-RoPE-publication-verified',
              'source_commit': COMMIT, 'base_main': BASE, 'files_checked': len(rows),
              'bytes_checked': sum(r['bytes'] for r in rows), 'archives_checked': 18,
              'archive_members_checked': 4414, 'recorded_reader_exit_code': proc.returncode,
              'standalone_reader_outside_Git': True, 'isolated_Python': True,
              'all_TLS_verified': True, 'authorization_headers_used': False,
              'binding_sha256': sha((OUT / 'binding.json').read_bytes()),
              'verifier_sha256': sha(Path(__file__).read_bytes()),
              'at_utc': datetime.now(timezone.utc).isoformat(), 'seconds': time.monotonic() - start,
              'fresh_Lean_checks': 0, 'model_calls': 0, 'gpu_trials': 0,
              'new_registered_source_certificates': 0, 'original_paper_fully_reproduced': False}
    write(OUT / 'results.json', result)
    write(OUT / 'manifest.json', {p.name: sha(p.read_bytes()) for p in sorted(OUT.iterdir())
                                 if p.is_file() and p.name != 'manifest.json'})
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
