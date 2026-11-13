"""Verify anonymous immutable downloads after the exact branch push completes."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import time

ROOT = Path('/tmp/lark-ptx-pointwise-refinement-20261113')
BASE = '7712c5d46fd2bac34b3b5cb1c6dfce1442674eed'
OUT = Path('/tmp/lark-ptx-pointwise-publication-v1-20261113')
PACKETS = (
    'reproduction/ptx/results/full-size-relu-proof-v1',
)


def call(command):
    environment = os.environ.copy()
    environment['HTTPS_PROXY'] = 'socks5://127.0.0.1:19093'
    return subprocess.check_output(command, cwd=ROOT, timeout=60, env=environment)


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', required=True)
    args = parser.parse_args()
    commit = args.commit
    assert len(commit) == 40 and all(value in '0123456789abcdef' for value in commit)
    assert call(['git', 'rev-parse', 'HEAD']).decode().strip() == commit
    assert not call(['git', 'status', '--porcelain']).strip()
    remote = json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/reproduction/ptx-pointwise-refinement']))
    assert remote['object']['sha'] == commit, 'Exact branch push must finish before verification'
    assert not OUT.exists(), 'Inspect existing output/process before another check'
    paths = []
    for packet in PACKETS:
        folder = ROOT / packet
        manifest = json.loads((folder / 'manifest.json').read_text())
        assert not any(path.is_symlink() for path in folder.rglob('*'))
        assert {str(path.relative_to(folder)) for path in folder.rglob('*') if path.is_file()} == set(manifest) | {'manifest.json'}
        for name in [*manifest, 'manifest.json']:
            path = PurePosixPath(name)
            assert not path.is_absolute() and '..' not in path.parts and str(path) == name
            if name != 'manifest.json':
                assert hashlib.sha256((folder / name).read_bytes()).hexdigest() == manifest[name]
            paths.append(packet + '/' + name)
    paths += [
        'README.md', 'reproduction/ptx/README.md', 'reproduction/ptx/POINTWISE.md',
        'lark_kernels/ptx_pointwise.py', 'lark_kernels/ptx_pointwise_certificate.py',
        'lean/Lark/PtxPointwise.lean', 'pyproject.toml',
        'reproduction/ptx/check_pointwise_controls.py', 'tests/test_ptx_pointwise.py',
    ]
    assert len(paths) == len(set(paths))
    assert set(call(['git', 'diff', '--name-only', BASE, commit]).decode().splitlines()) == set(paths)
    OUT.mkdir(exist_ok=False)
    write(OUT / 'progress.json', {'status': 'exact-pushed-publication-downloads-running',
          'pid': os.getpid(), 'source_commit': commit, 'files': len(paths),
          'model_Lean_GPU_actions': 0})

    def get(relative):
        destination = OUT / 'downloaded' / relative
        destination.parent.mkdir(parents=True, exist_ok=True)
        committed = call(['git', 'show', commit + ':' + relative])
        attempts = []
        for number in (1, 2, 3):
            temporary = destination.with_name(destination.name + '.attempt-' + str(number))
            url = ('https://raw.githubusercontent.com/harsh-nod/lark/' + commit + '/' + relative
                   + '?lark_published_commit=' + commit + '&attempt=' + str(number))
            proc = subprocess.run(
                ['curl', '-q', '--proxy', 'socks5h://127.0.0.1:19093', '--noproxy', '',
                 '--proto', '=https', '--connect-timeout', '10', '--max-time', '60', '-fsS',
                 '--output', str(temporary), '--write-out', '%{json}', url],
                text=True, capture_output=True, timeout=70)
            metadata = json.loads(proc.stdout) if proc.stdout.strip() else {}
            observation = {'attempt': number, 'curl_exit_code': proc.returncode,
                           'http_status': metadata.get('http_code'),
                           'curl_ssl_verify_result': metadata.get('ssl_verify_result'),
                           'stderr': proc.stderr[:1200]}
            attempts.append(observation)
            write(destination.with_name(destination.name + '.attempts.json'), attempts)
            if proc.returncode == 0 and metadata.get('http_code') == 200 and metadata.get('ssl_verify_result') == 0:
                data = temporary.read_bytes()
                assert data == committed, 'Anonymous download differs from exact Git blob: ' + relative
                temporary.replace(destination)
                return {'path': relative, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
                        'http_status': 200, 'curl_ssl_verify_result': 0, 'tls_verification': True,
                        'authorization_header': False, 'matches_committed_bytes': True,
                        'download_attempts': attempts}
            if number < 3:
                time.sleep(2 * number)
        raise RuntimeError('Three read-only download attempts failed: ' + relative)

    with ThreadPoolExecutor(max_workers=3) as pool:
        observations = list(pool.map(get, paths))
    for packet in PACKETS:
        folder = OUT / 'downloaded' / packet
        manifest = json.loads((folder / 'manifest.json').read_text())
        assert all(hashlib.sha256((folder / name).read_bytes()).hexdigest() == value for name, value in manifest.items())
    report = {'schema': 1, 'status': 'anonymous-exact-source-full-size-PTX-ReLU-proof-publication-verified',
              'source_commit': commit, 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'downloaded_files': observations, 'total_downloaded_bytes': sum(row['bytes'] for row in observations),
              'all_downloads_match_committed_bytes': True, 'tls_verification': True, 'authorization_header': False,
              'model_calls': 0, 'gpu_trials': 0, 'fresh_lean_checks': 0, 'new_registered_certificates': 0,
              'original_paper_fully_reproduced': False,
              'scope': 'Anonymous exact-commit Git-blob and manifest checks for one independent exact-source full-size finite PTX ReLU development proof, its fresh source-only/installed-wheel rechecks, four direct Lean source-binding controls, wheel/build data and all new source/test/documentation files. Downloads check publication bytes and repeat no scientific proof/model/hardware trial. Bounded transport retries retain every observation; no scientific/model/Lean/GPU trial is repeated.'}
    write(OUT / 'results.json', report)
    print(json.dumps({'status': report['status'], 'files': len(observations),
                      'bytes': report['total_downloaded_bytes'],
                      'download_attempts': sum(len(row['download_attempts']) for row in observations)}))


if __name__ == '__main__':
    main()
