from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import subprocess

ROOT = Path('/tmp/lark-full-shape-flash-runtimes-20261113')
OUT = Path('/tmp/lark-flash-runtimes-publication-v1-20261113')
SOURCE = 'fa5260b72c648a89dc640180e774c9047da81f90'
BASE = 'reproduction/local_models/results/'
PACKETS = ('full-shape-runtime-flash-hip-v1', 'full-shape-runtime-flash-cuda-v1', 'hip-cuda-reference-identity-ci-main-v1')
OUT.mkdir(exist_ok=False)
paths = []
for name in PACKETS:
    manifest = json.loads((ROOT / BASE / name / 'manifest.json').read_text())
    for file in list(manifest) + ['manifest.json']:
        relative = PurePosixPath(file)
        assert not relative.is_absolute() and '..' not in relative.parts
        paths.append(BASE + name + '/' + file)

def get(relative):
    destination = OUT / 'downloaded' / relative
    destination.parent.mkdir(parents=True, exist_ok=True)
    url = 'https://raw.githubusercontent.com/harsh-nod/lark/' + SOURCE + '/' + relative
    command = ['curl', '-q', '--proxy', 'socks5h://127.0.0.1:19089', '--noproxy', '',
               '--proto', '=https', '--connect-timeout', '10', '--max-time', '60', '-fS',
               '--output', str(destination), '--write-out', '%{json}', url]
    result = subprocess.run(command, capture_output=True, text=True, timeout=70)
    assert result.returncode == 0, result.stderr
    metadata = json.loads(result.stdout)
    assert metadata['http_code'] == 200 and metadata['ssl_verify_result'] == 0
    committed = subprocess.check_output(['git', 'show', SOURCE + ':' + relative],
                                        cwd=ROOT, timeout=20)
    data = destination.read_bytes()
    assert data == committed
    return {'path': relative, 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
            'http_status': 200, 'curl_ssl_verify_result': 0, 'tls_verification': True,
            'authorization_header': False, 'matches_committed_bytes': True}

with ThreadPoolExecutor(max_workers=3) as pool:
    observations = list(pool.map(get, paths))
for name in PACKETS:
    root = OUT / 'downloaded' / BASE / name
    manifest = json.loads((root / 'manifest.json').read_text())
    assert all(hashlib.sha256((root / p).read_bytes()).hexdigest() == h
               for p, h in manifest.items())
report = {'schema': 1, 'status': 'anonymous-both-flash-runtimes-and-reference-main-packets-verified',
          'source_commit': SOURCE, 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
          'downloaded_files': observations,
          'total_downloaded_bytes': sum(x['bytes'] for x in observations),
          'all_downloads_match_committed_bytes': True, 'tls_verification': True,
          'authorization_header': False, 'model_calls': 0, 'gpu_trials': 0,
          'fresh_lean_checks': 0, 'new_registered_certificates': 0,
          'original_paper_fully_reproduced': False,
          'scope': 'Anonymous byte/manifest validation of both full-size Flash runtime setups and the checked nineteen-job reference identity main receipt. No model, numerical, GPU or Lean experiment rerun.'}
(OUT / 'results.json').write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({'status': report['status'], 'files': len(observations),
                  'bytes': report['total_downloaded_bytes']}))
