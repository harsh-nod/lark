"""Read bounded original-artifact endpoints over verified anonymous HTTPS."""
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path
import re
import subprocess
from urllib.parse import quote

ROOT = Path('/tmp/lark-original-artifact-refresh-20261113-1745')


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def get(item):
    label, url = item
    path = ROOT / 'raw' / (label + '.body')
    proc = subprocess.run(['curl', '-q', '--proxy', 'socks5h://127.0.0.1:19089', '--noproxy', '',
                           '--proto', '=https', '--connect-timeout', '10', '--max-time', '60',
                           '-sS', '--output', str(path), '--write-out', '%{json}', url],
                          text=True, capture_output=True, timeout=70)
    metadata = json.loads(proc.stdout) if proc.stdout.strip() else {}
    row = {'url': url, 'curl_exit_code': proc.returncode, 'http_status': metadata.get('http_code'),
           'curl_ssl_verify_result': metadata.get('ssl_verify_result'), 'authorization_header': False,
           'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'stderr': proc.stderr,
           'body_bytes': path.stat().st_size if path.exists() else 0,
           'body_sha256': hashlib.sha256(path.read_bytes()).hexdigest() if path.exists() else None}
    write(ROOT / 'packet' / (label + '-request.json'), row)
    assert proc.returncode == 0 and metadata.get('ssl_verify_result') == 0, row
    return label, row


def main():
    assert not ROOT.exists(), 'Inspect the original output/handle before another read'
    (ROOT / 'raw').mkdir(parents=True)
    packet = ROOT / 'packet'
    packet.mkdir()
    queries = [
        ('kernelcraft-metadata', 'https://api.github.com/repos/AICrossSim/KernelCraft'),
        ('kernelcraft-releases', 'https://api.github.com/repos/AICrossSim/KernelCraft/releases?per_page=100'),
        ('arxiv-repositories', 'https://api.github.com/search/repositories?q=2611.02028&per_page=20'),
        ('arxiv-abstract', 'https://arxiv.org/abs/2611.02028'),
    ]
    with ThreadPoolExecutor(max_workers=3) as pool:
        observations = dict(pool.map(get, queries))
    for label in ['kernelcraft-metadata', 'kernelcraft-releases', 'arxiv-repositories']:
        assert observations[label]['http_status'] == 200, observations[label]
        (packet / (label + '.json')).write_bytes((ROOT / 'raw' / (label + '.body')).read_bytes())
    repo = json.loads((packet / 'kernelcraft-metadata.json').read_text())
    _, ref = get(('kernelcraft-default-ref', 'https://api.github.com/repos/AICrossSim/KernelCraft/git/ref/heads/'
                  + quote(repo['default_branch'], safe='')))
    observations['kernelcraft-default-ref'] = ref
    (packet / 'kernelcraft-default-ref.json').write_bytes((ROOT / 'raw/kernelcraft-default-ref.body').read_bytes())
    html = (ROOT / 'raw/arxiv-abstract.body').read_text()
    assert observations['arxiv-abstract']['http_status'] == 200 and '2611.02028' in html and 'LARK' in html
    class Text(HTMLParser):
        def __init__(self):
            super().__init__()
            self.pieces = []
        def handle_data(self, data):
            self.pieces.append(data)
    parser = Text()
    parser.feed(html)
    versions = list(dict.fromkeys(re.findall(r'\[v([0-9]+)\]', ' '.join(parser.pieces))))
    assert versions, 'Version labels not found; raw HTML retained for inspection'
    version_observation = {'identifier': '2611.02028', 'version_labels_observed': versions,
        'raw_HTML_sha256': observations['arxiv-abstract']['body_sha256'],
        'raw_HTML_retained_outside_public_packet': True,
        'scope': 'Version labels on the captured abstract page only; the original manuscript source archive pin is unchanged.'}
    write(packet / 'manuscript-version-observation.json', version_observation)
    releases = json.loads((packet / 'kernelcraft-releases.json').read_text())
    search = json.loads((packet / 'arxiv-repositories.json').read_text())
    result = {'schema': 1, 'status': 'bounded-public-original-artifact-endpoints-refreshed',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'observations': observations,
        'kernelcraft': {k: repo[k] for k in ['full_name','html_url','size','pushed_at','updated_at','default_branch','archived']},
        'kernelcraft_public_releases_on_first_page': len(releases),
        'default_ref_status': ref['http_status'],
        'default_ref_body': json.loads((packet / 'kernelcraft-default-ref.json').read_text()),
        'arxiv_repository_search_total': search['total_count'],
        'arxiv_repository_search_items': [r['full_name'] for r in search['items']],
        'manuscript_version_labels': versions,
        'scope': 'Only these official public repository metadata/releases/default-ref endpoints, exact-ID '
                 'repository search and captured abstract-page version labels. Not a proof of global '
                 'artifact absence. No author contact, source execution, model, Lean or GPU action.',
        'model_calls': 0, 'GPU_actions': 0, 'fresh_lean_checks': 0, 'original_paper_fully_reproduced': False}
    write(packet / 'results.json', result)
    (packet / 'driver.py').write_bytes(Path(__file__).read_bytes())
    write(packet / 'manifest.json', {p.name: hashlib.sha256(p.read_bytes()).hexdigest()
                                    for p in sorted(packet.iterdir()) if p.is_file()})
    print(json.dumps({k: result[k] for k in ['status','kernelcraft','kernelcraft_public_releases_on_first_page',
            'default_ref_status','arxiv_repository_search_total','manuscript_version_labels']}))


if __name__ == '__main__':
    main()
