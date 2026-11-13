"""Continue a bounded public-artifact observation after an anonymous search rate limit."""

from datetime import datetime, timezone
import hashlib
from html.parser import HTMLParser
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

INITIAL = Path('/tmp/lark-original-artifact-refresh-20261113-bmm-publication-v1')
OUT = Path('/tmp/lark-original-artifact-observation-bmm-v1-20261113')


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def authenticated_read(label, resource):
    environment = dict(os.environ, HTTPS_PROXY='socks5://127.0.0.1:19089')
    result = subprocess.run(['gh', 'api', resource], env=environment, capture_output=True,
                            text=True, timeout=40)
    body = json.loads(result.stdout)
    status = 200 if result.returncode == 0 else int(body.get('status') or
        re.search(r'HTTP (\d+)', result.stderr).group(1))
    path = OUT / (label + '.json')
    write(path, body)
    write(OUT / (label + '-request.json'), {'url': 'https://api.github.com/' + resource,
          'HTTP_status': status, 'gh_exit_code': result.returncode,
          'authenticated_read': True, 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
          'body_bytes': path.stat().st_size, 'body_sha256': sha(path)})
    return body, status


def main():
    assert not OUT.exists()
    OUT.mkdir()
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    for label in ('kernelcraft-metadata', 'kernelcraft-releases'):
        row = json.loads((INITIAL / 'packet' / (label + '-request.json')).read_text())
        assert row['http_status'] == 200 and row['curl_ssl_verify_result'] == 0
        raw = INITIAL / 'raw' / (label + '.body')
        assert row['body_sha256'] == sha(raw)
        shutil.copyfile(raw, OUT / (label + '.json'))
        shutil.copyfile(INITIAL / 'packet' / (label + '-request.json'), OUT / (label + '-request.json'))
    limited = json.loads((INITIAL / 'packet/arxiv-repositories-request.json').read_text())
    assert limited['http_status'] == 403
    assert 'API rate limit exceeded' in (INITIAL / 'raw/arxiv-repositories.body').read_text()
    write(OUT / 'initial-anonymous-search-rate-limit.json', {
          'status': 'anonymous-search-HTTP403-rate-limit-retained-not-artifact-absence',
          'request': limited, 'raw_error_body_retained_locally': True,
          'initial_observer_exit_code': 1,
          'explanation': 'Earlier observer stopped at this actual failed request. Metadata/releases/abstract '
                         'responses are reused byte for byte; only the missing default ref and one '
                         'authenticated exact-ID search are requested here. No scientific run is repeated.'})
    repo = json.loads((OUT / 'kernelcraft-metadata.json').read_text())
    ref, ref_status = authenticated_read('kernelcraft-default-ref',
        'repos/AICrossSim/KernelCraft/git/ref/heads/' + repo['default_branch'])
    search, search_status = authenticated_read('arxiv-repositories-authenticated',
        'search/repositories?q=2611.02028&per_page=20')
    assert search_status == 200
    abstract_row = json.loads((INITIAL / 'packet/arxiv-abstract-request.json').read_text())
    abstract = INITIAL / 'raw/arxiv-abstract.body'
    assert abstract_row['http_status'] == 200 and abstract_row['body_sha256'] == sha(abstract)
    shutil.copyfile(INITIAL / 'packet/arxiv-abstract-request.json', OUT / 'arxiv-abstract-request.json')
    class Text(HTMLParser):
        def __init__(self):
            super().__init__()
            self.parts = []
        def handle_data(self, text):
            self.parts.append(text)
    parser = Text()
    parser.feed(abstract.read_text())
    versions = list(dict.fromkeys(re.findall(r'\[v([0-9]+)\]', ' '.join(parser.parts))))
    assert versions
    write(OUT / 'manuscript-version-observation.json', {'identifier': '2611.02028',
          'version_labels_observed': versions, 'raw_HTML_sha256': sha(abstract),
          'raw_HTML_retained_locally': True, 'original_v1_archive_pin_unchanged': True})
    result = {'schema': 1, 'status': 'bounded-original-artifact-observation-completed-with-rate-limit-fallback',
          'checked_at_utc': datetime.now(timezone.utc).isoformat(),
          'kernelcraft': {k: repo[k] for k in ('full_name', 'html_url', 'size', 'pushed_at', 'updated_at', 'default_branch')},
          'kernelcraft_public_releases_on_first_page': len(json.loads((OUT / 'kernelcraft-releases.json').read_text())),
          'default_ref_status': ref_status, 'default_ref_body': ref,
          'exact_ID_repository_search_total': search['total_count'],
          'exact_ID_repository_search_items': [row['full_name'] for row in search['items']],
          'manuscript_version_labels': versions, 'initial_anonymous_search_rate_limit_retained': True,
          'authenticated_read_only_fallback_used': True,
          'scope': 'Only the named public repository metadata/releases/default ref, exact-ID repository '
                   'search and captured abstract-page version labels. The failed anonymous search is '
                   'retained and not interpreted as absence. No proof of global artifact absence, '
                   'author contact, source execution, model, Lean or GPU action.',
          'model_calls': 0, 'GPU_actions': 0, 'fresh_lean_checks': 0,
          'original_paper_fully_reproduced': False}
    write(OUT / 'results.json', result)
    write(OUT / 'manifest.json', {p.name: sha(p) for p in sorted(OUT.iterdir()) if p.is_file()})
    print(json.dumps(result), flush=True)


if __name__ == '__main__':
    main()
