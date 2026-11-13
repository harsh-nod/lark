"""Verify anonymous immutable downloads after the exact branch push completes."""
import argparse
from concurrent.futures import ThreadPoolExecutor
from datetime import datetime, timezone
import hashlib
import io
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import time
import tarfile
import zipfile

ROOT = Path('/tmp/lark-ptx-matrix-refinement-20261113')
BASE = 'ae61a113489f1eb9b946f877028c6edb7796dced'
OUT = Path('/tmp/lark-ptx-matrix-publication-v2-20261113')
PACKETS = (
    'reproduction/ptx/results/full-size-gemm-proof-v1',
    'reproduction/paper_results/snapshot-v24-ci-main-v1',
    'reproduction/ptx/results/full-size-gemm-proof-publication-v1',
    'reproduction/ptx/results/full-size-gemm-proof-ci-failed-v1',
    'reproduction/ptx/results/full-size-gemm-proof-ci-failure-log-v1',
)


def call(command):
    environment = os.environ.copy()
    environment['HTTPS_PROXY'] = 'socks5://127.0.0.1:19089'
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
    remote = json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/reproduction/ptx-matrix-refinement']))
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
    packet_paths = set(paths)
    paths = call(['git', 'diff', '--name-only', BASE, commit]).decode().splitlines()
    assert packet_paths <= set(paths), 'Every packet member must be a published change'
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
                ['curl', '-q', '--proxy', 'socks5h://127.0.0.1:19089', '--noproxy', '',
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
    # Validate all five publicly downloaded archives without executing captured code.
    packet = OUT / 'downloaded' / PACKETS[0]
    summary = json.loads((packet / 'results.json').read_text())
    assert summary['independent_source_bound_development_proofs'] == 1
    assert summary['retained_positive_Main_checks'] == 4 and summary['positive_rechecks'] == 3
    assert summary['owned_module_builds_across_four_checks'] == 20
    assert summary['direct_Lean_negative_controls'] == 4 and summary['negative_timeouts'] == 0
    assert summary['original_paper_fully_reproduced'] is summary['nvidia_execution'] is False
    bundles = {}
    archive_members = 0
    for label, expected in summary['archives'].items():
        archive = packet / (label + '.tar.gz')
        inventory = packet / (label + '-files.json')
        assert hashlib.sha256(archive.read_bytes()).hexdigest() == expected['archive_sha256']
        assert hashlib.sha256(inventory.read_bytes()).hexdigest() == expected['inventory_sha256']
        files = json.loads(inventory.read_text())
        with tarfile.open(archive) as data:
            members = data.getmembers()
            assert len(members) == len(files) == expected['files']
            assert len({m.name for m in members}) == len(members) and {m.name for m in members} == set(files)
            assert all(m.isfile() and not PurePosixPath(m.name).is_absolute()
                       and '..' not in PurePosixPath(m.name).parts
                       and str(PurePosixPath(m.name)) == m.name for m in members)
            bundle = {m.name: data.extractfile(m).read() for m in members}
        assert {n: hashlib.sha256(b).hexdigest() for n, b in bundle.items()} == files
        bundles[label] = bundle
        archive_members += len(files)
    positives = [(bundles['export'], ''), (bundles['replay'], ''),
                 (bundles['controls'], 'positive-source-only-replay/'),
                 (bundles['installed-wheel'], 'source-only-replay/')]
    for bundle, prefix in positives:
        report = json.loads(bundle[prefix + 'results.json'])
        assert report['status'] == 'verified-source-bound-full-PTX-GEMM'
        assert report['source_bound_proof_accepted'] is True and report['owned_Lean_modules_freshly_compiled'] == 5
        assert report['old_owned_olean_cache_used'] is False
        assert report['shapes'] == [[64,256],[256,512],[64,512]]
        assert report['launch'] == {'grid':32768,'block':1,'warp':32}
        assert report['unchanged_CUDA_contract_fuel'] == [1030,1,1,1] and report['PTX_instructions'] == 171
        assert report['main_sha256'] == summary['main_sha256'] == hashlib.sha256(bundle[prefix+'Main.lean']).hexdigest()
        assert len(report['axiom_audits']) == 6 and len(report['library_axiom_audits']) == 169
        assert all(set(values) <= {'propext','Classical.choice','Quot.sound'}
                   for values in [*report['axiom_audits'].values(), *report['library_axiom_audits'].values()])
        assert all(row['exit_code'] == 0 and row['timed_out'] is False
                   for row in [*report['module_checks'], report['main_check']])
    control_bundle = bundles['controls']
    control_report = json.loads(control_bundle['results.json'])
    negatives = control_report['negative_controls']
    assert len(negatives) == 4 and {r['control'] for r in negatives} == {
        'wrong-product', 'wrong-loop-counter-stride', 'wrong-B-pointer-stride', 'conflicting-output-address'}
    assert control_report['timeouts'] == 0 and control_report['owned_modules_freshly_compiled'] == 5
    for row in negatives:
        prefix = row['control'] + '/'
        assert row['reader_accepted'] is row['all_shapes_dtypes_geometry_and_CUDA_fuel_unchanged'] is True
        assert row['channel'] == 'source-program-equality-proof-refused'
        assert row['Lean']['exit_code'] != 0 and row['Lean']['timed_out'] is False
        assert hashlib.sha256(control_bundle[prefix+'kernel.ptx']).hexdigest() == row['source_sha256']
        assert hashlib.sha256(control_bundle[prefix+'Main.lean']).hexdigest() == row['main_sha256']
        assert hashlib.sha256(control_bundle[prefix+'Main.log']).hexdigest() == row['Lean']['log_sha256']
        log = control_bundle[prefix+'Main.log'].decode()
        assert "tactic 'decide' proved that" in log and 'is false' in log
        assert not any(marker in log for marker in ('maximum recursion','maximum number of heartbeats','Stack overflow'))
    export = bundles['export']
    bindings = json.loads(export['source-bindings.json'])
    with zipfile.ZipFile(io.BytesIO(bundles['wheel-build']['lark_kernels-0.2.0-py3-none-any.whl'])) as wheel:
        assert hashlib.sha256(bundles['wheel-build']['lark_kernels-0.2.0-py3-none-any.whl']).hexdigest() == summary['wheel_sha256']
        for name, digest in bindings.items():
            path = 'lark_kernels/' + name[7:] if name.startswith('python/') else name
            committed = call(['git','show',commit+':'+path])
            assert hashlib.sha256(committed).hexdigest() == digest
            assert export['owned-sources/'+name] == committed
            if name.startswith('python/'):
                member = 'lark_kernels/' + name[7:]
            else:
                matches = [n for n in wheel.namelist() if n.endswith('/share/lark/'+name)]
                assert len(matches) == 1
                member = matches[0]
            assert wheel.read(member) == committed
    report = {'schema': 1, 'status': 'anonymous-exact-source-full-size-PTX-GEMM-proof-publication-verified',
              'archive_members_checked': archive_members, 'owned_source_bindings_checked': len(bindings),
              'archives_checked': len(bundles), 'source_commit': commit, 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'downloaded_files': observations, 'total_downloaded_bytes': sum(row['bytes'] for row in observations),
              'all_downloads_match_committed_bytes': True, 'tls_verification': True, 'authorization_header': False,
              'model_calls': 0, 'gpu_trials': 0, 'fresh_lean_checks': 0, 'new_registered_certificates': 0,
              'original_paper_fully_reproduced': False,
              'prior_failed_source_CI_runs_retained': 1,
              'scope': 'Anonymous exact-commit Git-blob and manifest checks for one independent exact-source full-size complete PTX GEMM development proof, its fresh source-only/installed-wheel rechecks, four direct Lean source-binding controls, wheel/build data and all new source/test/documentation files, the initial valid publication receipt and preserved failed initial CI/failure analysis. Full-size inputs now live outside the four bounded fixtures; all55trusted SDK/Lean sources and all input bytes are unchanged. Downloads check publication bytes and repeat no scientific proof/model/hardware trial. Bounded transport retries retain every observation; no scientific/model/Lean/GPU trial is repeated.'}
    write(OUT / 'results.json', report)
    print(json.dumps({'status': report['status'], 'files': len(observations),
                      'bytes': report['total_downloaded_bytes'],
                      'download_attempts': sum(len(row['download_attempts']) for row in observations)}))


if __name__ == '__main__':
    main()
