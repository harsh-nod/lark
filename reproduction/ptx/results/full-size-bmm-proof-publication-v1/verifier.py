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

ROOT = Path('/tmp/lark-ptx-batched-refinement-20261113')
BASE = 'f1dd8c2751e1b4f79c55d7e90c6b8466d8c691d8'
OUT = Path('/tmp/lark-ptx-batched-publication-v1-20261113')
PACKETS = (
    'reproduction/ptx/results/full-size-bmm-proof-v1',
    'reproduction/paper_results/snapshot-v25-ci-main-v1',
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
    remote = json.loads(call(['gh', 'api', 'repos/harsh-nod/lark/git/ref/heads/reproduction/ptx-batched-refinement']))
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
    # Validate all nine publicly downloaded archives without executing captured code.
    packet = OUT / 'downloaded' / PACKETS[0]
    summary = json.loads((packet / 'results.json').read_text())
    assert summary['independent_source_bound_development_proofs'] == 1
    assert summary['retained_positive_Main_checks'] == 5 and summary['positive_rechecks'] == 4
    assert summary['current_SDK_positive_Main_checks'] == 4 and summary['initial_SDK_positive_Main_checks'] == 1
    assert summary['owned_module_builds_across_four_current_checks'] == 32
    assert summary['owned_module_builds_across_five_successful_official_checks'] == 40
    assert summary['retained_failed_official_exports'] == 1
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
        assert report['status'] == 'verified-source-bound-full-PTX-BMM'
        assert report['source_bound_proof_accepted'] is True and report['owned_Lean_modules_freshly_compiled'] == 8
        assert report['old_owned_olean_cache_used'] is False
        assert report['shapes'] == [[32,64,256],[32,256,512],[32,64,512]]
        assert report['launch'] == {'grid':1048576,'block':1,'warp':32}
        assert report['unchanged_CUDA_contract_fuel'] == [1030,1,1,1] and report['PTX_instructions'] == 138
        assert report['main_sha256'] == summary['main_sha256'] == hashlib.sha256(bundle[prefix+'Main.lean']).hexdigest()
        assert len(report['axiom_audits']) == 6 and len(report['library_axiom_audits']) == 271
        assert all(set(values) <= {'propext','Classical.choice','Quot.sound'}
                   for values in [*report['axiom_audits'].values(), *report['library_axiom_audits'].values()])
        assert all(row['exit_code'] == 0 and row['timed_out'] is False
                   for row in [*report['module_checks'], report['main_check']])
    control_bundle = bundles['controls']
    control_report = json.loads(control_bundle['results.json'])
    negatives = control_report['negative_controls']
    assert len(negatives) == 4 and {r['control'] for r in negatives} == {
        'wrong-product', 'wrong-loop-counter-stride', 'wrong-B-pointer-stride', 'shifted-output-address'}
    assert control_report['timeouts'] == 0 and control_report['owned_modules_freshly_compiled'] == 8
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
    assert len(bundles) == 9
    failed = json.loads(bundles['failed-export-v2']['results.json'])
    assert failed['source_bound_proof_accepted'] is False and failed['source_bound_development_proofs'] == 0
    assert failed['status'] == 'unproved-source-bound-PTX-BMM'
    assert failed['owned_Lean_modules_freshly_compiled'] == 8
    assert failed['main_check']['exit_code'] == 1 and failed['main_check']['timed_out'] is False
    assert 'maximum recursion depth' in bundles['failed-export-v2']['Main.log'].decode()
    assert failed['limits'] == {'maxRecDepth':10000,'maxHeartbeats':2000000,
      'per_Lean_process_seconds':180,'source_import_build_seconds':600}
    initial_bundle = bundles['initial-export-v1']
    initial = json.loads(initial_bundle['results.json'])
    assert initial['status'] == 'verified-source-bound-full-PTX-BMM' and initial['source_bound_proof_accepted'] is True
    assert initial['owned_Lean_modules_freshly_compiled'] == 8 and initial['old_owned_olean_cache_used'] is False
    assert initial['input_bindings'] == summary['input_bindings']
    assert initial['main_sha256'] == hashlib.sha256(initial_bundle['Main.lean']).hexdigest()
    assert len(initial['axiom_audits']) == 6 and len(initial['library_axiom_audits']) == 271
    assert all(set(v)<={'propext','Classical.choice','Quot.sound'} for v in
      [*initial['axiom_audits'].values(),*initial['library_axiom_audits'].values()])
    initial_bindings = json.loads(initial_bundle['source-bindings.json'])
    assert len(initial_bindings) == 60
    for name,digest in initial_bindings.items():
        path = 'lark_kernels/'+name[7:] if name.startswith('python/') else name
        trusted = call(['git','show','65928f01c164802ee11322f5cd863b6356778641:'+path])
        assert hashlib.sha256(trusted).hexdigest()==digest
        assert initial_bundle['owned-sources/'+name]==trusted
    test_report=json.loads(bundles['sdk-tests']['results.json'])
    assert test_report['exit_code']==0 and test_report['timed_out'] is False
    assert test_report['status']=='BMM-SDK-complete-proof-replay-adversarial-test-passed'
    test_source=(packet/'sdk-test-source.py').read_bytes()
    assert hashlib.sha256(test_source).hexdigest()==test_report['test_source_sha256']
    assert test_source==call(['git','show',commit+':tests/test_ptx_batched.py'])
    installed=json.loads(bundles['installed-wheel']['results.json'])
    assert installed['status']=='installed-wheel-source-only-PTX-BMM-replay-passed'
    assert installed['isolated_mode'] is True and installed['checkout_imported'] is False
    assert installed['git_on_PATH'] is installed['network_during_install_and_replay'] is False
    assert installed['all60_owned_source_bindings_match'] is True
    assert installed['initial_BMM_renderer_source_change_refused_before_output'] is True
    export = bundles['export']
    bindings = json.loads(export['source-bindings.json'])
    with zipfile.ZipFile(io.BytesIO(bundles['wheel-build']['lark_kernels-0.3.0-py3-none-any.whl'])) as wheel:
        assert hashlib.sha256(bundles['wheel-build']['lark_kernels-0.3.0-py3-none-any.whl']).hexdigest() == summary['wheel_sha256']
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
    report = {'schema': 1, 'status': 'anonymous-exact-source-full-size-PTX-BMM-proof-publication-verified',
              'archive_members_checked': archive_members, 'owned_source_bindings_checked': len(bindings),
              'archives_checked': len(bundles), 'source_commit': commit, 'checked_at_utc': datetime.now(timezone.utc).isoformat(),
              'downloaded_files': observations, 'total_downloaded_bytes': sum(row['bytes'] for row in observations),
              'all_downloads_match_committed_bytes': True, 'tls_verification': True, 'authorization_header': False,
              'model_calls': 0, 'gpu_trials': 0, 'fresh_lean_checks': 0, 'new_registered_certificates': 0,
              'original_paper_fully_reproduced': False,
              'earlier_failed_official_exports_retained': 1,
              'scope': 'Anonymous exact-commit Git-blob, manifest and archive checks for one independent full-size32batch BMM proof, four current-SDK fresh source-only and installed-wheel checks, one genuine earlier SDK export, the failed intermediate export, selected cached development history, four direct Lean source-binding controls, SDK adversarial tests and all new source/test/workflow/documentation files. All60 current trusted SDK/Lean sources and wheel members match the published commit. The earlier renderer is checked against its own committed source. Actual v25 main-promotion receipt is retained. Captured Python/Lean/oleans are data; this observation repeats no scientific proof/model/hardware trial. Bounded read-only transport retries retain every observation.'}

    write(OUT / 'results.json', report)
    print(json.dumps({'status': report['status'], 'files': len(observations),
                      'bytes': report['total_downloaded_bytes'],
                      'download_attempts': sum(len(row['download_attempts']) for row in observations)}))


if __name__ == '__main__':
    main()
