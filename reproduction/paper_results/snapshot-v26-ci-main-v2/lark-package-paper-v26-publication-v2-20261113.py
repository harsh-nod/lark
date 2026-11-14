"""Package actual v26 publication and both CI outcomes; no experimental reruns."""

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path('/tmp/lark-paper-v26-20261113')
BASE = ROOT / 'reproduction/paper_results'
RECOVERY = Path('/tmp/lark-paper-v26-publication-return-v2-20261113')
PUBLIC = RECOVERY / 'verified/public'
CI = Path('/tmp/lark-paper-v26-source-ci-v2-20261113')
FAILED_CI = Path('/tmp/lark-paper-v26-source-ci-v1-20261113')
SOURCE = 'ce5611655946a0a8cca76f97beb8f85bf8f4fc2b'
PREFIXES = ('snapshot-v26-publication', 'snapshot-v26-source-ci-v2',
            'snapshot-v26-source-ci-failed-v1')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def read(path):
    return json.loads(path.read_text())


def verify(folder):
    assert not any(p.is_symlink() for p in folder.rglob('*'))
    for manifest in folder.rglob('manifest.json'):
        actual = {p.name: sha(p) for p in manifest.parent.iterdir()
                  if p.is_file() and p.name != 'manifest.json'}
        assert actual == read(manifest), str(manifest)


def manifest(folder):
    assert not (folder / 'manifest.json').exists()
    records = {p.name: sha(p) for p in sorted(folder.iterdir()) if p.is_file()}
    (folder / 'manifest.json').write_text(json.dumps(records, indent=2) + '\n')


def replace(path, before, after):
    value = path.read_text()
    assert value.count(before) == 1, (path, before)
    path.write_text(value.replace(before, after))


def main():
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == SOURCE
    assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip()
    expected_jobs = set(re.findall(r'^  ([a-z][a-z0-9-]*):$',
        (ROOT / '.github/workflows/ci.yml').read_text().split('\njobs:\n', 1)[1], re.M))
    assert len(expected_jobs) == 23
    ci = read(CI / 'results.json')
    assert ci['source_commit'] == SOURCE and ci['run_id'] == 43544667567
    assert ci['status'] == 'exact-source-CI-all-23-passed' and ci['successful_jobs'] == 23
    assert set(ci['expected_jobs']) == expected_jobs
    jobs = read(CI / 'jobs.json')['jobs']
    assert len(jobs) == 23 and {j['name'] for j in jobs} == expected_jobs
    assert all(j['status'] == 'completed' and j['conclusion'] == 'success' for j in jobs)
    failed = read(FAILED_CI / 'results.json')
    assert failed['source_commit'] == '411663e0aefe96ce7fc72dc94c459c95b7dd1c3d'
    assert failed['run_id'] == 43541910060 and failed['status'] == 'exact-source-CI-terminal-non-success'
    assert failed['successful_jobs'] == 22
    assert [j['name'] for j in read(FAILED_CI / 'jobs.json')['jobs'] if j['conclusion'] != 'success'] == ['paper-ledger']
    for folder in [CI, FAILED_CI, PUBLIC, RECOVERY / 'verified/observer']:
        verify(folder)
    inventory = read(RECOVERY / 'verified/capture.json')
    assert inventory['source_commit'] == SOURCE
    for r in inventory['files']:
        p = RECOVERY / 'verified' / r['path']
        assert p.stat().st_size == r['bytes'] and sha(p) == r['sha256']
    public = read(PUBLIC / 'results.json')
    assert public['source_commit'] == SOURCE and public['snapshot'] == '20261113-v26'
    assert public['positive_replays'] == 8 and public['negative_controls'] == 81
    assert public['authenticated_download_requests'] is public['git_on_replay_path'] is False
    assert public['all_downloads_match_committed_bytes'] is public['tls_verification'] is True
    assert public['original_paper_fully_reproduced'] is False
    snapshot = 'reproduction/paper_results/snapshots/20261113-v26'
    names = set(subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', SOURCE, '--', snapshot], cwd=ROOT, text=True).splitlines())
    names.update('reproduction/paper_results/' + n for n in
                 ['replay_snapshot.py', 'check_snapshot_controls.py', 'snapshot_archives.py', 'snapshot_control_archives.py'])
    records = public['downloaded_files']
    assert len(names) == len(records) == 17 and {r['path'] for r in records} == names
    assert sum(r['bytes'] for r in records) == public['total_downloaded_bytes'] == 238899106
    for r in records:
        p = ROOT / r['path']
        assert sha(p) == r['sha256'] and p.stat().st_size == r['bytes']
        assert r['http_status'] == 200 and r['curl_ssl_verify_result'] == 0
        assert r['authorization_header'] is False and r['tls_verification'] is True
    validation = read(PUBLIC / 'validation/results.json')
    assert validation == public['validation'] and validation['status'] == 'passed'
    assert len(validation['checks']) == 89 and len(list((PUBLIC / 'validation').glob('*.log'))) == 89
    assert len(validation['released_completed_temporary_control_copies']) == 80
    assert validation['checks'] == read(BASE / 'snapshot-v26-validation-mi350-v3/validation/results.json')['checks']
    assert sha(ROOT / snapshot / 'manifest.json') == '251d9b381282f54cc721587bc88d78e0f344a44eaeaf03f112fb6f6556baf6ed'
    assert all(not (BASE / name).exists() for name in PREFIXES)
    shutil.copytree(PUBLIC, BASE / PREFIXES[0])
    destination = BASE / PREFIXES[0]
    for name in ['observer', 'launch', 'git-view']:
        shutil.copytree(RECOVERY / 'verified' / name, destination / name)
        if not (destination / name / 'manifest.json').exists():
            manifest(destination / name)
    capture = destination / 'capture'
    capture.mkdir()
    for name in ['driver.py', 'remote-capture.py', 'transport.json', 'results.json',
                 'capture.stdout', 'capture.stderr', 'download.stdout', 'download.stderr']:
        shutil.copyfile(RECOVERY / name, capture / name)
    shutil.copyfile(RECOVERY / 'verified/capture.json', capture / 'captured-file-inventory.json')
    shutil.copyfile('/tmp/lark-paper-v26-publication-source-bindings-v2-20261113.json', capture / 'source-bindings.json')
    manifest(capture)
    for folder, name in [(CI, PREFIXES[1]), (FAILED_CI, PREFIXES[2])]:
        shutil.copytree(folder, BASE / name)
    for name in PREFIXES:
        verify(BASE / name)
    readme = BASE / 'README.md'
    replace(readme, 'Anonymous publication, updated source CI and main promotion remain pending.',
            'This first run did not establish the separate public-download or source-CI gates.\n'
            'Their completed receipts are recorded below.')
    replace(readme, 'changes; a new standard-runner source CI pass is still required.',
            'changes. The subsequent actual source CI and public-download passes are recorded below.')
    anchor = '```bash\npython3 reproduction/paper_results/replay_snapshot.py \\\n  --snapshot reproduction/paper_results/snapshots/20261113-v26'
    replace(readme, anchor,
        'The [anonymous v26 publication check](snapshot-v26-publication/results.json)\n'
        'downloaded all **17 files / 238,899,106 bytes** from source `ce56116` over\n'
        'verified HTTPS without authentication. Every byte matched that exact Git\n'
        'commit. All eight positive replays and 81 negative controls then passed\n'
        'outside Git on MI350 CPU; the full download-and-validation run took 186.29\n'
        'seconds. The [observer and capture records](snapshot-v26-publication/observer/results.json)\n'
        'retain its single launch, all 89 logs and complete source bindings.\n\n'
        'The [actual source CI](snapshot-v26-source-ci-v2/results.json) records all\n'
        '**23 jobs passing** at `ce56116`, including the five-proof ledger and its\n'
        'unchanged 300-second full control-suite cap. The [earlier source CI](snapshot-v26-source-ci-failed-v1/results.json)\n'
        'remains a failure: 22 jobs passed and the ledger timed out. It was not\n'
        'rerun. Only documentation and retained receipts follow the successful\n'
        'source; code, Lean libraries, tests, workflows and snapshots retain the\n'
        'exact tested bytes. These checks establish evidence integrity and add\n'
        'no original model outcome, NVIDIA measurement or full-paper result.\n\n' + anchor)
    replace(ROOT / 'README.md',
        'all original paper results have not been reproduced.',
        'all original paper results have not been reproduced. The\n'
        '[v26 public-download validation](reproduction/paper_results/snapshot-v26-publication/results.json)\n'
        'verified all 17 published files against source `ce56116` and passed eight\n'
        'positive replays plus 81 negative controls outside Git. All\n'
        '[23 CI jobs](reproduction/paper_results/snapshot-v26-source-ci-v2/results.json)\n'
        'passed at that source. Subsequent documentation and receipts preserve\n'
        'the tested code, workflow, Lean, test and snapshot bytes.')
    archive = BASE / 'ARCHIVE_FORMAT.md'
    changes = [
        ('The complete v26 snapshot and its full control-suite run remain pending.',
         'The complete v26 build and full control-suite receipts appear below.'),
        ('the expected v26 eight-positive/eighty-one-negative counts. A v26 anonymous\ndownload and full control-suite pass have not yet been recorded.',
         'the expected v26 eight-positive/eighty-one-negative counts. The completed\nv26 anonymous-download and full control-suite record appears below.'),
        ('preparation/renderer tests passed in 0.592 seconds. The actual v26 build and\nfull control suite remain separately required.',
         'preparation/renderer tests passed in 0.592 seconds. The actual build and\ncomplete control-suite results are recorded separately below.'),
        ('model or GPU result and does not satisfy the pending full control-suite,\nanonymous publication, new source CI or main-promotion gates.',
         'model or GPU result. The separate complete-control, anonymous-publication\nand actual source-CI gates are recorded below.'),
        ('No fresh Lean, GPU or model experiment ran. Anonymous publication, updated CI\nand main promotion remain pending.',
         'No fresh Lean, GPU or model experiment ran. Public-download and source-CI\nvalidation were separate requirements; their completed records appear below.'),
        ('are retained separately. Anonymous publication and actual updated CI/main gates\nremain pending.',
         'are retained separately. The later anonymous-publication and actual source-CI\nrecords appear below.'),
        ('This is validation of the I/O change on MI350 CPU. A new standard-runner source\nCI gate is still required; the earlier timeout is not relabeled as success.',
         'This validates the I/O change on MI350 CPU. The later actual standard-runner\nsource CI succeeded; the earlier timeout remains a failed gate.'),
    ]
    for before, after in changes:
        replace(archive, before, after)
    with archive.open('a') as stream:
        stream.write('\nThe [anonymous v26 publication run](snapshot-v26-publication/results.json)\n'
            'downloaded all 17 source/snapshot files, totaling 238,899,106 bytes,\n'
            'from exact source `ce56116` with HTTPS verification and no authorization\n'
            'header. Every byte matched its Git object. All 89 controls then passed\n'
            'outside Git on MI350 CPU within the unchanged limits. Download plus\n'
            'validation took 186.2903 seconds. Its complete logs, observer, single-launch\n'
            'record and selected actual Git-object view are retained. The latter is\n'
            'explicitly a selected commit/tree/blob view, not a full repository checkout.\n\n'
            'The [actual successful source CI](snapshot-v26-source-ci-v2/results.json)\n'
            'records all 23 jobs passing at that source; the ledger control step took\n'
            '261 seconds under its original 300-second cap. The\n'
            '[first source CI](snapshot-v26-source-ci-failed-v1/results.json) remains\n'
            'a 22-success/one-timeout failure, and no workflow was rerun. Only the\n'
            'three documentation files and these new receipts follow the successful\n'
            'source; all executable, test, workflow, Lean and snapshot bytes remain\n'
            'identical. These are evidence-validation results, not new paper experiments.\n')
    subprocess.run(['git', 'diff', '--check'], cwd=ROOT, check=True)
    print(json.dumps({'status': 'actual-v26-publication-and-both-source-CI-receipts-packaged',
                      'source_commit': SOURCE, 'public_files': 17, 'successful_CI_jobs': 23,
                      'earlier_CI_preserved_as_failed': True, 'original_paper_fully_reproduced': False}))


if __name__ == '__main__':
    main()
