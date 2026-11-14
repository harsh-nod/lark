"""Return the terminal v4 receipt and independently bind its reader sources."""
import hashlib
import io
import json
from pathlib import Path, PurePosixPath
import subprocess
import tarfile

OUT = Path('/tmp/lark-paper-v28-mi350-success-return-v4-20261114')
ROOT = Path('/tmp/lark-paper-v27-20261113')
SOURCE = 'f551fe0c1403de669ea2d98184c1ef48f46221c3'
SOCKET = '/tmp/lark-mi350-forward-v2-20261114.sock'


def main():
    OUT.mkdir(exist_ok=False)
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    command = ['ssh', '-S', SOCKET, '-o', 'BatchMode=yes', '-o', 'ConnectTimeout=15',
               'mi350', 'python3', '/tmp/lark-capture-paper-v28-mi350-v4-20261114.py']
    response = subprocess.run(command, capture_output=True, timeout=90)
    (OUT / 'capture.stdout').write_bytes(response.stdout)
    (OUT / 'capture.stderr').write_bytes(response.stderr)
    assert response.returncode == 0, response.stderr
    record = json.loads(response.stdout)
    (OUT / 'transport.json').write_text(json.dumps(record, indent=2) + '\n')
    response = subprocess.run(['scp', '-q', '-o', 'ControlPath=' + SOCKET, '-o', 'BatchMode=yes',
                               'mi350:' + record['archive'], str(OUT / 'receipt.tar.gz')],
                              capture_output=True, timeout=90)
    (OUT / 'download.stdout').write_bytes(response.stdout)
    (OUT / 'download.stderr').write_bytes(response.stderr)
    assert response.returncode == 0, response.stderr
    raw = (OUT / 'receipt.tar.gz').read_bytes()
    assert len(raw) == record['archive_bytes'] and hashlib.sha256(raw).hexdigest() == record['archive_sha256']
    with tarfile.open(fileobj=io.BytesIO(raw)) as archive:
        members = archive.getmembers()
        assert len(members) == len({m.name for m in members}) == record['files']
        assert all(m.isfile() and 0 <= m.size <= 10_000_000 and not PurePosixPath(m.name).is_absolute()
                   and '..' not in PurePosixPath(m.name).parts for m in members)
        entries = {m.name: archive.extractfile(m).read() for m in members}
    manifest = json.loads(entries['manifest.json'])
    assert set(entries) == set(manifest) | {'manifest.json'}
    assert all(hashlib.sha256(entries[n]).hexdigest() == h for n, h in manifest.items())
    result = json.loads(entries['observer/results.json'])
    controls = json.loads(entries['validation/results.json'])
    assert result['source_checkpoint'] == SOURCE and result['status'] == 'complete-control-suite-passed'
    previous = json.loads((ROOT / 'reproduction/paper_results/snapshot-v28-validation-mi350-v3/verified/validation/results.json').read_text())
    assert controls['checks'] == previous['checks'] and len(controls['checks']) == 108
    assert len([n for n in entries if n.startswith('validation/') and n.endswith('.log')]) == 108
    readers = {}
    for name in ('replay_snapshot.py', 'check_snapshot_controls.py', 'snapshot_archives.py', 'snapshot_control_archives.py'):
        expected = subprocess.check_output(['git', 'show', SOURCE + ':reproduction/paper_results/' + name], cwd=ROOT)
        assert entries['input-readers/' + name] == expected
        readers[name] = hashlib.sha256(expected).hexdigest()
    verified = OUT / 'verified'
    verified.mkdir()
    for name, data in entries.items():
        path = verified / name
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(data)
    comparison = {'status': 'complete-full108-pass-receipt-and-reader-source-independently-verified',
                  'source_checkpoint': SOURCE, 'seconds': result['seconds'],
                  'archive_sha256': record['archive_sha256'], 'archive_bytes': len(raw), 'files': len(entries),
                  'all108_records_identical_to_previous_complete_v28_pass': True,
                  'reader_source_sha256': readers, 'positive_replays': 10, 'negative_controls': 98,
                  'limits': result['limits'], 'CI_or_publication_claim': False,
                  'experiment_restarts': 0, 'original_paper_fully_reproduced': False}
    (OUT / 'source-and-record-comparison.json').write_text(json.dumps(comparison, indent=2) + '\n')
    print(json.dumps(comparison), flush=True)


if __name__ == '__main__':
    main()
