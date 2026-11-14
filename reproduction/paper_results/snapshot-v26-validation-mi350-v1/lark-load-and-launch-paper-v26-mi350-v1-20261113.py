"""Verify the exact transport and launch one durable, bounded CPU control job."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import subprocess
import tarfile

BASE = Path('/tmp/lark-paper-v26-controls-mi350-v1-20261113')
EXPECTED_TAR = 'bdf077911ef48dbe7b46d04f2ebb4e3075b251e17c2195cad2654c5f3f5d209c'
EXPECTED_MANIFEST = '404cab8ad340203c3af2e874278e440bd9fd39f84711db8b3e9c4964490fc386'


def sha(path):
    value = hashlib.sha256()
    with path.open('rb') as source:
        for data in iter(lambda: source.read(1024 * 1024), b''):
            value.update(data)
    return value.hexdigest()


def main():
    assert not (BASE / 'launch.json').exists(), 'Inspect existing PID/journal; do not launch again'
    assert (BASE / 'input.tar').stat().st_size == 240496640
    assert sha(BASE / 'input.tar') == EXPECTED_TAR
    with tarfile.open(BASE / 'input.tar', mode='r:') as archive:
        manifest_bytes = archive.extractfile('bundle-manifest.json').read()
        assert hashlib.sha256(manifest_bytes).hexdigest() == EXPECTED_MANIFEST
        manifest = json.loads(manifest_bytes)
        members = archive.getmembers()
        assert len(members) == len({m.name for m in members}) == len(manifest) + 1
        assert {m.name for m in members} == set(manifest) | {'bundle-manifest.json'}
        for member in members:
            path = PurePosixPath(member.name)
            assert path.parts and not path.is_absolute() and '..' not in path.parts and str(path) == member.name
            assert member.isfile() and 0 <= member.size <= 90000000
            destination = BASE / member.name
            destination.parent.mkdir(parents=True, exist_ok=True)
            assert destination.resolve().is_relative_to(BASE) and not destination.is_symlink()
            expected = EXPECTED_MANIFEST if member.name == 'bundle-manifest.json' else manifest[member.name]
            if destination.exists():
                assert destination.stat().st_size == member.size and sha(destination) == expected
            else:
                value = archive.extractfile(member).read()
                assert len(value) == member.size and hashlib.sha256(value).hexdigest() == expected
                with destination.open('xb') as output:
                    output.write(value)
        assert all(sha(BASE / name) == digest for name, digest in manifest.items())
    loaded = {'at_utc': datetime.now(timezone.utc).isoformat(), 'input_tar_sha256': EXPECTED_TAR,
              'bundle_manifest_sha256': EXPECTED_MANIFEST, 'payload_files_verified': len(manifest),
              'all_bytes_match_local_transport': True, 'GPU_jobs_started': 0, 'model_calls': 0}
    (BASE / 'load.json').write_text(json.dumps(loaded, indent=2) + '\n')
    with (BASE / 'launch.json').open('x') as lock:
        lock.write(json.dumps({'stage': 'launching', 'at_utc': datetime.now(timezone.utc).isoformat()}) + '\n')
        lock.flush()
        os.fsync(lock.fileno())
        with (BASE / 'launch.stdout').open('w') as stdout, (BASE / 'launch.stderr').open('w') as stderr:
            process = subprocess.Popen(['/usr/bin/python3', str(BASE / 'run-controls.py')], cwd=BASE,
                                       stdin=subprocess.DEVNULL, stdout=stdout, stderr=stderr,
                                       start_new_session=True)
        launch = {'stage': 'launched-once', 'pid': process.pid, 'at_utc': datetime.now(timezone.utc).isoformat(),
                  'base': str(BASE), 'host': 'mi350', 'aggregate_seconds': 300,
                  'per_replay_seconds': 120, 'max_independent_replayers': 2,
                  'GPU_jobs_started': 0, 'model_calls': 0, 'load': loaded}
        lock.seek(0)
        lock.truncate()
        lock.write(json.dumps(launch, indent=2) + '\n')
        lock.flush()
        os.fsync(lock.fileno())
    print(json.dumps(launch), flush=True)


if __name__ == '__main__':
    main()
