import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import subprocess
import sys
import tarfile
import time

packet = Path('/tmp/lark-native-fused-rmsnorm-components-v3-20261110')
project = Path('/tmp/lark-native-fused-rmsnorm-archive-replay-v3-20261110')
out = Path('/tmp/lark-native-fused-rmsnorm-archive-validation-v3-20261110')
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
for name, digest in json.loads((packet / 'manifest.json').read_text()).items():
    assert sha(packet / name) == digest, name
manifest = json.loads((packet / 'source-manifest.json').read_text())
project.mkdir(exist_ok=False)
out.mkdir(exist_ok=False)
seen = set()
with tarfile.open(packet / 'source.tar.gz') as archive:
    for entry in archive:
        p = PurePosixPath(entry.name)
        assert entry.isfile() and not p.is_absolute() and '..' not in p.parts
        assert entry.name not in seen and entry.name in manifest
        blob = archive.extractfile(entry).read()
        assert hashlib.sha256(blob).hexdigest() == manifest[entry.name]
        path = project / p
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_bytes(blob)
        seen.add(entry.name)
assert seen == set(manifest)
assert not (project / '.lake').exists()
env = dict(os.environ)
env['PATH'] = '/tmp/lean-4.19.0-linux/bin'
env.pop('PYTHONPATH', None)
env['PYTHONNOUSERSITE'] = '1'
report = json.loads((packet / 'results.json').read_text())
checks = []
for record in report['checks']:
    name, expected = record['name'], record['expected_accepted']
    if name == 'frozen-reader-replay':
        command = [sys.executable, 'validate_source.py']
    elif name == 'fresh-build':
        command = ['lake', 'build']
    else:
        command = ['lake', 'env', 'lean', name + '.lean']
    start = time.monotonic()
    run = subprocess.run(command, cwd=project, env=env, text=True, capture_output=True, timeout=300)
    log = run.stdout + run.stderr
    (out / (name + '.log')).write_text(log)
    accepted = run.returncode == 0 and 'sorryAx' not in log and 'error:' not in log
    assert accepted == expected, (name, log)
    if not expected:
        assert 'is false' in log and 'error:' in log, (name, log)
    if name == 'fresh-build':
        audits = dict(re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log))
        assert audits == report['axiom_audits']
    checks.append({'name': name, 'expected_accepted': expected, 'exit_code': run.returncode,
                   'seconds': time.monotonic() - start, 'timed_out': False})
result = {
    'schema': 1, 'status': 'frozen-source-archive-replayed', 'fresh_source_files': len(seen),
    'local_lean_modules': report['local_lean_modules'], 'axiom_audits': len(report['axiom_audits']),
    'false_claims_rejected': report['false_claims_rejected'], 'checks': checks,
    'source_archive_sha256': sha(packet / 'source.tar.gz'),
    'packet_manifest_sha256': sha(packet / 'manifest.json'),
    'git_available_on_path': False, 'frozen_python_reader_replayed': True,
    'own_lean_compiled_cache_seeded': False, 'source_certificates': 0,
    'whole_kernel_execution_proved': False, 'actual_trace_classification_proved': False,
    'gpu_trials': 0, 'model_calls': 0, 'original_paper_fully_reproduced': False,
}
(out / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
(out / 'replay.py').write_bytes(Path(__file__).read_bytes())
(out / 'manifest.json').write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2) + '\n')
print(json.dumps({k: result[k] for k in ['status', 'local_lean_modules', 'axiom_audits', 'false_claims_rejected']}))
