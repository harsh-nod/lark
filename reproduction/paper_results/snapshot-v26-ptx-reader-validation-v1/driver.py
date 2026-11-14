"""Record pinned standard-library-only BMM/Linear reader and control validation."""

from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time

ROOT = Path('/tmp/lark-paper-v26-20261113')
OUT = Path('/tmp/lark-ptx-extended-reader-validation-v1-20261113')
COMMIT = '4cecb94561b47a0e4174400a7b719642c6bbbc39'
FILES = ('reproduction/paper_results/ptx_extended_evidence.py',
         'reproduction/paper_results/ptx_extended_protocols.json',
         'reproduction/paper_results/check_snapshot_controls.py',
         'tests/test_ptx_extended_paper_evidence.py')

PAYLOAD = '''"""Authored reader validation; captured packet code remains data."""
import importlib.util
import json
from pathlib import Path
import sys
import time

here = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('trusted_recording_reader', here / 'ptx_extended_evidence.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
root = here / 'corpus'
assert not any((p / '.git').exists() for p in (root, *root.parents))
config = {'evidence_groups': {}}
for kind, protocol in module.PROTOCOLS.items():
    config[module.CONFIG_KEYS[kind]] = {k: protocol[k] for k in (
        'prefix', 'publication_prefix', 'ci_prefix', 'main_prefix')}
    config['evidence_groups'][kind] = [p.relative_to(root).as_posix()
        for key in ('prefix', 'publication_prefix', 'ci_prefix', 'main_prefix')
        for p in (root / protocol[key]).iterdir() if p.is_file()]
reports = {}
for kind in module.PROTOCOLS:
    started = time.monotonic()
    reports[kind] = module.check_ptx_extended_evidence(config, kind=kind, root=root)
    reports[kind]['reader_seconds'] = time.monotonic() - started
assert not any(n == 'lark_kernels' or n.startswith('lark_kernels.') for n in sys.modules)
assert sys.flags.isolated and all(not p.startswith(str(Path('/tmp/lark-paper-v26-20261113')))
                                 for p in sys.path)
(here / 'standalone-reader-results.json').write_text(json.dumps(reports, indent=2) + '\\n')
print(json.dumps({'status': 'isolated-no-Git-no-SDK-complete-readers-passed',
                  'archives': sum(v['archives_checked'] for v in reports.values()),
                  'archive_members': sum(v['archive_members_checked'] for v in reports.values()),
                  'fresh_Lean_GPU_model_checks': 0}), flush=True)
'''


def sha(path):
    value = hashlib.sha256()
    with path.open('rb') as stream:
        for data in iter(lambda: stream.read(1024 * 1024), b''):
            value.update(data)
    return value.hexdigest()


def write(name, value):
    temporary = OUT / (name + '.next')
    temporary.write_text(json.dumps(value, indent=2) + '\n')
    temporary.replace(OUT / name)


def run(label, command, started, cwd, env=None):
    elapsed = time.monotonic() - started
    assert elapsed < 300
    with (OUT / (label + '.stdout')).open('w') as stdout, (OUT / (label + '.stderr')).open('w') as stderr:
        child = subprocess.Popen(command, cwd=cwd, env=env, stdout=stdout, stderr=stderr, start_new_session=True)
        write('progress.json', {'pid': os.getpid(), 'child_pid': child.pid, 'stage': label,
            'at_utc': datetime.now(timezone.utc).isoformat(), 'command': command,
            'per_child_limit_seconds': 120, 'aggregate_limit_seconds': 300, 'independent_workers': 1})
        begin = time.monotonic()
        timed_out = False
        try:
            code = child.wait(timeout=min(120, 300 - elapsed))
        except subprocess.TimeoutExpired:
            timed_out = True
            os.killpg(child.pid, signal.SIGTERM)
            try:
                code = child.wait(timeout=5)
            except subprocess.TimeoutExpired:
                os.killpg(child.pid, signal.SIGKILL)
                code = child.wait(timeout=5)
    result = {'command': command, 'exit_code': code, 'timed_out': timed_out, 'seconds': time.monotonic() - begin}
    write(label + '.json', result)
    assert code == 0 and not timed_out, 'Inspect original failure; never restart on observation loss'
    return result


def main():
    assert not OUT.exists(), 'Inspect original handle/output; do not restart'
    assert subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip() == COMMIT
    assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip()
    assert sha(ROOT / 'reproduction/paper_results/snapshots/20261113-v25/manifest.json') == 'e90502aaaedfacbea8c0ded36ad8facd8adf1870c755c3b5a38de321dead572f'
    OUT.mkdir()
    (OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
    source_hashes = {name: sha(ROOT / name) for name in FILES}
    started = time.monotonic()
    isolated = OUT / 'isolated'
    isolated.mkdir()
    for name in FILES[:2]:
        shutil.copyfile(ROOT / name, isolated / Path(name).name)
    (isolated / 'validate.py').write_text(PAYLOAD)
    protocols = json.loads((ROOT / FILES[1]).read_text())
    for protocol in protocols.values():
        for key in ('prefix', 'publication_prefix', 'ci_prefix', 'main_prefix'):
            shutil.copytree(ROOT / protocol[key], isolated / 'corpus' / protocol[key])
    env = {k: v for k, v in os.environ.items() if k != 'PYTHONPATH'}
    env.update(PATH='/nonexistent', PYTHONNOUSERSITE='1')
    standalone = run('standalone', ['/usr/bin/python3', '-I', str(isolated / 'validate.py')],
                     started, isolated, env)
    shutil.copyfile(isolated / 'validate.py', OUT / 'standalone-driver.py')
    shutil.copyfile(isolated / 'standalone-reader-results.json', OUT / 'standalone-reader-results.json')
    tests = run('reader-controls', ['/usr/bin/python3', '-m', 'unittest',
                'tests.test_ptx_extended_paper_evidence', '-v'], started, ROOT)
    assert 'Ran 17 tests' in (OUT / 'reader-controls.stderr').read_text()
    assert {name: sha(ROOT / name) for name in FILES} == source_hashes
    write('results.json', {'schema': 1, 'status': 'complete-extended-PTX-recording-readers-and-controls-passed',
        'source_revision': COMMIT, 'source_sha256': source_hashes, 'standalone': standalone, 'tests': tests,
        'test_cases': 17, 'rehashed_scope_controls_in_tests': 16, 'archive_members': 1662, 'archives': 16,
        'independent_kernels': 2, 'official_positive_recordings': {'bmm': 5, 'linear': 4},
        'current_positive_recordings_each': 4, 'retained_failed_official_exports': {'bmm': 1, 'linear': 0},
        'standalone_isolated_no_Git_no_SDK': True, 'captured_code_executed': False,
        'fresh_Lean_checks': 0, 'gpu_trials': 0, 'model_calls': 0,
        'original_paper_fully_reproduced': False, 'v26_snapshot_created': False,
        'per_child_limit_seconds': 120, 'aggregate_limit_seconds': 300, 'max_independent_workers': 1,
        'seconds_including_data_copies': time.monotonic() - started,
        'scope': 'Standard-library-only validation of existing recorded BMM/Linear source proofs, '
                 'all archive bytes, failed history, wheels, anonymous publication observations, '
                 'actual source CI and completed main receipts; no new scientific experiment '
                 'or finished ledger/reproduction claim.'})
    write('progress.json', {'pid': os.getpid(), 'stage': 'terminal', 'exit_code': 0,
                           'at_utc': datetime.now(timezone.utc).isoformat()})
    write('manifest.json', {p.name: sha(p) for p in sorted(OUT.iterdir())
                            if p.is_file() and p.name != 'manifest.json'})
    print(json.dumps({'status': 'readers-and-17-tests-passed', 'source': COMMIT,
                      'output': str(OUT), 'seconds': time.monotonic() - started}), flush=True)


if __name__ == '__main__':
    main()
