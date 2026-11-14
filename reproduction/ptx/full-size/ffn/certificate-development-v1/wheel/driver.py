"""Build FFN SDK offline; compare all owned bytes and replay outside the repo."""
from pathlib import Path
import hashlib
import json
import os
import subprocess
import sys
import time
import zipfile

ROOT = Path('/tmp/lark-ptx-ffn-refinement-20261114')
OUT = Path('/tmp/lark-ptx-ffn-wheel-v1-20261114')
BUILD_PYTHON = Path('/tmp/lark-ptx-pointwise-build-env-20261113/bin/python')
RECORDING = Path('/tmp/lark-ptx-ffn-certificate-export-v1-20261114')
LEAN = Path('/tmp/lean-4.19.0-linux/bin/lean')
sys.path.insert(0, str(ROOT))
from lark_kernels import ptx_ffn_certificate as checker


def run(command, name, env, cwd, timeout):
    with (OUT / (name + '.stdout')).open('wb') as stdout, (OUT / (name + '.stderr')).open('wb') as stderr:
        result = subprocess.run(command, cwd=cwd, env=env, stdout=stdout, stderr=stderr, timeout=timeout)
    assert result.returncode == 0, (name, result.returncode)


assert not OUT.exists()
OUT.mkdir()
(OUT / 'driver.py').write_bytes(Path(__file__).read_bytes())
env = dict(os.environ, PIP_NO_INDEX='1', PIP_DISABLE_PIP_VERSION_CHECK='1', PIP_CONFIG_FILE='/dev/null')
env.pop('PYTHONPATH', None)
backend = json.loads(subprocess.check_output([str(BUILD_PYTHON), '-I', '-c',
    'import json,importlib.metadata as m;print(json.dumps({n:m.version(n) for n in ["setuptools","wheel"]}))'], env=env, text=True))
assert backend == {'setuptools': '80.9.0', 'wheel': '0.45.1'}
commit = subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=ROOT, text=True).strip()
assert not subprocess.check_output(['git', 'status', '--porcelain'], cwd=ROOT, text=True).strip()
assert checker.read(RECORDING / 'source-bindings.json') == {n: checker.sha(v) for n, v in checker.own_sources().items()}
started = time.monotonic()
command = [str(BUILD_PYTHON), '-I', '-m', 'pip', 'wheel', '--no-index', '--no-deps',
           '--no-build-isolation', '--wheel-dir', str(OUT), str(ROOT)]
run(command, 'build', env, OUT, 120)
wheels = list(OUT.glob('*.whl'))
assert len(wheels) == 1
wheel = wheels[0]
sources = checker.own_sources()
with zipfile.ZipFile(wheel) as archive:
    for name, content in sources.items():
        path = ('lark_kernels/' + name.removeprefix('python/') if name.startswith('python/')
                else 'lark_kernels-0.4.0.data/data/share/lark/' + name)
        assert archive.read(path) == content, (name, path)
build = {'status': 'offline-FFN-wheel-built-and-all-owned-source-bytes-checked',
         'source_commit': commit, 'backend': backend, 'command': command,
         'wheel_filename': wheel.name, 'wheel_sha256': checker.sha(wheel.read_bytes()),
         'wheel_bytes': wheel.stat().st_size, 'owned_source_bindings_checked': len(sources),
         'owned_Lean_files_included': 14, 'new_FFN_Lean_files_included': 9,
         'seconds': time.monotonic() - started, 'network_during_build': False}
checker.write(OUT / 'build-results.json', build)
venv = OUT / 'venv'
run([sys.executable, '-m', 'venv', str(venv)], 'create-venv', env, OUT, 60)
python = venv / 'bin/python'
run([str(python), '-I', '-m', 'pip', 'install', '--no-index', '--no-deps', str(wheel)],
    'install', env, OUT, 60)
probe = OUT / 'check_installed.py'
probe.write_text('''from pathlib import Path
import json,sys,sysconfig
from lark_kernels import ptx_ffn_certificate as checker
from lark_kernels import pointwise
venv,recording = map(Path,sys.argv[1:])
package=Path(checker.__file__).resolve()
library=pointwise.induction_path().resolve()
assert package.is_relative_to(venv.resolve()), str(package)
assert library.is_relative_to(venv.resolve()), str(library)
assert str(library).endswith('/share/lark/lean/Lark/Pointwise.lean')
expected=checker.read(recording/'source-bindings.json')
actual={n:checker.sha(v) for n,v in checker.own_sources().items()}
assert actual==expected
print(json.dumps({'installed_checker':str(package),'installed_Lean_library':str(library),
'owned_source_bindings_checked':len(actual),'all_owned_bytes_equal_to_export':True,
'isolated_python':bool(sys.flags.isolated),'data_path':sysconfig.get_path('data')}))
''')
run([str(python), '-I', str(probe), str(venv), str(RECORDING)], 'installed-path-and-bindings', env, OUT, 60)
replay = OUT / 'fresh-installed-replay'
checker.write(OUT / 'progress.json', {'pid': os.getpid(), 'stage': 'fresh-installed-proof-replay',
              'source_commit': commit, 'build_passed': True})
replay_started = time.monotonic()
command = [str(python), '-I', '-m', 'lark_kernels.ptx_ffn_certificate', 'replay',
           '--recording', str(RECORDING), '--output', str(replay), '--lean', str(LEAN)]
run(command, 'installed-replay', env, OUT, 620)
result = checker.read(replay / 'replay.json')
assert result['status'] == 'fresh-source-only-PTX-FFN-pipeline-proof-replay-passed'
assert result['owned_modules_freshly_compiled'] == 14 and result['old_owned_olean_cache_used'] is False
report = {'schema': 1, 'status': 'offline-wheel-installed-isolated-FFN-source-replay-passed',
          'source_commit': commit, 'build': build, 'replay': result,
          'installed_probe': json.loads((OUT / 'installed-path-and-bindings.stdout').read_text()),
          'replay_seconds': time.monotonic() - replay_started,
          'model_calls': 0, 'gpu_trials': 0, 'nvidia_execution': False,
          'new_registered_source_certificates': 0, 'source_bound_proofs_added': 0,
          'original_paper_fully_reproduced': False}
checker.write(OUT / 'results.json', report)
# The virtual environment is a tool environment, not an evidence payload. Bind
# every retained driver, build/install/probe log, wheel and fresh replay byte.
inventory = {p.relative_to(OUT).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
             for p in sorted(OUT.rglob('*')) if p.is_file()
             and not p.is_relative_to(venv) and p != OUT / 'manifest.json'}
checker.write(OUT / 'manifest.json', inventory)
print(json.dumps({k: report[k] for k in ('status', 'source_commit', 'replay_seconds')}), flush=True)
