"""Build and exercise the installed AWQ verifier outside the source checkout."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import time
import zipfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_awq_gemm_certificate as native  # noqa: E402


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lean', required=True)
    parser.add_argument('--dependency-project', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    assert not any((p/'.git').exists() for p in (out, *out.parents))
    out.mkdir(parents=True, exist_ok=False)
    env = dict(os.environ, LARK_REAL_PROJECT=str(args.dependency_project.resolve()), PYTHONNOUSERSITE='1')
    env.pop('PYTHONPATH', None)
    checks = []

    def run(name, command, *, cwd=out, expected=True, timeout=180):
        before = time.monotonic()
        result = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
        log = result.stdout+result.stderr
        (out/(name+'.log')).write_text(log)
        assert (result.returncode == 0) is expected, name+'\n'+log
        checks.append({'name': name, 'accepted': result.returncode == 0, 'expected_accepted': expected,
                       'seconds': time.monotonic()-before, 'timed_out': False})
        return log

    run('wheel-build', [sys.executable, '-m', 'pip', 'wheel', '.', '--no-deps', '--wheel-dir', str(out/'wheel')], cwd=ROOT)
    wheel, = (out/'wheel').glob('*.whl')
    resources = {}
    with zipfile.ZipFile(wheel) as archive:
        for name, data in native.libraries().items():
            relative = ('lean-real/' if name.startswith('LarkReal/') else 'lean/')+name
            matches = [n for n in archive.namelist() if n.endswith('/share/lark/'+relative)]
            assert len(matches) == 1 and archive.read(matches[0]) == data, name
            resources[relative] = hashlib.sha256(data).hexdigest()
        python_sources = {}
        for path in sorted((ROOT/'lark_kernels').glob('*.py')):
            relative = 'lark_kernels/'+path.name
            assert archive.read(relative) == path.read_bytes(), relative
            python_sources[relative] = sha(path)
    assert len(resources) == 83
    run('create-venv', [sys.executable, '-m', 'venv', str(out/'installed')])
    python = str(out/'installed/bin/python')
    cli = str(out/'installed/bin/lark')
    run('install-wheel', [python, '-m', 'pip', 'install', '--no-index', '--no-deps', str(wheel)])
    module_path = run('installed-module-path', [python, '-c', 'import lark_kernels; print(lark_kernels.__file__)']).strip()
    assert str(out/'installed') in module_path and str(ROOT) not in module_path
    case = ROOT/'reproduction/production_awq_gemm/cases/m17_k32_n64'
    certificate = out/'certificate'
    run('installed-verify', [cli, 'verify-native-awq-gemm', str(case/'kernel.hip'),
              '--reference', str(case/'reference.py'), '--task', str(case/'task.json'),
              '--output', str(certificate), '--lean', args.lean, '--timeout', '180'])
    assert json.loads((certificate/'report.json').read_text())['status'] == 'verified'
    run('installed-recheck', [cli, 'check', str(certificate), '--lean', args.lean, '--timeout', '180'])
    tampered = out/'tampered-certificate'
    shutil.copytree(certificate, tampered)
    main = tampered/'Main.lean'
    main.write_text(main.read_text()+'\n-- Rehashed change must still be refused.\n')
    report_path = tampered/'report.json'
    report = json.loads(report_path.read_text())
    report['files']['Main.lean'] = sha(main)
    report_path.write_text(json.dumps(report, indent=2)+'\n')
    log = run('installed-rehashed-statement-refused', [cli, 'check', str(tampered), '--lean', args.lean,
              '--timeout', '180'], expected=False)
    assert 'theorem differs from fixed source/reference statement' in log
    result = {
        'schema': 1, 'status': 'installed-wheel-native-awq-real-certificate-verified-and-rechecked-outside-checkout',
        'wheel': wheel.name, 'wheel_sha256': sha(wheel), 'wheel_bytes': wheel.stat().st_size,
        'required_lean_resources_matched': len(resources), 'proof_resources': resources,
        'python_sources': python_sources, 'installed_module_path': module_path,
        'source_certificates': 1, 'managed_cache_used': True,
        'fresh_frozen_source_rebuild_claimed': False, 'rehashed_statement_rejected': True,
        'model_calls': 0, 'gpu_trials': 0, 'original_paper_fully_reproduced': False, 'checks': checks,
    }
    (out/'results.json').write_text(json.dumps(result, indent=2)+'\n')
    shutil.copyfile(Path(__file__), out/'checker.py')
    (out/'manifest.json').write_text(json.dumps({
        p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()
    }, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'required_lean_resources_matched': len(resources)}))


if __name__ == '__main__':
    main()
