"""Bind an anonymous release download to its replayed archive and Git source."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_awq_gemm_certificate as native, real_backend  # noqa: E402
from replay_native_real import CASES  # noqa: E402


def digest(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--commit', required=True)
    parser.add_argument('--ci-run', required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--proxy', required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    release = json.loads(subprocess.check_output([
        'gh', 'api', 'repos/harsh-nod/lark/releases/tags/native-awq-canonical-real-20261112']))
    assert release['target_commitish'] == args.commit and release['prerelease'] and not release['draft']
    asset, = release['assets']
    assert asset['name'] == 'awq-canonical-real-source-20261112.tar.gz'
    path = out/asset['name']
    subprocess.run(['curl', '--silent', '--show-error', '--fail', '--location', '--proto', '=https',
                    '--proto-redir', '=https', '--proxy', args.proxy, '--noproxy', '',
                    '--output', str(path), asset['browser_download_url']], check=True, timeout=60)
    frozen = ROOT/'reproduction/production_awq_gemm/results/canonical-real-v1'
    replay = json.loads((ROOT/'reproduction/production_awq_gemm/results/canonical-real-validation-v1/results.json').read_text())
    assert path.read_bytes() == (frozen/'source.tar.gz').read_bytes()
    assert replay['source_archive_sha256'] == digest(path.read_bytes()) and replay['axiom_audits'] == 734
    assert replay['source_certificates'] == 4 and replay['actual_trace_race_freedom_proved'] is True
    hashes = json.loads((frozen/'source-manifest.json').read_text())
    data = {}
    with tarfile.open(path) as archive:
        for entry in archive:
            relative = PurePosixPath(entry.name)
            assert entry.isfile() and not relative.is_absolute() and '..' not in relative.parts
            assert entry.name not in data and entry.name in hashes
            data[entry.name] = archive.extractfile(entry).read()
    assert set(data) == set(hashes) and all(digest(data[n]) == h for n,h in hashes.items())
    bindings = {}

    def bind(name, expected=None):
        content = subprocess.check_output(['git', 'show', args.commit+':'+name], cwd=ROOT)
        assert content == (ROOT/name).read_bytes(), name
        if expected is not None:
            assert content == expected, name
        bindings[name] = digest(content)

    for name, content in native.libraries().items():
        assert data[name] == content
        bind(('lean-real/' if name.startswith('LarkReal/') else 'lean/')+name, content)
    for name, content in data.items():
        if name.startswith('lark_kernels/'):
            bind(name, content)
    for name in real_backend.configuration():
        assert data[name] == real_backend.configuration()[name]
    for case in CASES:
        folder = ROOT/'reproduction/production_awq_gemm/cases'/case
        for name in ('kernel.hip', 'reference.py', 'task.json'):
            bind(str((folder/name).relative_to(ROOT)), data['cases/'+case+'/'+name])
        task, translated = native.prepare(*((folder/name).read_text() for name in ('kernel.hip','reference.py','task.json')))
        assert data['Main.lean' if case == CASES[0] else case+'.lean'] == native.render(task,translated).encode()
    bind('LICENSE', data['LICENSE'])
    bind('reproduction/production_awq_gemm/upstream/LICENSE', data['UPSTREAM-LICENSE'])
    for name in ('lean-real/lake-manifest.json', 'lean-real/lean-toolchain', 'pyproject.toml',
                 '.github/workflows/ci.yml', 'reproduction/production_awq_gemm/REAL.md',
                 *(f'reproduction/production_awq_gemm/{n}.py' for n in (
                     'check_native_real','replay_native_real','check_native_real_stages','check_installed','check_public_source'))):
        bind(name)
    ci = json.loads(subprocess.check_output(['gh','run','view',args.ci_run,'--repo','harsh-nod/lark',
                    '--json','status,conclusion,jobs,headSha,url']))
    assert ci['headSha'] == args.commit
    result = {
        'schema': 1, 'status': 'public-awq-canonical-real-source-archive-checked',
        'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'source_commit': args.commit,
        'release_url': release['html_url'], 'anonymous_downloads': 1,
        'downloaded_bytes': path.stat().st_size, 'asset_sha256': digest(path.read_bytes()),
        'all_archive_hashes_match': True, 'frozen_files_checked': len(data),
        'owned_lean_files_bound': len(native.libraries()), 'source_files_bound': len(bindings),
        'source_instances_rerendered': 4,
        'archive_byte_identical_to_independently_replayed_archive': True,
        'cold_proof_replay_repeated_on_identical_download': False, 'axiom_audit_occurrences': 734,
        'source_ci_url': ci['url'], 'source_ci_last_observed_status': ci['status'],
        'source_ci_last_observed_conclusion': ci['conclusion'], 'source_certificates': 4,
        'whole_kernel_execution_proved': True, 'actual_trace_race_freedom_proved': True,
        'source_reference_equality_proved': True, 'ieee_equivalence_proved': False,
        'floating_point_error_bound_proved': False, 'original_paper_fully_reproduced': False,
        'model_calls': 0, 'new_gpu_launches': 0,
    }
    for name,value in (('release.json',release),('source-bindings.json',{'commit':args.commit,'files':bindings}),
                       ('ci-last-observed.json',ci),('results.json',result)):
        (out/name).write_text(json.dumps(value,indent=2)+'\n')
    shutil.copyfile(Path(__file__), out/'checker.py')
    (out/'manifest.json').write_text(json.dumps({
        p.name: digest(p.read_bytes()) for p in sorted(out.iterdir()) if p.suffix in ('.json','.py')
    },indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('status','source_commit','downloaded_bytes','frozen_files_checked',
                                           'owned_lean_files_bound','source_files_bound')}))


if __name__ == '__main__':
    main()
