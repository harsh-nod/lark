"""Check complete source-bound AWQ real certificates and meaningful refusals."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import shutil
import sys
import tarfile
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_awq_gemm_certificate as native, real_backend  # noqa: E402
from lark_kernels.certificate import check, lean_binary  # noqa: E402
from lark_kernels.ir import Refusal, lean_list  # noqa: E402

HERE = Path(__file__).resolve().parent
CASES = ('m17_k32_n64', 'm17_k32_n128', 'm33_k64_n192', 'm33_k64_n256')
SOURCE_SHAS = {
    'm17_k32_n64': '1162bb20eda8cc574d0f44f768f87d0e3b9f08c4a61b470bfbd72cc8c4f61ca1',
    'm17_k32_n128': 'd2ed6d7607fea1e3f643c7ba537410f7c87894d0b79903c49a8e012fc0a2ad21',
    'm33_k64_n192': '13de072aa81ebdc63d7f4e0785ba008010cd46d8ac924475a65d69ce067b2541',
    'm33_k64_n256': '45b053406987fb698118022c71c0d3b88bc704982987e6ebad64869a7135730d',
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, data):
    path.write_text(json.dumps(data, indent=2)+'\n')


def audits(log):
    items = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    assert len(items) == len(dict(items)), 'Repeated axiom declaration'
    assert all(set(a.strip() for a in ax.split(',') if a.strip()) <=
               {'propext', 'Classical.choice', 'Quot.sound'} for _, ax in items), 'Unapproved axiom'
    return dict(items)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lean')
    args = parser.parse_args()
    out = args.output.resolve()
    assert not any((p/'.git').exists() for p in (out, *out.parents))
    out.mkdir(parents=True, exist_ok=False)
    lean, libraries = lean_binary(args.lean), native.libraries()
    checks, exports = [], {}

    def record(name, accepted, expected, before):
        assert accepted is expected, name
        checks.append({'name': name, 'accepted': accepted, 'expected_accepted': expected,
                       'seconds': time.monotonic()-before, 'timed_out': False})

    for case in CASES:
        source = HERE/'cases'/case
        assert sha(source/'kernel.hip') == SOURCE_SHAS[case]
        before = time.monotonic()
        report = native.verify(source/'kernel.hip', source/'reference.py', source/'task.json', out/case,
                               lean=lean, timeout=180)
        record(case, report['status'] == 'verified', True, before)
        exports[case] = audits(report['axiom_audit'])
        before = time.monotonic()
        log = check(out/case, lean=lean, timeout=180)
        (out/('recheck-'+case+'.log')).write_text(log)
        record('recheck-'+case, True, True, before)

    baseline, base_case = out/CASES[0], HERE/'cases/m33_k64_n192'
    main_source = (out/'m33_k64_n192/Main.lean').read_text()
    source = (base_case/'kernel.hip').read_text()
    source_controls = {
        'source-wrong-matrix-operand': source.replace('(left0, right0_0, acc0,', '(left0, left0, acc0,', 1),
        'source-missing-reuse-barrier': source.replace('    __syncthreads();\n', '', 1),
        'source-missing-staging-barrier': ''.join(source.rsplit('    __syncthreads();\n', 1)),
        'source-wrong-shared-a-stride': source.replace('* 40 + inputCol', '* 32 + inputCol', 1),
        'source-wrong-shared-b-stride': source.replace('tileB[bRow * 72', 'tileB[bRow * 64', 1),
        'source-aliased-output': source.replace('+ 0 + lane % 16] = __float2half(acc0[0]);',
                                                '+ 0 + lane % 8] = __float2half(acc0[0]);', 1),
        'source-wrong-k-increment': source.replace('kTile++;', 'kTile = kTile + 2;', 1),
        'source-shortened-k-loop': source.replace('while (kTile < 2)', 'while (kTile < 1)', 1),
        'source-wrong-output-guard': source.replace('if (outputRow0 < 33)', 'if (outputRow0 < 32)', 1),
    }
    controls = out/'controls'
    controls.mkdir()
    for name, changed in source_controls.items():
        assert changed != source, name
        kernel = controls/(name+'.hip')
        kernel.write_text(changed)
        before = time.monotonic()
        report = native.verify(kernel, base_case/'reference.py', base_case/'task.json', controls/name,
                               lean=lean, timeout=180)
        log = report['axiom_audit']
        assert 'program_data' in log and 'is false' in log and not any(x in log for x in (
            'maximum recursion', 'maximum number of heartbeats', 'Stack overflow')), name+'\n'+log
        record(name, report['status'] == 'verified', False, before)

    direct_controls = {
        'wrong-source-block-fuel': main_source.replace('def fuel : Fuel := ⟨512,9,5,1⟩',
                                                       'def fuel : Fuel := ⟨512,9,4,1⟩', 1).replace(
            'theorem fuel_data : fuel=LarkNativeAwqGemm.fuel shape := by rfl',
            'theorem fuel_data : fuel=LarkNativeAwqGemm.fuel shape := by decide', 1),
        'wrong-shared-half-layout': main_source.replace('[640, 2304]', '[639, 2304]', 1).replace(
            'theorem layout_data : layout=LarkNativeAwqGemm.layout shape := by rfl',
            'theorem layout_data : layout=LarkNativeAwqGemm.layout shape := by decide', 1),
        'wrong-halt-site': main_source.replace('end LarkCertificate',
            'example : program[136]?=some (.scalar .halt) := by decide\nend LarkCertificate', 1),
        'wrong-real-product': '''import LarkReal.NativeAwqGemm
open LarkReal.NativeAwqGemm LarkNativeAwqGemm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def shape : Shape := ⟨1,32,64,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
example : denseTerm shape (fun _ _ => (2 : ℝ)) 0 0 0=2 := by norm_num [denseTerm]
''',
        'wrong-output-length': '''import LarkReal.NativeAwqGemm
open LarkReal.NativeAwqGemm LarkNativeAwqGemm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
def shape : Shape := ⟨1,32,64,by decide,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩
example (input : Nat → Nat → ℝ) : (denseSpec shape input).length=63 := by simp [denseSpec,shape]
''',
    }
    for name, changed in direct_controls.items():
        assert changed != main_source, name
        (controls/(name+'.lean')).write_text(changed)
        before = time.monotonic()
        accepted, log = native.validate_main(changed.encode(), libraries, lean, 180)
        (out/(name+'.log')).write_text(log)
        assert 'error:' in log and ('is false' in log or '⊢ False' in log) and not any(x in log for x in (
            'maximum recursion', 'maximum number of heartbeats', 'Stack overflow')), name+'\n'+log
        record(name, accepted, False, before)

    reference = (base_case/'reference.py').read_text()
    reference_controls = {
        'reference-wrong-operand': reference.replace('b.float()', 'a.float()'),
        'reference-transposed-weight': reference.replace('b.float()', 'b.float().T'),
        'reference-wrong-output-type': reference.replace('.half()', '.float()'),
        'reference-extra-output': reference.replace('return (', 'return a, ('),
    }
    for name, changed in reference_controls.items():
        assert changed != reference, name
        before = time.monotonic()
        try:
            native.prepare(source, changed, (base_case/'task.json').read_text())
        except Refusal as error:
            (out/(name+'.log')).write_text(str(error)+'\n')
            record(name, False, False, before)
        else:
            raise AssertionError('Changed reference accepted: '+name)

    tamper_controls = (
        ('rehashed-main', 'Main.lean', lambda text: text.replace('def fuel : Fuel := ⟨512,9,3,1⟩', 'def fuel : Fuel := ⟨512,9,2,1⟩', 1)),
        ('rehashed-model', 'Lark/NativeAwqGemmCorrect.lean', lambda text: text+'\n-- changed pinned proof\n'),
        ('rehashed-reference', 'reference.py', lambda text: text.replace('b.float()', 'a.float()')),
        ('rehashed-source', 'kernel.hip', lambda text: text.replace('* 40 + inputCol', '* 32 + inputCol', 1)),
        ('rehashed-translation', 'translation.json', lambda text: text[:-2]+', "forged": true}\n'),
        ('rehashed-configuration', 'lake-manifest.json', lambda text: text+' '),
    )
    metadata_controls = {
        'invented-ieee-proof': ('ieee_equivalence_proved', True),
        'invented-error-bound': ('floating_point_error_bound_proved', True),
        'invented-paper-completion': ('original_paper_fully_reproduced', True),
        'missing-whole-launch': ('whole_launch_proved', False),
        'missing-race-proof': ('actual_whole_trace_race_freedom_proved', False),
        'missing-reference-proof': ('source_reference_equality_proved', False),
        'boolean-m-count': ('m', True),
        'wrong-output-count': ('output_elements', 1087),
        'wrong-matrix-site-count': ('native_matrix_sites', 7),
        'wrong-shared-cell-count': ('shared_half_cells', 2943),
        'boolean-schema': ('schema', True),
        'unknown-report-field': ('unproved_extra_claim', False),
        'invented-model-call': ('model_calls', 1),
        'missing-axiom-audit': ('axiom_audit', None),
    }
    for name, filename, transform in (*tamper_controls, *((name, None, None) for name in metadata_controls)):
        dest = controls/name
        shutil.copytree(baseline, dest)
        report = json.loads((dest/'report.json').read_text())
        if filename:
            path = dest/filename
            old = path.read_text()
            changed = transform(old)
            assert changed != old, name
            path.write_text(changed)
            report['files'][filename] = sha(path)
            if filename in report['model_hashes']:
                report['model_hashes'][filename] = sha(path)
        else:
            field, value = metadata_controls[name]
            report[field] = value
        write(dest/'report.json', report)
        before = time.monotonic()
        try:
            check(dest, lean=lean, timeout=180)
        except Refusal as error:
            (out/(name+'.log')).write_text(str(error)+'\n')
            record(name, False, False, before)
        else:
            raise AssertionError('Rehashed tamper accepted: '+name)

    cache, _ = real_backend.prepare(libraries, lean, 180, target=native.TARGET)
    shutil.copyfile(cache/'build.log', out/'fresh-library-build.log')
    library_audits, main_audits = audits((out/'fresh-library-build.log').read_text()), exports[CASES[0]]
    assert len(libraries) == 83 and len(library_audits) == 702 and len(main_audits) == 8
    assert all(v == main_audits for v in exports.values())
    assert 'LarkReal.NativeAwqGemm.canonical_correct' in library_audits
    assert 'LarkNativeAwqGemm.initialized_whole_grid_race_free' in library_audits
    project = out/'source'
    shutil.copytree(baseline, project)
    for name in ('report.json', 'lean-1.log'):
        (project/name).unlink()
    for case in CASES:
        shutil.copytree(HERE/'cases'/case, project/'cases'/case)
        if case != CASES[0]:
            shutil.copyfile(out/case/'Main.lean', project/(case+'.lean'))
    for name in source_controls:
        shutil.copyfile(controls/name/'Main.lean', project/(name+'.lean'))
        shutil.copyfile(controls/(name+'.hip'), project/(name+'.hip'))
    for name in direct_controls:
        shutil.copyfile(controls/(name+'.lean'), project/(name+'.lean'))
    frozen = project/'lark_kernels'
    frozen.mkdir()
    for path in sorted((ROOT/'lark_kernels').glob('*.py')):
        shutil.copyfile(path, frozen/path.name)
    (project/'validate_source.py').write_text('''from pathlib import Path
from lark_kernels import native_awq_gemm_certificate as native
root = Path(__file__).resolve().parent
cases = ('m17_k32_n64', 'm17_k32_n128', 'm33_k64_n192', 'm33_k64_n256')
for i, case in enumerate(cases):
    folder = root/'cases'/case
    task, translation = native.prepare(*((folder/name).read_text() for name in ('kernel.hip','reference.py','task.json')))
    assert (root/('Main.lean' if i==0 else case+'.lean')).read_text()==native.render(task,translation)
    if i==0:
        assert all((root/name).read_bytes()==(folder/name).read_bytes() for name in ('kernel.hip','reference.py','task.json'))
folder = root/'cases/m33_k64_n192'
for source in sorted(root.glob('source-*.hip')):
    task, translation = native.prepare(source.read_text(),(folder/'reference.py').read_text(),(folder/'task.json').read_text())
    assert source.with_suffix('.lean').read_text()==native.render(task,translation)
print('Frozen typed reader, all four complete source/reference bindings and altered-source bindings passed.')
''')
    shutil.copyfile(ROOT/'LICENSE', project/'LICENSE')
    shutil.copyfile(HERE/'upstream/LICENSE', project/'UPSTREAM-LICENSE')
    (project/'README.md').write_text(
        'Source replay: python3 validate_source.py. Fresh proof: lake build.\n'
        'Requires Lean4.19.0 and exact locked Mathlib dependencies/cache.\n'
        'Three other case-name Lean files specialize the universal supported-shape theorem.\n'
        'source-* and wrong-* Lean files intentionally fail on false claims.\n'
        'Complete initialized native launch, actual-trace race freedom and independent dense real reference outputs are proved.\n'
        'Storage conversions are identities here; no IEEE error bound or original-paper completion is claimed.\n')
    paths = sorted(p for p in project.rglob('*') if p.is_file())
    write(out/'source-manifest.json', {str(p.relative_to(project)): sha(p) for p in paths})
    with tarfile.open(out/'source.tar.gz', 'w:gz') as archive:
        for path in paths:
            info = archive.gettarinfo(str(path), arcname=str(path.relative_to(project)))
            info.uid = info.gid = info.mtime = 0
            info.uname = info.gname = ''
            with path.open('rb') as stream:
                archive.addfile(info, stream)
    shutil.copyfile(Path(__file__), out/'checker.py')
    result = {'schema': 1, 'status': 'native-awq-canonical-real-whole-launch-checked',
              'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'model_profile': native.PROFILE,
              'export_cases': list(CASES), 'source_sha256': SOURCE_SHAS,
              'shape_contract': 'positive M,K,N; K%32=0; N%64=0; signed matrix-product address bounds',
              'block': 64, 'physical_warp': 64, 'original_fuel_preserved': True,
              'source_archive_sha256': sha(out/'source.tar.gz'), 'source_manifest_sha256': sha(out/'source-manifest.json'),
              'local_lean_modules': len(libraries), 'local_real_modules': 3, 'mathlib_revision': real_backend.MATHLIB,
              'source_certificates': len(CASES), 'parameterized_source_certificate': True,
              'whole_kernel_execution_proved': True, 'actual_trace_race_freedom_proved': True,
              'source_reference_equality_proved': True, 'ieee_equivalence_proved': False,
              'floating_point_error_bound_proved': False, 'original_paper_fully_reproduced': False,
              'model_calls': 0, 'gpu_trials': 0, 'library_axiom_audits': library_audits,
              'main_axiom_audits': main_audits, 'export_axiom_audits': exports,
              'false_lean_claims_rejected': len(source_controls)+len(direct_controls),
              'false_claims_rejected': sum(not c['expected_accepted'] for c in checks), 'checks': checks}
    write(out/'results.json', result)
    write(out/'manifest.json', {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    print(json.dumps({k: result[k] for k in ('status','source_certificates','false_claims_rejected')}))


if __name__ == '__main__':
    main()
