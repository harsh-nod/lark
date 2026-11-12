"""Rebuild frozen complete AWQ real proofs without Git or owned compiled objects."""

import argparse
import hashlib
import json
import math
import os
from pathlib import Path, PurePosixPath
import re
import shutil
import subprocess
import sys
import tarfile
import time

MATHLIB = 'c44e0c8ee63ca166450922a373c7409c5d26b00b'
CASES = ('m17_k32_n64', 'm17_k32_n128', 'm33_k64_n192', 'm33_k64_n256')
SOURCE_SHAS = {
    'm17_k32_n64': '1162bb20eda8cc574d0f44f768f87d0e3b9f08c4a61b470bfbd72cc8c4f61ca1',
    'm17_k32_n128': 'd2ed6d7607fea1e3f643c7ba537410f7c87894d0b79903c49a8e012fc0a2ad21',
    'm33_k64_n192': '13de072aa81ebdc63d7f4e0785ba008010cd46d8ac924475a65d69ce067b2541',
    'm33_k64_n256': '45b053406987fb698118022c71c0d3b88bc704982987e6ebad64869a7135730d',
}
SOURCE_CONTROLS = (
    'source-wrong-matrix-operand', 'source-missing-reuse-barrier', 'source-missing-staging-barrier',
    'source-wrong-shared-a-stride', 'source-wrong-shared-b-stride', 'source-aliased-output',
    'source-wrong-k-increment', 'source-shortened-k-loop', 'source-wrong-output-guard',
)
DIRECT_CONTROLS = ('wrong-source-block-fuel', 'wrong-shared-half-layout', 'wrong-halt-site',
                   'wrong-real-product', 'wrong-output-length')
REFERENCE_CONTROLS = ('reference-wrong-operand', 'reference-transposed-weight',
                      'reference-wrong-output-type', 'reference-extra-output')
TAMPER_CONTROLS = (
    'rehashed-main', 'rehashed-model', 'rehashed-reference', 'rehashed-source', 'rehashed-translation',
    'rehashed-configuration', 'invented-ieee-proof', 'invented-error-bound', 'invented-paper-completion',
    'missing-whole-launch', 'missing-race-proof', 'missing-reference-proof', 'boolean-m-count',
    'wrong-output-count', 'wrong-matrix-site-count', 'wrong-shared-cell-count', 'boolean-schema',
    'unknown-report-field', 'invented-model-call', 'missing-axiom-audit',
)
CONTROLS = SOURCE_CONTROLS+DIRECT_CONTROLS


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audits(log):
    items = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    require(len(items) == len(dict(items)), 'Repeated axiom audit')
    require(all(set(a.strip() for a in ax.split(',') if a.strip()) <=
                {'propext', 'Classical.choice', 'Quot.sound'} for _, ax in items), 'Unapproved axiom')
    return dict(items)


def validate_metadata(report):
    required = {
        'schema': 1, 'status': 'native-awq-canonical-real-whole-launch-checked',
        'model_profile': 'native-awq-gemm-real-v24', 'export_cases': list(CASES), 'source_sha256': SOURCE_SHAS,
        'shape_contract': 'positive M,K,N; K%32=0; N%64=0; signed matrix-product address bounds',
        'block': 64, 'physical_warp': 64, 'original_fuel_preserved': True,
        'local_lean_modules': 83, 'local_real_modules': 3, 'mathlib_revision': MATHLIB,
        'source_certificates': 4, 'parameterized_source_certificate': True,
        'whole_kernel_execution_proved': True, 'actual_trace_race_freedom_proved': True,
        'source_reference_equality_proved': True, 'ieee_equivalence_proved': False,
        'floating_point_error_bound_proved': False, 'original_paper_fully_reproduced': False,
        'model_calls': 0, 'gpu_trials': 0, 'false_lean_claims_rejected': 14, 'false_claims_rejected': 38,
    }
    extra = {'checked_at_utc', 'source_archive_sha256', 'source_manifest_sha256', 'library_axiom_audits',
             'main_axiom_audits', 'export_axiom_audits', 'checks'}
    message = 'Unsupported AWQ real stage/scope metadata'
    require(type(report) is dict and set(report) == set(required)|extra, message)

    def same_typed(actual, expected):
        if type(actual) is not type(expected):
            return False
        if isinstance(expected, dict):
            return set(actual) == set(expected) and all(same_typed(actual[k], v) for k,v in expected.items())
        if isinstance(expected, list):
            return len(actual) == len(expected) and all(same_typed(a,b) for a,b in zip(actual,expected))
        return actual == expected

    require(all(same_typed(report[k], v) for k,v in required.items()), message)
    require(type(report['checked_at_utc']) is str and bool(report['checked_at_utc']), message)
    require(all(type(report[k]) is str and re.fullmatch(r'[0-9a-f]{64}', report[k])
                for k in ('source_archive_sha256','source_manifest_sha256')), message)
    library, main, exports = (report[k] for k in ('library_axiom_audits','main_axiom_audits','export_axiom_audits'))
    require(type(library) is dict and len(library) == 702 and type(main) is dict and len(main) == 8
            and type(exports) is dict and set(exports) == set(CASES)
            and all(type(v) is dict and v == main for v in exports.values()), message)
    for name, ax in {**library, **main}.items():
        require(type(name) is str and type(ax) is str and set(a.strip() for a in ax.split(',') if a.strip())
                <= {'propext','Classical.choice','Quot.sound'}, message)
    require({'LarkReal.NativeAwqGemm.canonical_correct', 'LarkNativeAwqGemm.source_correct',
             'LarkNativeAwqGemm.initialized_whole_grid_race_free'} <= set(library), message)
    require(set(main) == {'LarkCertificate.'+n for n in (
        'reference_data','program_data','segmentation_data','segmentation','race_free',
        'segment_equivalence','kernel_eq_spec','kernel_eq_spec_pre')}, message)
    names = [name for case in CASES for name in (case,'recheck-'+case)]
    names += list(CONTROLS+REFERENCE_CONTROLS+TAMPER_CONTROLS)
    checks = report['checks']
    require(type(checks) is list and len(checks) == len(names), message)
    for i, (check, name) in enumerate(zip(checks, names)):
        require(type(check) is dict and set(check) == {'name','accepted','expected_accepted','seconds','timed_out'}
                and check['name'] == name and check['accepted'] is (i<8)
                and check['expected_accepted'] is (i<8) and check['timed_out'] is False
                and type(check['seconds']) in (int,float) and math.isfinite(check['seconds'])
                and check['seconds'] >= 0, message)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lean-bin', type=Path, required=True)
    parser.add_argument('--dependency-project', type=Path, required=True)
    args = parser.parse_args()
    packet, out, lean_bin = args.packet.resolve(), args.output.resolve(), args.lean_bin.resolve()
    require(not any((p/'.git').exists() for p in (out, *out.parents)), 'Output must be outside Git')
    require(all((lean_bin/name).is_file() for name in ('lean','lake')), 'Lean/lake missing')
    require(shutil.which('git', path=str(lean_bin)) is None, 'Git must be unavailable on replay PATH')
    manifest = json.loads((packet/'manifest.json').read_text())
    require({'results.json','source-manifest.json','source.tar.gz'} <= set(manifest), 'Incomplete packet manifest')
    for name, digest in manifest.items():
        require(Path(name).name == name and not (packet/name).is_symlink() and sha(packet/name) == digest,
                'Packet hash/path: '+name)
    report = json.loads((packet/'results.json').read_text())
    validate_metadata(report)
    require(sha(packet/'source.tar.gz') == report['source_archive_sha256'], 'Archive hash differs')
    require(sha(packet/'source-manifest.json') == report['source_manifest_sha256'], 'Source manifest hash differs')
    source_manifest = json.loads((packet/'source-manifest.json').read_text())
    out.mkdir(parents=True, exist_ok=False)
    project = out/'project'
    project.mkdir()
    seen, total = set(), 0
    with tarfile.open(packet/'source.tar.gz') as archive:
        for entry in archive:
            rel = PurePosixPath(entry.name)
            require(entry.isfile() and not rel.is_absolute() and '..' not in rel.parts and str(rel) == entry.name
                    and not entry.name.endswith(('.olean','.ilean')) and '.git' not in rel.parts and '.lake' not in rel.parts
                    and entry.name not in seen and entry.name in source_manifest, 'Unexpected archived source: '+entry.name)
            total += entry.size
            require(entry.size <= 8_000_000 and total <= 50_000_000, 'Source archive too large')
            blob = archive.extractfile(entry).read()
            require(hashlib.sha256(blob).hexdigest() == source_manifest[entry.name], 'Source hash: '+entry.name)
            path = project/rel
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(blob)
            seen.add(entry.name)
    require(seen == set(source_manifest) and not (project/'.lake').exists(), 'Source/cache mismatch')
    require(not any(project.rglob('*.olean')), 'Compiled own objects present before build')
    owned = [name for name in seen if name.startswith(('Lark/','LarkReal/')) and name.endswith('.lean')]
    require(len(owned) == 83 and sum(name.startswith('LarkReal/') for name in owned) == 3, 'Proof source closure differs')
    for path in (*project.glob('Lark/NativeAwqGemm*.lean'), *project.glob('LarkReal/NativeAwqGemm*.lean'),
                 *project.glob('*.lean')):
        source = path.read_text()
        require(source.count('set_option maxRecDepth 10000') == 1
                and source.count('set_option maxHeartbeats 2000000') == 1
                and not re.search(r'\b(?:sorry|admit|native_decide)\b|(?m:^\s*axiom\b)',source),
                'AWQ proof policy: '+path.name)
    lock = json.loads((project/'lake-manifest.json').read_text())
    packages = lock['packages']
    require(len(packages) == 9 and all(p['type'] == 'git' for p in packages)
            and [p['rev'] for p in packages if p['name'] == 'mathlib'] == [MATHLIB], 'Wrong dependency lock')
    seeds, dependency_records = {}, []
    for package in packages:
        name = package['name']
        require(re.fullmatch(r'[A-Za-z0-9_]+',name), 'Unexpected dependency name')
        path = (args.dependency_project/'.lake/packages'/name).resolve()
        head = subprocess.run(['git','rev-parse','HEAD'],cwd=path,capture_output=True,text=True,timeout=30)
        clean = subprocess.run(['git','diff','--quiet','--no-ext-diff','--no-textconv','HEAD','--'],
                               cwd=path,capture_output=True,timeout=30)
        require(head.returncode == 0 and head.stdout.strip() == package['rev'] and clean.returncode == 0,
                'Dependency source differs: '+name)
        seeds[name] = path
        dependency_records.append({'name': name,'revision': package['rev'],'clean': True})
    overrides = [dict(package,type='path',dir=str(seeds[package['name']])) for package in packages]
    overrides_path = out/'dependency-path-overrides.json'
    overrides_path.write_text(json.dumps({'version': lock['version'],'packages': overrides},indent=2)+'\n')
    lake = ['lake','--packages='+str(overrides_path)]
    env = dict(os.environ,PATH=str(lean_bin),PYTHONNOUSERSITE='1')
    env.pop('PYTHONPATH',None)
    env.pop('LEAN_PATH',None)
    checks = []

    def run(name, command, expected):
        before = time.monotonic()
        result = subprocess.run(command,cwd=project,env=env,text=True,capture_output=True,timeout=180)
        log = result.stdout+result.stderr
        (out/(name+'.log')).write_text(log)
        accepted = result.returncode == 0 and 'error:' not in log and 'sorryAx' not in log
        require(accepted is expected,'Unexpected acceptance: '+name+'\n'+log)
        if not expected:
            require('error:' in log and ('is false' in log or '⊢ False' in log) and not any(s in log for s in (
                'maximum recursion','maximum number of heartbeats','Stack overflow')),'Wrong rejection gate: '+name)
        checks.append({'name': name,'accepted': accepted,'expected_accepted': expected,'exit_code': result.returncode,
                       'seconds': time.monotonic()-before,'timed_out': False})
        return log

    run('frozen-reader-replay',[sys.executable,'validate_source.py'],True)
    build_log = run('fresh-build',lake+['build'],True)
    all_audits = audits(build_log)
    require(all_audits == {**report['library_axiom_audits'],**report['main_axiom_audits']},'Fresh axiom audits differ')
    for case in CASES[1:]:
        log = run(case,lake+['env','lean',case+'.lean'],True)
        require(audits(log) == report['main_axiom_audits'],'Source instance audits differ')
    for name in CONTROLS:
        run(name,lake+['env','lean',name+'.lean'],False)
    result = {'schema': 1,'status': 'frozen-awq-canonical-real-whole-launch-archive-replayed',
              'source_archive_sha256': sha(packet/'source.tar.gz'),'packet_manifest_sha256': sha(packet/'manifest.json'),
              'source_manifest_sha256': sha(packet/'source-manifest.json'),'fresh_source_files': len(seen),
              'local_lean_modules': 83,'axiom_audits': len(all_audits)+3*len(report['main_axiom_audits']),
              'unique_axiom_declarations': len(all_audits),'source_instances': 4,
              'dependency_sources_checked_before_path_restriction': dependency_records,
              'git_available_on_replay_path': False,'own_lean_compiled_cache_seeded': False,
              'external_pinned_mathlib_cache_seeded': True,'frozen_python_reader_replayed': True,
              'dependency_path_overrides_used': True,'original_git_lock_unchanged': True,
              'source_certificates': 4,'parameterized_source_certificate': True,'original_fuel_preserved': True,
              'whole_kernel_execution_proved': True,'actual_trace_race_freedom_proved': True,
              'source_reference_equality_proved': True,'ieee_equivalence_proved': False,
              'floating_point_error_bound_proved': False,'original_paper_fully_reproduced': False,
              'gpu_trials': 0,'model_calls': 0,'false_lean_claims_rejected': len(CONTROLS),'checks': checks}
    (out/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    shutil.copyfile(Path(__file__),out/'replay.py')
    (out/'manifest.json').write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()},indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('status','source_certificates','axiom_audits','false_lean_claims_rejected')}))


if __name__ == '__main__':
    main()
