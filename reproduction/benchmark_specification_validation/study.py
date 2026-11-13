"""Evaluate all independent benchmark references on CPU with checked Float64 operations."""
import argparse
import copy
import hashlib
import importlib
import importlib.util
import json
import math
import os
import platform
import shutil
from pathlib import Path
import struct
import sys
import subprocess
import time

ROOT = Path(__file__).resolve().parents[2]
HERE = Path(__file__).resolve().parent
CASES = [
    *[(name, 'pointwise', 'pointwise/cases/hip/'+name) for name in ('relu', 'silu', 'gelu')],
    *[(name, 'normalization', 'normalization/cases/'+kind+'/hip')
      for name, kind in [('rmsnorm', 'rms'), ('layernorm', 'layer'), ('softmax', 'softmax')]],
    ('gemv', 'gemv', 'reduction/cases/hip'),
    *[(name, 'matrix', 'matrix/cases/hip/'+name) for name in ('gemm', 'bmm')],
    ('linear', 'linear', 'linear/cases/hip'),
    *[(name, 'convolution', 'convolution/cases/hip/'+name) for name in ('conv2d', 'depthwise_conv')],
    ('rope', 'rotary', 'rotary/cases/hip'),
    ('ffn', 'feedforward', 'feedforward/cases/hip'),
    ('swiglu', 'swiglu', 'swiglu/cases/hip'),
    *[(name, 'attention', 'attention/cases/'+kind+'/hip')
      for name, kind in [('attention', 'dense'), ('gqa', 'gqa')]],
]


def reference_libraries(helper):
    libraries = {}
    for line in (HERE/'BenchmarkImports.lean').read_text().splitlines():
        if not line.startswith('import '):
            continue
        for name, content in helper.owned_sources(line.split()[1]).items():
            if name in libraries and libraries[name] != content:
                raise ValueError('Conflicting owned reference source: '+name)
            libraries[name] = content
    libraries['LarkReal/BenchmarkReferenceImports.lean'] = (HERE/'BenchmarkImports.lean').read_bytes()
    return libraries


def freeze_source(output, selected, libraries):
    files = set((ROOT/'lark_kernels').rglob('*.py'))
    files.update(path for path in HERE.iterdir() if path.suffix in ('.py','.lean','.md'))
    files.update(ROOT/name for name in ('lean-real/lean-toolchain','lean-real/lake-manifest.json',
                                      'reproduction/specification_validation/study.py'))
    for _, _, directory in selected:
        files.update(path for path in (ROOT/'reproduction'/directory).iterdir() if path.is_file())
    sources = {str(path.relative_to(ROOT)):path.read_bytes() for path in files}
    for name, content in libraries.items():
        prefix = 'lean-real/' if name.startswith('LarkReal/') else 'lean/'
        name = prefix+name
        if name in sources and sources[name] != content:
            raise ValueError('Conflicting frozen source: '+name)
        sources[name] = content
    bindings = {}
    for name, content in sorted(sources.items()):
        destination = output/'source'/name
        destination.parent.mkdir(parents=True,exist_ok=True)
        destination.write_bytes(content)
        bindings[name] = hashlib.sha256(content).hexdigest()
    (output/'source-bindings.json').write_text(json.dumps(bindings,indent=2)+'\n')
    return bindings


def prepare_runtime(output, lean, libraries):
    from lark_kernels import real_backend
    version = subprocess.check_output([str(lean),'--version'],text=True,timeout=30).strip()
    if not version.startswith('Lean (version 4.19.0,'):
        raise ValueError('Lean 4.19.0 is required')
    cache, environment = real_backend.prepare(libraries,str(lean),600,
                                              target='LarkReal.BenchmarkReferenceImports')
    marker = json.loads((cache/'checked-build.json').read_text())
    module = output/'numerical_modules'
    module.mkdir()
    environment['LEAN_PATH'] = str(module)+os.pathsep+environment['LEAN_PATH']
    (module/'environment.json').write_text(json.dumps({'LEAN_PATH':environment['LEAN_PATH']})+'\n')
    for name in ('BenchmarkRealAudit','BenchmarkFloatAudit'):
        (module/(name+'.lean')).write_bytes((HERE/(name+'.lean')).read_bytes())
        bounded_execute([str(lean),'-o',name+'.olean',name+'.lean'],module,environment,
                        module/(name+'-compile.log'),180)
    imports = {'target':'LarkReal.BenchmarkReferenceImports','source_count':len(libraries),
               'sources':marker['sources'],'compiled':marker['compiled'],
               'lean_version':version,'source_checked_cache':str(cache)}
    (output/'checked-imports.json').write_text(json.dumps(imports,indent=2)+'\n')
    return module,environment,imports


def run_controls(output, module, lean, environment):
    reports = {}
    for name, script in [('numerical','controls.py'),('materialization','materialization_controls.py')]:
        directory = output/(name+'-controls')
        log_path = output/(name+'-controls-driver.log')
        with log_path.open('w') as log:
            run = subprocess.run([sys.executable,str(HERE/script),'--module',str(module),
                                  '--lean',str(lean),'--output',str(directory)],
                                 cwd=ROOT,env=environment,stdout=log,stderr=subprocess.STDOUT,timeout=600)
        if run.returncode:
            raise ValueError('Numerical control runner failed: '+str(log_path))
        report = json.loads((directory/'results.json').read_text())
        expected = ('compiled-numerical-auditor-controls-passed' if name == 'numerical'
                    else 'materialization-controls-passed')
        if report['status'] != expected:
            raise ValueError('Numerical controls incomplete: '+name)
        reports[name] = {'status':report['status'],'positive_controls':report['positive_controls'],
                         'negative_controls':report['negative_controls'],
                         'report_sha256':hashlib.sha256((directory/'results.json').read_bytes()).hexdigest(),
                         'driver_log_sha256':hashlib.sha256(log_path.read_bytes()).hexdigest()}
    return reports


def prepare(case):
    key, module, directory = case
    folder = ROOT/'reproduction'/directory
    sdk = importlib.import_module('lark_kernels.'+module)
    owned = {path.name: path.read_bytes() for path in folder.iterdir() if path.is_file()}
    text = lambda name: owned[name].decode()
    task = lambda name: json.loads(text(name))
    if module == 'feedforward':
        arguments = sdk.prepare(text('up.hip'), text('down.hip'), text('reference.py'),
                                text('up-task.json'), text('down-task.json'))
        buffers = task('up-task.json')['buffers'][:2]+task('down-task.json')['buffers'][1:]
    elif module in ('attention', 'swiglu'):
        sources = {name.replace('.hip', '.cu'): content.decode() for name, content in owned.items()}
        arguments = sdk.prepare(sources)
        first = 'score' if module == 'attention' else 'gate'
        last = 'value' if module == 'attention' else 'down'
        buffers = task(first+'-task.json')['buffers'][:2]
        if module == 'swiglu':
            buffers += task('up-task.json')['buffers'][1:2]
        buffers += task(last+'-task.json')['buffers'][1:]
    else:
        arguments = sdk.prepare(text('kernel.hip'), text('reference.py'), text('task.json'))
        buffers = task('task.json')['buffers']
    rendered = sdk.render(*arguments)
    block = rendered[rendered.rindex('namespace LarkCertificate'):]
    block = block[:block.index('theorem segmentation_data')]
    return folder, {'buffers': copy.deepcopy(buffers)}, block, owned


def bounded_execute(command, cwd, environment, log_path, timeout):
    start = time.monotonic()
    with log_path.open('w') as stream:
        try:
            run = subprocess.run(command, cwd=cwd, env=environment, stdout=stream,
                                 stderr=subprocess.STDOUT, timeout=timeout)
        except subprocess.TimeoutExpired:
            (cwd/'attempt.json').write_text(json.dumps({
                'status':'timeout','limit_seconds':timeout,'seconds':time.monotonic()-start
            },indent=2)+'\n')
            raise
    log = log_path.read_text(errors='replace')
    if run.returncode or 'error:' in log or 'PANIC' in log or 'stacktrace:' in log:
        raise ValueError('Numerical Lean execution failed: '+str(log_path)+'\n'+log[:3000])
    rows = [json.loads(line.split('LARK_SPEC_AUDIT ',1)[1]) for line in log.splitlines()
            if 'LARK_SPEC_AUDIT ' in line]
    return rows,time.monotonic()-start


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--lean', required=True, type=Path)
    parser.add_argument('--case', action='append', choices=[case[0] for case in CASES])
    parser.add_argument('--stratum', action='append', choices=['dyadic', 'normal', 'basis', 'cancellation'])
    options = parser.parse_args()
    output = options.output.resolve()
    if any((parent/'.git').exists() for parent in (output,*output.parents)):
        raise ValueError('Output must be outside a Git checkout')
    output.mkdir(parents=True,exist_ok=False)
    for key in ('CUDA_VISIBLE_DEVICES', 'HIP_VISIBLE_DEVICES', 'ROCR_VISIBLE_DEVICES'):
        os.environ[key] = ''
    sys.path.insert(0, str(ROOT))
    spec = importlib.util.spec_from_file_location('benchmark_polymorphic_study_helpers',
                                               ROOT/'reproduction/specification_validation/study.py')
    helper = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = helper
    spec.loader.exec_module(helper)
    import torch
    torch.set_num_threads(1)
    identity = helper.identity_storage_type(torch)
    selected = [case for case in CASES if not options.case or case[0] in options.case]
    strata = [name for name in helper.STRATA if not options.stratum or name in options.stratum]
    libraries = reference_libraries(helper)
    source_bindings = freeze_source(output, selected, libraries)
    module, environment, imports = prepare_runtime(output, options.lean.resolve(), libraries)
    bindings = {name: helper.sha(module/name) for name in
                ('BenchmarkRealAudit.lean','BenchmarkRealAudit.olean',
                 'BenchmarkFloatAudit.lean','BenchmarkFloatAudit.olean')}
    controls = run_controls(output, module, options.lean.resolve(), environment)
    report = {'status': 'benchmark-reference-numerical-study-incomplete',
              'original_paper_fully_reproduced': False,
              'method': 'actual-polymorphic-reference-checked-float64',
              'module_bindings': bindings, 'driver_sha256': helper.sha(Path(__file__)),
              'schema':1, 'selected_cases':[case[0] for case in selected], 'strata':strata,
              'source_bindings_sha256':helper.sha(output/'source-bindings.json'),
              'source_file_count':len(source_bindings), 'import_bindings':imports,
              'controls':controls, 'seed':19831, 'storage_conversions':'identity',
              'absolute_tolerance':1e-10, 'relative_tolerance':1e-10,
              'ieee_equivalence_theorem':False, 'floating_point_error_bound':False,
              'python':sys.version, 'platform':platform.platform(),
              'maxRecDepth': 10000, 'maxHeartbeats': 2000000,
              'per_process_timeout_seconds': 180,
              'new_certificates': 0, 'gpu_trials': 0, 'model_calls': 0,
              'torch_version': torch.__version__, 'checks': []}
    (output/'results.json').write_text(json.dumps(report,indent=2)+'\n')
    for case in selected:
        folder, metadata, block, sources = prepare(case)
        key = case[0]
        reference = helper.torch_reference(folder)
        for stratum in strata:
            directory = output/(key+'-'+stratum)
            directory.mkdir()
            inputs = helper.make_inputs(torch, metadata, stratum, 19831)
            softmax_events = []
            storage = identity
            if case[1] == 'attention':
                class CaptureStorage(identity):
                    def softmax(self, *args, **kwargs):
                        before = self.as_subclass(torch.Tensor).detach().clone()
                        result = super().softmax(*args, **kwargs)
                        softmax_events.append((before,result.as_subclass(torch.Tensor).detach().clone()))
                        return result
                storage = CaptureStorage
            expected = helper.flatten(torch, reference(*[
                value.double().as_subclass(storage) for value in inputs if value is not None]))
            if case[1] == 'attention':
                helper.require(len(softmax_events) == 1, 'Exactly one original softmax event is required')
                ordinary = helper.flatten(torch, reference(*[
                    value.double().as_subclass(identity) for value in inputs if value is not None]))
                helper.require(torch.equal(expected,ordinary), 'Telemetry changed the reference outputs')
            actual_dtype = helper.flatten(torch, reference(*[value for value in inputs if value is not None]))
            indices = sorted({0, 1, min(127, expected.numel()-2), expected.numel()//2, expected.numel()-1})
            helper.require(len(indices) == 5, 'Exactly five output positions are required')
            (directory/'Input.json').write_text(json.dumps({
                'schema': 1, 'buffers': [[] if value is None else helper.encode(value) for value in inputs]
            })+'\n')
            main = ('import BenchmarkFloatAudit\nset_option maxRecDepth 10000\n'
                    'set_option maxHeartbeats 2000000\n')+block
            main += ('benchmark_audit_float @spec from "Input.json" at ['+','.join(map(str, indices))+
                     ']\nend LarkCertificate\n')
            (directory/'Main.lean').write_text(main)
            rows, seconds = bounded_execute([str(options.lean.resolve()), 'Main.lean'],
                                           directory, environment, directory/'lean.log', 180)
            log = (directory/'lean.log').read_text(errors='replace')
            helper.require('PANIC' not in log and 'stacktrace:' not in log, 'Interpreter panic is not a result')
            helper.require([row['index'] for row in rows] == indices, 'Wrong sample selection')
            for row in rows:
                helper.require(row['output_count'] == expected.numel(), 'Reference output shape differs')
                helper.require(row['method'] == report['method'], 'Wrong audit method')
                value = struct.unpack('<d', struct.pack('<Q', int(row['float64_bits'])))[0]
                target = expected[row['index']].item()
                error = abs(value-target)
                helper.require(math.isfinite(value) and math.isfinite(target) and
                               error <= 1e-10+1e-10*abs(target), 'Float64 reference mismatch: '+key+'/'+stratum)
                rounded = actual_dtype[row['index']].item()
                row.update(lean_float64=value, torch_ideal_float64=target, absolute_error=error,
                           torch_original_dtype=rounded if math.isfinite(rounded) else None,
                           original_dtype_finite=math.isfinite(rounded))
            helper.require(bindings == {name: helper.sha(module/name) for name in bindings},
                           'Frozen numerical modules changed')
            check = {'case': key, 'stratum': stratum, 'samples': rows, 'seconds': seconds,
                     'input_sha256': helper.sha(directory/'Input.json'),
                     'main_sha256': helper.sha(directory/'Main.lean'),
                     'log_sha256': helper.sha(directory/'lean.log'),
                     'input_metadata': metadata,
                     'case_source_bindings': {name: hashlib.sha256(content).hexdigest()
                                              for name, content in sorted(sources.items())}}
            cache = directory/'MaterializedScores.json'
            strategies = {row['evaluation_strategy'] for row in rows}
            if strategies == {'source-scoreValue-materialization'}:
                helper.require(cache.is_file(), 'Missing materialized score evidence')
                evidence = json.loads(cache.read_text())
                helper.require(evidence['count'] == len(evidence['float64_bits']), 'Cache shape mismatch')
                check['materialized_score_binding'] = {
                    'sha256':helper.sha(cache),'count':evidence['count'],
                    'bytes':cache.stat().st_size,'source_function':evidence['compiled_source_function']}
                helper.require(case[1] == 'attention' and len(softmax_events) == 1,
                               'Materialized score oracle is missing')
                original_scores = softmax_events[0][0].reshape(-1)
                helper.require(original_scores.dtype == torch.float64 and
                               original_scores.device.type == 'cpu' and
                               original_scores.numel() == evidence['count'], 'Score oracle scope differs')
                actual_scores = torch.tensor([
                    struct.unpack('<d',struct.pack('<Q',int(bits)))[0]
                    for bits in evidence['float64_bits']], dtype=torch.float64, device='cpu')
                errors = (actual_scores-original_scores).abs()
                helper.require(bool(torch.isfinite(actual_scores).all()) and
                               bool((errors <= 1e-10+1e-10*original_scores.abs()).all()),
                               'Materialized score tensor differs from unchanged Torch reference')
                oracle_bits = helper.encode(original_scores)
                oracle = directory/'TorchSoftmaxInput.json'
                oracle.write_text(json.dumps({
                    'schema':1,'event':'unchanged-reference-Tensor.softmax-input',
                    'shape':list(softmax_events[0][0].shape),'dtype':'float64','device':'cpu',
                    'reference_sha256':check['case_source_bindings']['reference.py'],
                    'float64_bits':oracle_bits})+'\n')
                check['score_tensor_comparison'] = {
                    'comparisons':evidence['count'],'max_absolute_error':errors.max().item(),
                    'bit_identical':sum(a==b for a,b in zip(evidence['float64_bits'],oracle_bits)),
                    'oracle_sha256':helper.sha(oracle),'telemetry_preserved_final_outputs':True}
            else:
                helper.require(strategies == {'direct-source-evaluation'} and not cache.exists(),
                               'Unexpected materialization strategy')
            (directory/'results.json').write_text(json.dumps(check, indent=2)+'\n')
            report['checks'].append(check)
            (output/'results.json').write_text(json.dumps(report, indent=2)+'\n')
            print(json.dumps({'case': key, 'stratum': stratum, 'matched': len(rows),
                              'seconds': seconds, 'max_absolute_error': max(row['absolute_error'] for row in rows)}),
                  flush=True)
    report.update(status='benchmark-reference-numerical-study-matched',
                  sample_count=sum(len(check['samples']) for check in report['checks']),
                  selected_cases=[case[0] for case in selected],
                  score_comparison_count=sum(c.get('score_tensor_comparison',{}).get('comparisons',0)
                                             for c in report['checks']),
                  max_absolute_error=max(r['absolute_error'] for c in report['checks'] for r in c['samples']))
    (output/'results.json').write_text(json.dumps(report, indent=2)+'\n')


if __name__ == '__main__':
    main()
