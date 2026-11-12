"""Numerically evaluate elaborated Lean production references against owned Torch modules."""

import argparse
import ast
from dataclasses import dataclass
import hashlib
import importlib
import importlib.util
import json
import os
from pathlib import Path
import platform
import shutil
import struct
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import real_backend  # noqa: E402


@dataclass(frozen=True)
class Case:
    key: str
    family: str
    directory: str
    sdk: str | None
    target: str
    expression: str


CASES = (
    Case('silu', 'vllm-silu', 'production_silu/cases/partial_wave', 'silu', 'LarkReal.Ops',
         'LarkReal.siluSpec shape LarkSpecAudit.input'),
    Case('weighted-rmsnorm', 'vllm-rmsnorm', 'production_rmsnorm/cases/weighted_16384',
         'native_rmsnorm_certificate', 'LarkReal.NativeRmsNorm',
         'LarkReal.NativeRmsNorm.canonical_spec shape LarkSpecAudit.input'),
    Case('fused-rmsnorm', 'fused-add-rmsnorm', 'production_fused_rmsnorm/cases/native_16384',
         'native_fused_rmsnorm_certificate', 'LarkReal.NativeFusedRmsNorm',
         'LarkReal.NativeFusedRmsNorm.canonical_spec shape LarkSpecAudit.input'),
    Case('attention', 'native-attention', 'online_attention/cases/native_fp16', None,
         'LarkReal.NativeAttention', 'LarkReal.NativeAttention.denseSpec shape LarkSpecAudit.input'),
    Case('rope-interleaved', 'vllm-rope', 'production_rope/cases/interleaved',
         'native_rope_certificate', 'Lark.NativeRopeCorrect',
         'LarkNativeRope.spec shape neox LarkReal.ops LarkSpecAudit.input'),
    Case('rope-split', 'vllm-rope', 'production_rope/cases/split-half',
         'native_rope_certificate', 'Lark.NativeRopeCorrect',
         'LarkNativeRope.spec shape neox LarkReal.ops LarkSpecAudit.input'),
    Case('qknorm-interleaved', 'fused-qknorm-rope', 'production_qknorm_rope/cases/interleaved',
         'native_qknorm_rope_certificate', 'LarkReal.NativeQKNormRopeInterleaved',
         'LarkReal.NativeQKNormRope.denseSpec shape LarkSpecAudit.input'),
    Case('qknorm-split', 'fused-qknorm-rope', 'production_qknorm_rope/cases/split-half',
         'native_qknorm_rope_split_certificate', 'LarkReal.NativeQKNormRopeSplit',
         'LarkReal.NativeQKNormRope.Split.denseSpec shape LarkSpecAudit.input'),
    Case('flashinfer-rmsnorm', 'flashinfer-rmsnorm', 'production_flashinfer_rmsnorm/cases/native_16384',
         'native_flashinfer_rmsnorm_certificate', 'LarkReal.NativeFlashInferRmsNorm',
         'LarkReal.NativeFlashInferRmsNorm.canonical_spec shape LarkSpecAudit.input'),
    Case('sglang-rmsnorm', 'sglang-rmsnorm', 'production_sglang_rmsnorm/cases/native_fixed',
         'native_sglang_rmsnorm_certificate', 'LarkReal.NativeSglangRmsNorm',
         'LarkReal.NativeSglangRmsNorm.canonical_spec shape LarkSpecAudit.input'),
    Case('awq', 'vllm-awq', 'production_awq_gemm/cases/m17_k32_n64',
         'native_awq_gemm_certificate', 'LarkReal.NativeAwqGemm',
         'LarkReal.NativeAwqGemm.denseSpec shape LarkSpecAudit.input'),
    Case('softmax-reference', 'llmc-softmax-reference', 'production_softmax/cases/native_fixed', None,
         'LarkReal.NativeSoftmaxCanonical', 'LarkReal.NativeSoftmax.canonicalSpec shape LarkSpecAudit.input'),
)
STRATA = ('dyadic', 'normal', 'basis', 'cancellation')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition, message):
    if not condition:
        raise ValueError(message)


def owned_sources(target):
    pending, sources = {target}, {}
    while pending:
        module = pending.pop()
        name = module.replace('.', '/')+'.lean'
        if name in sources:
            continue
        prefix = 'lean-real/' if module.startswith('LarkReal.') else 'lean/'
        data = real_backend.resource(prefix+name).read_bytes()
        sources[name] = data
        for line in data.decode().splitlines():
            if line.startswith('import '):
                pending.update(n for n in line.split()[1:] if n.startswith(('Lark.', 'LarkReal.')))
    return dict(sorted(sources.items()))


def freeze_source(out, selected):
    """Freeze runnable own sources, with no Git metadata or compiled objects."""
    files = {p.relative_to(ROOT) for p in (ROOT/'lark_kernels').glob('*.py')}
    files.update(p.relative_to(ROOT) for p in Path(__file__).parent.iterdir()
                 if p.suffix in ('.py', '.lean'))
    files.update(Path(n) for n in ('lean-real/lake-manifest.json', 'lean-real/lean-toolchain'))
    from lark_kernels import native_awq_gemm_certificate as awq
    libraries = awq.libraries()
    for case in selected:
        for name, content in owned_sources(case.target).items():
            if name in libraries and libraries[name] != content:
                raise ValueError('Conflicting owned Lean source: '+name)
            libraries[name] = content
        folder = Path('reproduction')/case.directory
        files.update((ROOT/folder/n).relative_to(ROOT) for n in ('reference.py', 'task.json'))
        files.update(p.relative_to(ROOT) for p in (ROOT/folder).glob('kernel.*'))
    for name in libraries:
        prefix = 'lean-real/' if name.startswith('LarkReal/') else 'lean/'
        files.add(Path(prefix+name))
    result = {}
    for name in sorted(files):
        destination = out/'source'/name
        destination.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT/name, destination)
        result[name.as_posix()] = sha(destination)
    (out/'source-bindings.json').write_text(json.dumps(result, indent=2)+'\n')
    return result


def prepare(case):
    folder = ROOT/'reproduction'/case.directory
    task_data = json.loads((folder/'task.json').read_text())
    if case.sdk:
        sdk = importlib.import_module('lark_kernels.'+case.sdk)
        kernel = 'kernel.hip' if (folder/'kernel.hip').is_file() else 'kernel.cu'
        args = sdk.prepare(*((folder/n).read_text() for n in (kernel, 'reference.py', 'task.json')))
        rendered = sdk.render(*args)
        shape = rendered[rendered.index('def shape :'):rendered.index('def layout :', rendered.index('def shape :'))]
    elif case.key == 'attention':
        from lark_kernels import native_attention
        task = native_attention.parse_task((folder/'task.json').read_text())
        native_attention.check_reference((folder/'reference.py').read_text(), task)
        native_attention.translate((folder/'kernel.hip').read_text(), task)
        shape = f'def shape : LarkNativeAttention.Shape := ⟨{task.grid},by decide,by decide⟩\n'
    else:
        from lark_kernels import native_softmax
        task = native_softmax.parse_task((folder/'task.json').read_text())
        # The softmax development reader has no certificate/reference checker.
        # Bind the same closed AST used by its existing numerical auditor.
        expected = 'import torch\ndef reference(inp):\n    return torch.softmax(inp.float(), dim=1).half()\n'
        if ast.dump(ast.parse((folder/'reference.py').read_text())) != ast.dump(ast.parse(expected)):
            raise ValueError('Softmax numerical reference AST differs')
        native_softmax.translate((folder/'kernel.hip').read_text(), task)
        shape = f'def shape : LarkNativeSoftmax.Shape := ⟨{task.grid},by decide,by decide⟩\n'
    return folder, task_data, shape


def torch_reference(folder):
    spec = importlib.util.spec_from_file_location('owned_reference_'+folder.parent.name+'_'+folder.name, folder/'reference.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.reference


def identity_storage_type(torch):
    class IdentityStorage(torch.Tensor):
        def float(self, *args, **kwargs):
            return self

        def half(self, *args, **kwargs):
            return self

        def to(self, *args, **kwargs):
            floats = (torch.float16, torch.float32, torch.float64)
            args = tuple(torch.float64 if isinstance(a, torch.dtype) and a in floats else a for a in args)
            if kwargs.get('dtype') in floats:
                kwargs = dict(kwargs, dtype=torch.float64)
            return super().to(*args, **kwargs)

        @classmethod
        def __torch_function__(cls, func, types, args=(), kwargs=None):
            kwargs = {} if kwargs is None else dict(kwargs)
            if kwargs.get('dtype') in (torch.float16, torch.float32, torch.float64):
                kwargs['dtype'] = torch.float64
            return super().__torch_function__(func, types, args, kwargs)

    return IdentityStorage


def flatten(torch, value):
    if isinstance(value, (tuple, list)):
        return torch.cat([flatten(torch, part) for part in value])
    require(value.device.type == 'cpu', 'Reference unexpectedly used a non-CPU device')
    return value.as_subclass(torch.Tensor).detach().reshape(-1)


def make_inputs(torch, task, stratum, seed):
    values = []
    for b, buffer in enumerate(task['buffers']):
        if buffer['role'] == 'output':
            values.append(None)
            continue
        count = 1
        for n in buffer['shape']:
            count *= n
        index = torch.arange(count, dtype=torch.int64, device='cpu')
        if stratum == 'dyadic':
            data = (((index*17+b*13)%31)-15).double()/16
        elif stratum == 'normal':
            generator = torch.Generator(device='cpu').manual_seed(seed+b*101)
            data = torch.randn(count, generator=generator, dtype=torch.float64, device='cpu')/4
        elif stratum == 'basis':
            data = torch.zeros(count, dtype=torch.float64, device='cpu')
            data[index%128 == 127] = 0.5
            data[index%128 == 0] = -0.0
        else:
            data = torch.where(index%2 == 0, 1., -1.).double() + ((index+b)%7).double()/2048
        if 'weight' in buffer['name'] and stratum == 'basis':
            data.fill_(1.)
        data = data.reshape(buffer['shape']).to(dtype=getattr(torch, buffer['dtype']), device='cpu')
        require(bool(torch.isfinite(data).all()), 'Non-finite generated input')
        values.append(data)
    return values


def encode(values):
    return [str(struct.unpack('<Q', struct.pack('<d', x))[0]) for x in values.double().reshape(-1).tolist()]


def execute(command, cwd, env, output, timeout):
    start = time.monotonic()
    run = subprocess.run(command, cwd=cwd, env=env, capture_output=True, text=True, timeout=timeout)
    (output).write_text(run.stdout+run.stderr)
    if run.returncode or 'error:' in run.stdout+run.stderr:
        raise ValueError('Numerical Lean execution failed: '+str(output)+'\n'+run.stdout+run.stderr)
    records = [json.loads(line.split('LARK_SPEC_AUDIT ', 1)[1]) for line in run.stdout.splitlines()
               if 'LARK_SPEC_AUDIT ' in line]
    return records, time.monotonic()-start


def merged_imports(directory, caches, dependencies):
    """Lean resolves a namespace at its first root, so use one checked own root."""
    directory.mkdir(parents=True)
    compiled = {}
    sources = {}
    for cache in caches:
        marker = json.loads((cache/'checked-build.json').read_text())
        for relative, expected in marker['compiled'].items():
            path = cache/relative
            if sha(path) != expected:
                raise ValueError('Compiled reference cache changed: '+str(path))
            name = str(Path(relative).relative_to('.lake/build/lib/lean'))
            if name in compiled and compiled[name] != expected:
                raise ValueError('Conflicting reference import: '+name)
            destination = directory/name
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(path, destination)
            compiled[name] = expected
            source = Path(name).with_suffix('.lean')
            source_hash = sha(cache/source)
            if str(source) in sources and sources[str(source)] != source_hash:
                raise ValueError('Conflicting reference source: '+str(source))
            sources[str(source)] = source_hash
    (directory/'source-bindings.json').write_text(json.dumps(sources, indent=2)+'\n')
    return dict(os.environ, LEAN_PATH=os.pathsep.join([str(directory), *dependencies])), {
        'sources':sources, 'compiled':compiled}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--lean', required=True)
    parser.add_argument('--case', action='append', choices=[c.key for c in CASES])
    parser.add_argument('--stratum', action='append', choices=STRATA)
    args = parser.parse_args()
    selected = [c for c in CASES if not args.case or c.key in args.case]
    out = args.output.resolve()
    require(not any((p/'.git').exists() for p in (out, *out.parents)), 'Output must be outside Git')
    out.mkdir(parents=True, exist_ok=False)
    for name in ('CUDA_VISIBLE_DEVICES', 'HIP_VISIBLE_DEVICES', 'ROCR_VISIBLE_DEVICES'):
        os.environ[name] = ''
    import torch
    torch.set_num_threads(1)
    identity = identity_storage_type(torch)
    bindings = freeze_source(out, selected)
    from lark_kernels import native_awq_gemm_certificate as awq
    base_cache, base_env = real_backend.prepare(awq.libraries(), args.lean, 180, target=awq.TARGET)
    dependencies = base_env['LEAN_PATH'].split(os.pathsep)[1:]
    module = Path(__file__).with_name('SpecAudit.lean')
    shutil.copyfile(module, out/'SpecAudit.lean')
    env = dict(base_env, LEAN_PATH=str(out)+':'+base_env['LEAN_PATH'])
    execute([args.lean, '-o', 'SpecAudit.olean', 'SpecAudit.lean'], out, env, out/'compile.log', 180)
    compilation = {'source_sha256':sha(out/'SpecAudit.lean'), 'olean_sha256':sha(out/'SpecAudit.olean')}
    from controls import run_controls
    control_report = run_controls(args.lean, env, out/'controls')
    records = []
    import_bindings = {}
    for case in selected:
        ordinal = CASES.index(case)
        folder, task, shape = prepare(case)
        if case.target == awq.TARGET or case.key == 'silu':
            cache = base_cache
        elif case.sdk == 'native_rope_certificate':
            sdk = importlib.import_module('lark_kernels.'+case.sdk)
            from lark_kernels import native_rope_backend
            cache, _ = native_rope_backend.prepare(sdk.libraries(), args.lean, 600)
        else:
            sdk = importlib.import_module('lark_kernels.'+case.sdk) if case.sdk else None
            sources = sdk.libraries() if sdk else owned_sources(case.target)
            cache, _ = real_backend.prepare(sources, args.lean, 600, target=case.target)
        proof_env, import_bindings[case.key] = merged_imports(
            out/'imports'/case.key, list(dict.fromkeys((base_cache, cache))), dependencies)
        reference = torch_reference(folder)
        for stratum in args.stratum or STRATA:
            directory = out/case.key/stratum
            directory.mkdir(parents=True)
            inputs = make_inputs(torch, task, stratum, 7321+ordinal*1009)
            actual_args = [x.clone() for x in inputs if x is not None]
            ideal_args = [x.double().as_subclass(identity) for x in inputs if x is not None]
            ideal = flatten(torch, reference(*ideal_args))
            actual = flatten(torch, reference(*actual_args)).double()
            require(ideal.dtype == torch.float64 and bool(torch.isfinite(ideal).all()),
                    'Idealized Torch track must return finite float64 values')
            require(actual.numel() == ideal.numel() and bool(torch.isfinite(actual).all()),
                    'Original-dtype Torch output must be finite with the same output size')
            data = {'schema':1,'buffers':[[] if x is None else encode(x) for x in inputs]}
            (directory/'Input.json').write_text(json.dumps(data)+'\n')
            count = ideal.numel()
            indices = sorted({0, 1, min(127, count-1), count//2, count-1})
            header = ('import SpecAudit\nimport '+case.target+'\nset_option maxRecDepth 10000\n'
                      'set_option maxHeartbeats 2000000\n'+shape)
            source = header+''.join(f'audit_spec ({case.expression}) from "Input.json" at {i}\n' for i in indices)
            (directory/'Main.lean').write_text(source)
            run_env = dict(proof_env, LEAN_PATH=str(out)+':'+proof_env['LEAN_PATH'])
            found, seconds = execute([args.lean,'Main.lean'], directory, run_env, directory/'lean.log', 180)
            require([r['index'] for r in found] == indices, 'Lean sample index set differs')
            comparisons = []
            for row in found:
                i = row['index']
                value = struct.unpack('<d', struct.pack('<Q', int(row['float64_bits'])))[0]
                expected = ideal[i].item()
                require(abs(value-expected) <= 1e-10+1e-10*abs(expected),
                        f'Float64 reference mismatch: {case.key}/{stratum}/{i}: Lean={value}, Torch={expected}')
                comparisons.append(dict(row, lean_float64=value, torch_ideal_float64=expected,
                                        torch_original_dtype=actual[i].item()))
            record = {'case':case.key,'family':case.family,'stratum':stratum,'samples':comparisons,
                      'reference_sha256':sha(folder/'reference.py'),'task_sha256':sha(folder/'task.json'),
                      'input_sha256':sha(directory/'Input.json'),'main_sha256':sha(directory/'Main.lean'),
                      'lean_log_sha256':sha(directory/'lean.log'),'lean_seconds':seconds,
                      'reference_executed_unchanged':True,'output_elements':count,
                      'ideal_max_abs_error':max(abs(r['lean_float64']-r['torch_ideal_float64']) for r in comparisons),
                      'native_max_abs_difference':max(abs(r['lean_float64']-r['torch_original_dtype']) for r in comparisons),
                      'seed':7321+ordinal*1009,'input_stratum':stratum}
            (directory/'results.json').write_text(json.dumps(record,indent=2)+'\n')
            records.append(record)
            print(json.dumps({'case':case.key,'stratum':stratum,'matched':len(comparisons),'seconds':seconds}),flush=True)
    for name, expected in bindings.items():
        if sha(ROOT/name) != expected:
            raise ValueError('Own source changed during numerical study: '+name)
    report = {'schema':2,'status':'elaborated-production-references-matched-on-samples','checks':records,
              'families':len({r['family'] for r in records}),'variants':len({r['case'] for r in records}),
              'samples':sum(len(r['samples']) for r in records),'torch_version':torch.__version__,
              'device':'cpu','module_compilation':compilation,'reference_imports':import_bindings,
              'source_bindings':bindings,'lean_version':subprocess.check_output([args.lean,'--version'],text=True).strip(),
              'lean_binary_sha256':sha(Path(args.lean)),'python':sys.version,'platform':platform.platform(),
              'positive_controls':control_report['positive_controls'],
              'negative_controls':control_report['negative_controls'],'new_certificates':0,
              'comparison_atol':1e-10,'comparison_rtol':1e-10,
              'strata':list(args.stratum or STRATA),'selected_cases':[c.key for c in selected],
              'formal_ieee_or_error_theorem':False,'original_paper_fully_reproduced':False,
              'model_calls':0,'gpu_trials':0,'cast_idealization':'Explicit float/half/floating to()/dtype conversions are identities for the float64 Torch track; original dtype outputs are reported separately.'}
    (out/'results.json').write_text(json.dumps(report,indent=2)+'\n')


if __name__ == '__main__':
    main()
