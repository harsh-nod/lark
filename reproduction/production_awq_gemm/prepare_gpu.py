"""Freeze exact native AWQ sources and inputs for paired AMD numerical trials."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_awq_gemm as native  # noqa: E402

HERE = Path(__file__).resolve().parent
SHAPES = ((1, 32, 64), (15, 32, 128), (16, 64, 192), (17, 32, 64),
          (17, 32, 128), (33, 64, 192), (33, 64, 256), (64, 256, 512),
          (65, 96, 64), (65, 96, 128))
LABELS = ("seeded-normal", "signed-zero", "structured-dyadic", "row-k-basis",
          "half-subnormals", "cancellation")
ATOL, RTOL, SEED = .002, .002, 261102028


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def driver(shapes):
    lines = ['#include <hip/hip_runtime.h>', '#include <hip/hip_fp16.h>']
    for i, shape in enumerate(shapes):
        lines += [f'namespace case{i} {{', f'#define awq_fp16_gemm awq_fp16_gemm_{i}',
                  f'#include "kernel_{i}.hip"', '#undef awq_fp16_gemm', '}']
    lines += ['extern "C" int run_case(int which,void* a,void* b,void* out) {',
              '  switch(which) {']
    for i, shape in enumerate(shapes):
        lines += [f'  case {i}: hipLaunchKernelGGL(case{i}::awq_fp16_gemm_{i},'
                  f'dim3({shape.grid}),dim3(64),0,0,'
                  '(const _Float16*)a,(const _Float16*)b,(_Float16*)out);break;']
    lines += ['  default:return (int)hipErrorInvalidValue;', '  }',
              '  return (int)hipGetLastError();', '}',
              'extern "C" int runtime_attribute(int which) {',
              '  hipDeviceProp_t p;if(hipGetDeviceProperties(&p,0)!=hipSuccess)return -1;',
              '  return which==0?p.warpSize:which==1?p.maxThreadsPerBlock:p.sharedMemPerBlock;', '}',
              'extern "C" const char* runtime_architecture() {',
              '  static hipDeviceProp_t p;if(hipGetDeviceProperties(&p,0)!=hipSuccess)return "unknown";',
              '  return p.gcnArchName;', '}']
    return '\n'.join(lines)+'\n'


def inputs(shape, trial, rng):
    import numpy as np
    m, k, n = shape.m, shape.k, shape.n
    ai, bi = np.arange(m*k).reshape(m, k), np.arange(k*n).reshape(k, n)
    if trial == 0:
        a, b = rng.normal(0, .25, (m, k)), rng.normal(0, .25, (k, n))
    elif trial == 1:
        a, b = np.where(ai % 2, -0., 0.), np.where(bi % 2, -0., 0.)
    elif trial == 2:
        a, b = ((ai*17) % 67-33)/64, ((bi*7) % 43-21)/64
    elif trial == 3:
        a = np.zeros((m, k))
        a[np.arange(m), (np.arange(m)*17+3) % k] = 1
        b = ((bi*11+bi//n) % 127-63)/32
    elif trial == 4:
        values = np.array([2**-24, -(2**-24), 2**-14, .125, -.125, 1, -1, 0])
        a, b = values[(ai+ai//k) % 8], ((bi*13) % 31-15)/32
    elif trial == 5:
        values = np.array([64, -64, .5, -.5, 1, -1, 2**-14, 0])
        a, b = values[(ai*7+ai//k) % 8], ((bi*3+bi//n) % 17-8)/64
    else:
        raise ValueError("Unknown trial")
    return a.astype('<f2'), b.astype('<f2')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    out = args.output.resolve()
    if out.is_relative_to(ROOT):
        raise ValueError('Fresh input directory outside checkout required')
    out.mkdir(parents=True, exist_ok=False)
    import numpy as np
    import torch
    torch.set_num_threads(1)
    shapes = tuple(native.Shape(*dims) for dims in SHAPES)
    metadata = {'schema': 1, 'method': 'independent-native-wave64-fp16-awq',
                'seed': SEED, 'atol': ATOL, 'rtol': RTOL,
                'torch': torch.__version__, 'numpy': np.__version__, 'cases': [],
                'reference': 'Fresh CPU float64 GEMM from exactly promoted frozen FP16 operands; separate CPU Torch FP32 matmul rounded to FP16',
                'source_certificates': 0, 'gpu_trials': 0, 'model_calls': 0,
                'original_paper_fully_reproduced': False}
    for i, shape in enumerate(shapes):
        source = native.kernel_source(shape)
        task = native.parse_task(json.dumps(native.task_data(shape)))
        translated = native.translate(source, task)
        (out/f'kernel_{i}.hip').write_text(source)
        (out/f'task_{i}.json').write_text(json.dumps(native.task_data(shape), indent=2)+'\n')
        case = {'index': i, 'm': shape.m, 'k': shape.k, 'n': shape.n,
                'grid': shape.grid, 'block': 64, 'tile_n': shape.tile_n,
                'fuel': list(shape.fuel), 'source_sha256': sha(out/f'kernel_{i}.hip'),
                'ir_instructions': len(translated.program), 'trials': []}
        rng = np.random.default_rng(SEED+shape.m*1000000+shape.k*1000+shape.n)
        for trial, label in enumerate(LABELS):
            a, b = inputs(shape, trial, rng)
            reference = a.astype(np.float64) @ b.astype(np.float64)
            torch_ref = (torch.from_numpy(a.copy()).float() @ torch.from_numpy(b.copy()).float()).half().numpy()
            if not np.isfinite(reference).all() or not np.isfinite(torch_ref).all():
                raise ValueError('Prepared reference must be finite')
            stem = f'case-{i}-trial-{trial}'
            (out/(stem+'-a.bin')).write_bytes(a.tobytes())
            (out/(stem+'-b.bin')).write_bytes(b.tobytes())
            case['trials'].append({'trial': trial, 'label': label, 'stem': stem,
                'cpu_float64_reference_sha256': hashlib.sha256(reference.astype('<f8').tobytes()).hexdigest(),
                'torch_fp32_rounded_reference_sha256': hashlib.sha256(torch_ref.astype('<f2').tobytes()).hexdigest()})
        metadata['cases'].append(case)
    (out/'driver.hip').write_text(driver(shapes))
    for name in ('run_gpu.py', 'audit_gpu.py'):
        shutil.copyfile(HERE/name, out/name)
    shutil.copyfile(Path(__file__), out/'prepare_gpu.py')
    (out/'dataset.json').write_text(json.dumps(metadata, indent=2)+'\n')
    (out/'manifest.json').write_text(json.dumps({'files': {
        p.relative_to(out).as_posix(): sha(p) for p in sorted(out.rglob('*')) if p.is_file()}}, indent=2)+'\n')
    print(json.dumps({'status': 'prepared', 'shapes': len(shapes), 'trials': len(shapes)*len(LABELS),
                      'output_elements_per_host': sum(p.m*p.n for p in shapes)*len(LABELS)}), flush=True)


if __name__ == '__main__':
    main()
