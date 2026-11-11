"""Generate the fixed native 256-thread out-of-place fused Q/K adaptation."""

import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import native_qknorm_rope as native

HERE = Path(__file__).resolve().parent


def source(layout):
    lines = ['extern "C" __global__ void fused_qknorm_rope(__half* output, const __half* qkv, const __half* q_weight, const __half* k_weight, const __half* cache) {',
             '  int headGlobal = blockIdx.x * 8 + threadIdx.x / 32;',
             '  int row = headGlobal / 40;', '  int head = headGlobal % 40;',
             '  int lane = threadIdx.x % 32;', '  int column = lane * 4;',
             '  int inputBase = row * 6144 + head * 128 + column;',
             '  int outputBase = row * 5120 + head * 128 + column;']
    for i in range(4):
        lines += [f'  int a{i} = inputBase + {i};', f'  float x{i} = __half2float(qkv[a{i}]);']
    lines += ['  float ss = 0.0f;']
    for i in range(4):
        lines += [f'  float square{i} = x{i} * x{i};', f'  ss = ss + square{i};']
    lines += ['  float peer;']
    for mask in (16, 8, 4, 2, 1):
        lines += [f'  peer = __shfl_xor(ss, {mask}, 32);', '  ss = ss + peer;']
    lines += ['  float mean = ss / 128.0f;', '  float shifted = mean + 0.00001f;',
              '  float scale = rsqrtf(shifted);']
    for i in range(4):
        lines += [f'  int w{i} = column + {i};', f'  float weight{i};']
    lines += ['  if (head < 32) {']
    for i in range(4):
        lines += [f'    weight{i} = __half2float(q_weight[w{i}]);']
    lines += ['  } else {']
    for i in range(4):
        lines += [f'    weight{i} = __half2float(k_weight[w{i}]);']
    lines += ['  }']
    for i in range(4):
        lines += [f'  float scaledWeight{i} = scale * weight{i};', f'  float n{i} = x{i} * scaledWeight{i};']
    if layout == 'interleaved':
        for pair in range(2):
            x, y = pair * 2, pair * 2 + 1
            lines += [f'  int ca{pair} = row * 128 + lane * 2 + {pair};',
                      f'  int sa{pair} = ca{pair} + 64;',
                      f'  float c{pair} = __half2float(cache[ca{pair}]);',
                      f'  float s{pair} = __half2float(cache[sa{pair}]);',
                      f'  float xc{pair} = n{x} * c{pair};', f'  float ys{pair} = n{y} * s{pair};',
                      f'  float xs{pair} = n{x} * s{pair};', f'  float yc{pair} = n{y} * c{pair};',
                      f'  float o{x} = xc{pair} - ys{pair};', f'  float o{y} = xs{pair} + yc{pair};']
    elif layout == 'split-half':
        lines += ['  __syncwarp();']
        for i in range(4):
            lines += [f'  float p{i} = __shfl_xor(n{i}, 16, 32);']
        lines += ['  if (lane < 16) {']
        for i in range(4):
            lines += [f'    p{i} = -p{i};']
        lines += ['  }']
        for i in range(4):
            lines += [f'  int ca{i} = row * 128 + (column + {i}) % 64;',
                      f'  int sa{i} = ca{i} + 64;',
                      f'  float c{i} = __half2float(cache[ca{i}]);',
                      f'  float s{i} = __half2float(cache[sa{i}]);',
                      f'  float xc{i} = n{i} * c{i};', f'  float ps{i} = p{i} * s{i};',
                      f'  float o{i} = xc{i} + ps{i};']
        lines += ['  __syncwarp();']
    else:
        raise ValueError('Unknown layout')
    for i in range(4):
        lines += [f'  int out{i} = outputBase + {i};', f'  output[out{i}] = __float2half(o{i});']
    return '\n'.join(lines + ['}', ''])


def main():
    for layout in native.LAYOUTS:
        case = HERE / 'cases' / layout
        case.mkdir(parents=True, exist_ok=False)
        (case / 'kernel.hip').write_text(source(layout))
        (case / 'reference.py').write_text(native.canonical_reference(layout))
        buffers = [{'name': name, 'shape': shape, 'dtype': 'float16', 'role': role} for name, shape, role in (
            ('output', [1, 40, 128], 'output'), ('qkv', [1, 48, 128], 'input'),
            ('q_weight', [128], 'input'), ('k_weight', [128], 'input'), ('cache', [1, 128], 'input'))]
        task = {'name': 'native-fused-qknorm-rope-' + layout, 'language': 'hip', 'entry': 'fused_qknorm_rope', 'buffers': buffers,
                'launch': {'grid': 5, 'block': 256, 'warp': 64}, 'fuel': list(native.FUEL), 'rotary_layout': layout}
        (case / 'task.json').write_text(json.dumps(task, indent=2) + '\n')
        contract = native.parse_task(json.dumps(task))
        tr = native.translate(source(layout), contract)
        print(layout, len(tr.program), 'instructions', sum(i.op == 'shuffle' for i in tr.program), 'shuffles')
    files = {p.relative_to(HERE).as_posix(): hashlib.sha256(p.read_bytes()).hexdigest()
             for folder in ('cases', 'upstream') for p in sorted((HERE / folder).rglob('*')) if p.is_file()}
    provenance = {'schema': 1, 'upstream_repository': 'https://github.com/vllm-project/vllm',
                  'upstream_revision': '83f5de466a889c29ac5fbfbe342d6fe4c09811e8',
                  'upstream_path': 'csrc/fused_qknorm_rope_kernel.cu', 'files_sha256': files,
                  'rows': [1, 65535], 'q_heads': 32, 'k_heads': 8, 'v_heads': 8, 'head_dim': 128,
                  'native_block': 256, 'physical_warp': 64, 'logical_warp': 32,
                  'epsilon': '1e-5', 'rotary_dimension': 128,
                  'rewrites': ['Instantiate FP16 input/weights/cache and full128 rotation, Q32/K8/V8 heads, native block256.',
                               'Inline four-element register arrays and packed vector loads/stores as scalar operations in source order.',
                               'Expand the five XOR shuffle stages with width32 inside physical wave64.',
                               'Replace sync-mask CUDA spellings with HIP full-wave synchronization and logical32 shuffles.',
                               'Drop the provably unreachable token guard at grid5*tokens; use bounded signed-int32 arithmetic.',
                               'Retain upstream unary negation; the exact-arithmetic IR interprets it as zero subtraction.',
                               'Omit PDL/cache hints; use standard HIP launches.'],
                  'departures': ['Already-gathered cosine/sine rows replace position_ids gather, as in the paper.',
                                 'Write Q/K to a separate [tokens,40,128] output; read-only QKV input retains V heads, as the paper makes this kernel out of place.',
                                 'Fixed shapes/flags/epsilon and HIP execution; original author-adapted source and NVIDIA measurements are unavailable.'],
                  'whole_kernel_execution_proved': False, 'source_reference_equality_proved': False,
                  'source_certificates': 0, 'model_calls': 0, 'original_paper_fully_reproduced': False}
    (HERE / 'provenance.json').write_text(json.dumps(provenance, indent=2) + '\n')


if __name__ == '__main__':
    main()
