"""Independently recompute every frozen AWQ numerical result and compare hosts."""

import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path

SHAPES = ((1, 32, 64), (15, 32, 128), (16, 64, 192), (17, 32, 64),
          (17, 32, 128), (33, 64, 192), (33, 64, 256), (64, 256, 512),
          (65, 96, 64), (65, 96, 128))
LABELS = ('seeded-normal', 'signed-zero', 'structured-dyadic', 'row-k-basis',
          'half-subnormals', 'cancellation')
ATOL, RTOL = .002, .002


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(test, detail):
    if not test:
        raise ValueError(detail)


def check_manifest(root, files):
    for name, expected in files.items():
        path = (root/name).resolve()
        require(path.is_relative_to(root) and path.is_file() and sha(path) == expected,
                'Manifest mismatch: '+name)


def audit(data, hosts):
    import numpy as np
    import torch
    torch.set_num_threads(1)
    require(set(hosts) == {'mi350', 'mi350-2'}, 'Both named hosts required')
    metadata = json.loads((data/'dataset.json').read_text())
    check_manifest(data, json.loads((data/'manifest.json').read_text())['files'])
    require(metadata['schema'] == 1 and metadata['method'] == 'independent-native-wave64-fp16-awq', 'Dataset scope')
    require(type(metadata['source_certificates']) is int and metadata['source_certificates'] == 0
            and metadata['model_calls'] == 0 and metadata['original_paper_fully_reproduced'] is False, 'Dataset claim scope')
    require(metadata['atol'] == ATOL and metadata['rtol'] == RTOL, 'Tolerance differs')
    require([(c['m'], c['k'], c['n']) for c in metadata['cases']] == list(SHAPES), 'Shape coverage differs')
    reports, indexed = {}, {}
    for name, root in hosts.items():
        report = json.loads((root/'results.json').read_text())
        check_manifest(root, json.loads((root/'manifest.json').read_text()))
        for key in ('whole_kernel_execution_proved', 'actual_whole_trace_race_freedom_proved',
                    'source_reference_equality_proved', 'ieee_equivalence_proved',
                    'original_nvidia_kernel_executed', 'original_paper_fully_reproduced'):
            require(report[key] is False, 'Unsupported scope: '+key)
        require(type(report['source_certificates']) is int and report['source_certificates'] == 0, 'Certificate scope')
        require(type(report['model_calls']) is int and report['model_calls'] == 0, 'Model scope')
        require(report['method'] == metadata['method'] and report['architecture'].startswith('gfx950')
                and report['warp'] == 64 and report['block'] == 64, 'Native scope')
        require(report['trials'] == 60 and report['launches'] == 60 and len(report['cases']) == 60, 'Trial coverage')
        require(report['input_manifest_sha256'] == sha(data/'manifest.json')
                and report['runner_sha256'] == sha(data/'run_gpu.py'), 'Input/runner binding')
        require(report['binary_sha256'] == sha(root/'driver.so'), 'Binary binding')
        memory = json.loads((root/'memory-guard.json').read_text())
        require(memory['minimum_free_fraction'] == .98 and memory['busy_percent'] == 0
                and memory['free_bytes'] >= .98*memory['total_bytes'], 'Occupied GPU')
        require(memory['minimum_idle_samples'] == 3 and memory['poll_interval_seconds'] == .5
                and memory['max_samples'] == 20 and 3 <= len(memory['samples']) <= 20
                and all(s['busy_percent'] == 0 and s['free_bytes'] >= .98*s['total_bytes']
                        for s in memory['samples'][-3:]), 'Stable idle samples')
        entries = {(r['case'], r['trial']): r for r in report['cases']}
        require(len(entries) == 60, 'Repeated trial')
        reports[name], indexed[name] = report, entries
    records, total, cross_diff = [], 0, 0
    for i, case in enumerate(metadata['cases']):
        m, k, n = SHAPES[i]
        tile = 128 if n % 128 == 0 else 64
        require(case['index'] == i and case['grid'] == ((m+15)//16)*(n//tile)
                and case['block'] == 64 and case['tile_n'] == tile
                and case['fuel'] == [512, tile//8+1, 2*(k//32)+1, 1], 'Source shape/fuel binding')
        require(case['source_sha256'] == sha(data/f'kernel_{i}.hip'), 'Source hash')
        require([t['label'] for t in case['trials']] == list(LABELS), 'Input coverage')
        for trial, t in enumerate(case['trials']):
            stem = f'case-{i}-trial-{trial}'
            require(t['trial'] == trial and t['stem'] == stem, 'Trial order')
            a = np.fromfile(data/(stem+'-a.bin'), dtype='<f2')
            b = np.fromfile(data/(stem+'-b.bin'), dtype='<f2')
            require(a.size == m*k and b.size == k*n, 'Operand length')
            a, b = a.reshape(m, k), b.reshape(k, n)
            reference = a.astype(np.float64) @ b.astype(np.float64)
            torch_ref = (torch.from_numpy(a.copy()).float() @ torch.from_numpy(b.copy()).float()).half().numpy().astype('<f2')
            require(hashlib.sha256(reference.astype('<f8').tobytes()).hexdigest() == t['cpu_float64_reference_sha256'], 'CPU64 digest')
            require(hashlib.sha256(torch_ref.tobytes()).hexdigest() == t['torch_fp32_rounded_reference_sha256'], 'Torch digest')
            require(np.isfinite(reference).all() and np.isfinite(torch_ref).all(), 'Nonfinite reference')
            actuals = {}
            for name, root in hosts.items():
                r = indexed[name].get((i, trial))
                require(r is not None and r['stem'] == stem and r['output_elements'] == m*n
                        and r['source_sha256'] == case['source_sha256'], 'Missing/source-mismatched trial')
                require(all(r[key] is True for key in ('all_allocation_guards_unchanged', 'a_unchanged', 'b_unchanged')), 'Memory preservation')
                path = root/(stem+'-out.bin')
                require(r['output_sha256'] == sha(path), 'Output hash')
                actual = np.fromfile(path, dtype='<f2')
                require(actual.size == m*n and np.isfinite(actual).all(), 'Nonfinite/incomplete output')
                actual = actual.reshape(m, n)
                error = np.abs(actual.astype(np.float64)-reference)
                failures = int(np.count_nonzero(error > ATOL+RTOL*np.abs(reference)))
                require(failures == 0, f'Numerical mismatch {name} {stem}: {failures}')
                diff = int(np.count_nonzero(actual.view('<u2') != torch_ref.view('<u2')))
                records.append({'host': name, 'case': i, 'trial': trial, 'label': t['label'],
                                'm': m, 'k': k, 'n': n, 'output_elements': m*n,
                                'cpu_float64_failures': failures, 'max_absolute_error': float(error.max()),
                                'torch_fp32_bit_differences': diff})
                actuals[name] = actual
                total += m*n
            cross_diff += int(np.count_nonzero(actuals['mi350'].view('<u2') != actuals['mi350-2'].view('<u2')))
    for name in hosts:
        require(reports[name]['output_elements'] == sum(r['output_elements'] for r in records if r['host'] == name), 'Element coverage')
    return {'schema': 1, 'status': 'paired-native-awq-gemm-numerical-validation-checked',
            'checked_at_utc': datetime.now(timezone.utc).isoformat(), 'hosts': list(hosts),
            'shapes': len(SHAPES), 'launches': 120, 'compared_output_elements': total,
            'atol': ATOL, 'rtol': RTOL, 'cpu_float64_failures': 0,
            'torch_fp32_bit_differences': sum(r['torch_fp32_bit_differences'] for r in records),
            'cross_host_bit_differences': cross_diff, 'all_input_and_allocation_guards_preserved': True,
            'source_certificates': 0, 'model_calls': 0, 'whole_kernel_execution_proved': False,
            'actual_whole_trace_race_freedom_proved': False, 'source_reference_equality_proved': False,
            'ieee_equivalence_proved': False, 'original_nvidia_kernel_executed': False,
            'original_paper_fully_reproduced': False, 'cases': records,
            'input_manifest_sha256': sha(data/'manifest.json'),
            'host_manifest_sha256': {name: sha(root/'manifest.json') for name, root in hosts.items()}}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--mi350', type=Path, required=True)
    parser.add_argument('--mi350-2', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    report = audit(args.input.resolve(), {'mi350': args.mi350.resolve(), 'mi350-2': args.mi350_2.resolve()})
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({k: report[k] for k in ('status', 'launches', 'compared_output_elements', 'cpu_float64_failures',
                                           'torch_fp32_bit_differences', 'cross_host_bit_differences')}), flush=True)


if __name__ == '__main__':
    main()
