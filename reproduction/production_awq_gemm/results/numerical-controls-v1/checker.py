"""Reject fully rehashed false numerical claims without executing a GPU."""

import argparse
import json
from pathlib import Path
import shutil

from audit_gpu import audit, sha


def write(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def rehash(root, nested=False):
    manifest = {p.relative_to(root).as_posix(): sha(p) for p in sorted(root.rglob('*'))
                if p.is_file() and p != root/'manifest.json'}
    write(root/'manifest.json', {'files': manifest} if nested else manifest)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, required=True)
    parser.add_argument('--mi350', type=Path, required=True)
    parser.add_argument('--mi350-2', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    args = parser.parse_args()
    data = args.input.resolve()
    hosts = {'mi350': args.mi350.resolve(), 'mi350-2': args.mi350_2.resolve()}
    out = args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    positive = audit(data, hosts)
    checks = [{'name': 'unchanged-paired-packet', 'accepted': True,
               'compared_output_elements': positive['compared_output_elements']}]
    controls = {
        'widened-tolerance': 'Tolerance differs',
        'missing-trial': 'Trial coverage',
        'changed-readonly-input': 'Memory preservation',
        'one-wrong-output': 'Numerical mismatch',
        'missing-final-store': 'Nonfinite/incomplete output',
        'invented-whole-execution': 'Unsupported scope',
        'invented-paper-completion': 'Unsupported scope',
        'boolean-certificate-count': 'Certificate scope',
        'occupied-gpu': 'Occupied GPU',
        'non-idle-final-history': 'Stable idle samples',
    }
    for name, expected in controls.items():
        root = out/name
        root.mkdir()
        target = root/'mi350'
        shutil.copytree(hosts['mi350'], target)
        changed_hosts, changed_data = {**hosts, 'mi350': target}, data
        report = json.loads((target/'results.json').read_text())
        if name == 'widened-tolerance':
            changed_data = root/'inputs'
            shutil.copytree(data, changed_data)
            metadata = json.loads((changed_data/'dataset.json').read_text())
            metadata['atol'] = 1.0
            write(changed_data/'dataset.json', metadata)
            rehash(changed_data, nested=True)
        elif name == 'missing-trial':
            report['cases'].pop()
        elif name == 'changed-readonly-input':
            report['cases'][0]['a_unchanged'] = False
        elif name in ('one-wrong-output', 'missing-final-store'):
            record = report['cases'][0]
            path = target/(record['stem']+'-out.bin')
            content = bytearray(path.read_bytes())
            content[-2:] = b'\xff\x7b' if name == 'one-wrong-output' else b'\x00\x7e'
            path.write_bytes(content)
            record['output_sha256'] = sha(path)
        elif name == 'invented-whole-execution':
            report['whole_kernel_execution_proved'] = True
        elif name == 'invented-paper-completion':
            report['original_paper_fully_reproduced'] = True
        elif name == 'boolean-certificate-count':
            report['source_certificates'] = False
        else:
            memory = json.loads((target/'memory-guard.json').read_text())
            if name == 'occupied-gpu':
                memory['busy_percent'] = 1
            else:
                memory['samples'][-2]['busy_percent'] = 1
            write(target/'memory-guard.json', memory)
        write(target/'results.json', report)
        rehash(target)
        try:
            audit(changed_data, changed_hosts)
        except ValueError as error:
            require = str(error)
            if expected not in require:
                raise AssertionError(name+': unexpected refusal '+require) from error
            (out/(name+'.log')).write_text(require+'\n')
            checks.append({'name': name, 'accepted': False, 'expected_refusal': expected,
                           'actual_refusal': require, 'fully_rehashed': True})
        else:
            raise AssertionError('False numerical claim accepted: '+name)
    result = {'schema': 1, 'status': 'native-awq-numerical-guards-checked',
              'accepted': 1, 'rejected': len(controls), 'gpu_trials': 0, 'model_calls': 0,
              'source_certificates': 0, 'original_paper_fully_reproduced': False, 'checks': checks}
    write(out/'results.json', result)
    shutil.copyfile(Path(__file__), out/'checker.py')
    write(out/'manifest.json', {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    print(json.dumps({k: result[k] for k in ('status', 'accepted', 'rejected')}))


if __name__ == '__main__':
    main()
