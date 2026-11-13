"""Fail-closed and semantic-mutation controls for the compiled numerical audit."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import struct
import subprocess
import sys
import time

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--module', required=True, type=Path)
parser.add_argument('--output', required=True, type=Path)
parser.add_argument('--lean', required=True)
arguments = parser.parse_args()
MODULE = arguments.module.resolve()
OUT = arguments.output.resolve()
OUT.mkdir(exist_ok=False)
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
bindings = {name: sha(MODULE/name) for name in
            ('BenchmarkRealAudit.lean', 'BenchmarkRealAudit.olean', 'BenchmarkFloatAudit.lean', 'BenchmarkFloatAudit.olean')}
environment = dict(os.environ, **json.loads((MODULE/'environment.json').read_text()))
for key in ('CUDA_VISIBLE_DEVICES', 'HIP_VISIBLE_DEVICES', 'ROCR_VISIBLE_DEVICES'):
    environment[key] = ''
HEADER = 'import BenchmarkFloatAudit\nset_option maxRecDepth 10000\nset_option maxHeartbeats 2000000\n'
SIGNATURE = ('def spec {α : Type} (ops : LarkNonlinear.Ops α) '
             '(input : Nat → Nat → α) : List α := ')
positive = '[ops.add (input 1 0) (ops.literal 1 1)]'
data = {'schema': 1, 'buffers': [[], [str(struct.unpack('<Q', struct.pack('<d', .25))[0])]]}
cases = [
    ('positive', positive, '0', data, None, {}),
    ('semantic-doubling', '[ops.mul (ops.literal 2 1) (ops.add (input 1 0) (ops.literal 1 1))]',
     '0', data, 'numerical-mismatch', {}),
    ('wrong-type', '[1]', '0', data, 'reference-audit expected polymorphic Ops reference',
     {'signature': SIGNATURE.replace(': List α', ': List Nat')}),
    ('output-index', positive, '1', data, 'reference-audit output index out of bounds', {}),
    ('input-buffer', '[input 2 0]', '0', data, 'reference-audit input index out of bounds', {}),
    ('input-offset', '[input 1 1]', '0', data, 'reference-audit input index out of bounds', {}),
    ('zero-literal-denominator', '[ops.literal 1 0]', '0', data,
     'reference-audit zero denominator', {}),
    ('zero-division-denominator', '[ops.div (ops.literal 1 1) (ops.literal 0 1)]', '0', data,
     'reference-audit zero denominator', {}),
    ('negative-sqrt', '[ops.rsqrt (ops.literal (-1) 1)]', '0', data,
     'reference-audit negative square-root input', {}),
    ('nonfinite-input', positive, '0', {'schema': 1, 'buffers': [[], ['9218868437227405312']]},
     'reference-audit non-finite input', {}),
    ('nonfinite-intermediate', '[ops.exp (ops.literal 1000000 1)]', '0', data,
     'reference-audit non-finite intermediate', {}),
    ('unknown-input-schema', positive, '0', dict(data, schema=2),
     'reference-audit unknown input schema', {}),
    ('duplicate-output', positive, '0,0', data, 'reference-audit duplicate output index', {}),
    ('empty-output', positive, '', data, 'reference-audit empty output selection', {}),
    ('unsupported-float-operation',
     '[ops.literal (Int.ofNat ((Float.exp (0 : Float)).toUInt64.toNat)) 1]', '0', data,
     'reference-audit unsupported declaration: Float.exp', {}),
    ('unregistered-helper', '[ops.literal (Int.ofNat Unregistered.number) 1]', '0', data,
     'reference-audit unsupported declaration owner: Unregistered.number',
     {'prefix': 'def Unregistered.number : Nat := 1\n'}),
    ('unsafe-reference', positive, '0', data,
     'reference-audit unsafe declaration: LarkCertificate.spec', {'signature': 'unsafe '+SIGNATURE}),
    ('injected-entrypoint', positive, '0', data, 'reference-audit unsupported reference entrypoint',
     {'term': '(fun {α : Type} (ops : LarkNonlinear.Ops α) (input : Nat → Nat → α) => LarkCertificate.spec ops input)'}),
]
report = {'schema': 1, 'status': 'compiled-numerical-auditor-controls-incomplete',
          'module_bindings': bindings, 'driver_sha256': sha(Path(__file__)), 'controls': [],
          'new_certificates': 0, 'original_paper_fully_reproduced': False}
for name, body, selection, inputs, expected, options in cases:
    directory = OUT/name
    directory.mkdir()
    (directory/'Input.json').write_text(json.dumps(inputs)+'\n')
    main = HEADER+options.get('prefix', '')+'namespace LarkCertificate\n'
    main += options.get('signature', SIGNATURE)+body+'\nend LarkCertificate\n'
    main += ('benchmark_audit_float '+options.get('term', '@LarkCertificate.spec')+
             ' from "Input.json" at ['+selection+']\n')
    (directory/'Main.lean').write_text(main)
    start = time.monotonic()
    run = subprocess.run([arguments.lean, 'Main.lean'], cwd=directory,
                         env=environment, capture_output=True, text=True, timeout=180)
    log = run.stdout+run.stderr
    (directory/'lean.log').write_text(log)
    if 'PANIC' in log or 'stacktrace:' in log:
        raise ValueError('Interpreter panic in control: '+name)
    row = {'control': name, 'exit_code': run.returncode, 'seconds': time.monotonic()-start,
           'main_sha256': sha(directory/'Main.lean'), 'input_sha256': sha(directory/'Input.json'),
           'log_sha256': sha(directory/'lean.log')}
    records = [json.loads(line.split('LARK_SPEC_AUDIT ', 1)[1]) for line in log.splitlines()
               if 'LARK_SPEC_AUDIT ' in line]
    if expected is None or expected == 'numerical-mismatch':
        if run.returncode or 'error:' in log or len(records) != 1:
            raise ValueError('Control did not evaluate: '+str(directory))
        value = struct.unpack('<d', struct.pack('<Q', int(records[0]['float64_bits'])))[0]
        matched = abs(value-1.25) <= 1e-10+1e-10*1.25
        if matched != (expected is None):
            raise ValueError('Semantic mutation was not detected: '+name)
        row.update(outcome='matched' if matched else 'numerical-mismatch-detected',
                   lean_float64=value, independent_expected=1.25)
    else:
        if run.returncode == 0 or expected not in log or records:
            raise ValueError('Named refusal missing: '+str(directory))
        row.update(outcome='refused', expected_refusal=expected)
    report['controls'].append(row)
    (OUT/'results.json').write_text(json.dumps(report, indent=2)+'\n')
    print(json.dumps({'control': name, 'outcome': row['outcome']}), flush=True)
if bindings != {name: sha(MODULE/name) for name in bindings}:
    raise ValueError('Frozen module changed during controls')
report.update(status='compiled-numerical-auditor-controls-passed',
              positive_controls=1, negative_controls=len(cases)-1)
(OUT/'results.json').write_text(json.dumps(report, indent=2)+'\n')
