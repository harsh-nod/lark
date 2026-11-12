"""Fail-closed and semantic-mutation controls for the separate numerical auditor."""

import json
from pathlib import Path
import struct
import subprocess
import time


HEADER = ('import SpecAudit\nset_option maxRecDepth 10000\n'
          'set_option maxHeartbeats 2000000\n')


def run_controls(lean, environment, output):
    output = Path(output)
    output.mkdir(parents=True, exist_ok=False)
    bits = str(struct.unpack('<Q', struct.pack('<d', .25))[0])
    data = {'schema':1, 'buffers':[[], [bits]]}
    term = '([LarkSpecAudit.input 1 0 + 1] : List ℝ)'
    cases = [
        ('positive', term, 0, data, None),
        ('semantic-doubling', term+'.map (fun x => 2*x)', 0, data, 'numerical-mismatch'),
        ('unsupported-operation', term+'.map Real.sin', 0, data,
         'reference-audit unsupported declaration: Real.sin'),
        ('wrong-element-type', '([1,2] : List Nat)', 0, data,
         'reference-audit expected List Real'),
        ('output-index', term, 1, data, 'reference-audit output index out of bounds'),
        ('input-buffer', '([LarkSpecAudit.input 2 0] : List ℝ)', 0, data,
         'reference-audit input index out of bounds'),
        ('input-offset', '([LarkSpecAudit.input 1 1] : List ℝ)', 0, data,
         'reference-audit input index out of bounds'),
        ('zero-denominator', '([(1:ℝ)/0] : List ℝ)', 0, data,
         'reference-audit zero denominator'),
        ('negative-sqrt', '([Real.sqrt (-1)] : List ℝ)', 0, data,
         'reference-audit negative square-root input'),
        ('nonfinite-input', term, 0, {'schema':1,'buffers':[[],['9218868437227405312']]},
         'reference-audit non-finite input'),
        ('nonfinite-intermediate', '([Real.exp 1000000] : List ℝ)', 0, data,
         'reference-audit non-finite intermediate'),
        ('unknown-input-schema', term, 0, dict(data, schema=2),
         'reference-audit unknown input schema'),
        ('noncanonical-add',
         '([@HAdd.hAdd ℝ ℝ ℝ ⟨fun a b => a*b⟩ (LarkSpecAudit.input 1 0) 2] : List ℝ)',
         0, data, 'reference-audit unsupported primitive instance'),
        ('noncanonical-literal', '([@OfNat.ofNat ℝ 1 ⟨(2:ℝ)⟩] : List ℝ)',
         0, data, 'reference-audit unsupported primitive instance'),
        ('noncanonical-append',
         '(@HAppend.hAppend (List ℝ) (List ℝ) (List ℝ) ⟨fun _ ys => ys⟩ [1] [2])',
         0, data, 'reference-audit unsupported primitive instance'),
    ]
    results = []
    for name, expression, index, inputs, expected in cases:
        directory = output/name
        directory.mkdir()
        (directory/'Input.json').write_text(json.dumps(inputs)+'\n')
        (directory/'Main.lean').write_text(
            HEADER+f'audit_spec ({expression}) from "Input.json" at {index}\n')
        start = time.monotonic()
        run = subprocess.run([lean, 'Main.lean'], cwd=directory, env=environment,
                             capture_output=True, text=True, timeout=180)
        log = run.stdout+run.stderr
        (directory/'lean.log').write_text(log)
        row = {'control':name, 'exit_code':run.returncode,
               'seconds':time.monotonic()-start}
        if expected is None or expected == 'numerical-mismatch':
            if run.returncode or 'error:' in log:
                raise ValueError('Control did not evaluate: '+str(directory))
            values = [json.loads(line.split('LARK_SPEC_AUDIT ',1)[1])
                      for line in log.splitlines() if 'LARK_SPEC_AUDIT ' in line]
            if len(values) != 1:
                raise ValueError('Control must produce exactly one scalar: '+name)
            value = struct.unpack('<d', struct.pack('<Q', int(values[0]['float64_bits'])))[0]
            # An independent toy arithmetic oracle tests the same comparison
            # used for production results. It is not a copied kernel formula.
            matched = abs(value-1.25) <= 1e-10+1e-10*1.25
            if matched != (expected is None):
                raise ValueError('Numerical mutation was not detected: '+name)
            row.update(outcome='matched' if matched else 'numerical-mismatch-detected',
                       lean_float64=value, independent_expected=1.25)
        else:
            if run.returncode == 0 or expected not in log or 'LARK_SPEC_AUDIT ' in log:
                raise ValueError('Expected named refusal was not observed: '+str(directory))
            row.update(outcome='refused', expected_refusal=expected)
        results.append(row)
    report = {'schema':1, 'status':'numerical-auditor-controls-passed',
              'positive_controls':1, 'negative_controls':len(results)-1,
              'controls':results, 'new_certificates':0}
    (output/'results.json').write_text(json.dumps(report, indent=2)+'\n')
    return report
