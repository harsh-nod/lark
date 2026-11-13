"""Focused controls for bit-preserving caches and exact source-call matching."""
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
options = parser.parse_args()
ROOT = options.module.resolve()
OUT = options.output.resolve()
OUT.mkdir(exist_ok=False)
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
bindings = {name: sha(ROOT/name) for name in
            ('BenchmarkRealAudit.lean', 'BenchmarkRealAudit.olean', 'BenchmarkFloatAudit.lean', 'BenchmarkFloatAudit.olean')}
environment = dict(os.environ, **json.loads((ROOT/'environment.json').read_text()))
HEADER = ('import BenchmarkFloatAudit\nset_option maxRecDepth 10000\n'
          'set_option maxHeartbeats 2000000\nopen Lean Meta Elab\n')
def scalar_probe(term):
    return HEADER+'''elab "#probe_cache" : command => do
  match '''+term+''' with
  | .error reason => throwError reason
  | .ok value => logInfo m!"LARK_CACHE_CONTROL {value.toBits.toNat}"
#probe_cache
'''

cases = [
    ('signed-zero', scalar_probe('LarkBenchmarkFloatAudit.scoreAt #[Float.ofBits (UInt64.ofNat 9223372036854775808)] 0'),
     None, '9223372036854775808'),
    ('cache-index', scalar_probe('LarkBenchmarkFloatAudit.scoreAt #[0.25] 1'),
     'reference-audit materialized score index out of bounds', None),
    ('empty-cache', scalar_probe('LarkBenchmarkFloatAudit.scoreAt #[] 0'),
     'reference-audit materialized score index out of bounds', None),
    ('nonfinite-cache', scalar_probe('LarkBenchmarkFloatAudit.scoreAt #[Float.ofBits (UInt64.ofNat 9218868437227405312)] 0'),
     'reference-audit non-finite intermediate', None),
    ('callback-error', HEADER+'''elab "#probe_callback" : command => do
  match LarkBenchmarkFloatAudit.materialize 3 (fun i =>
      if i=1 then .error "reference-audit injected score failure" else .ok 0.25) with
  | .error reason => throwError reason
  | .ok _ => throwError "unexpected callback success"
#probe_callback
''', 'reference-audit injected score failure', None),
]
repository = Path(__file__).resolve().parents[2]
sys.path.insert(0,str(repository))
from lark_kernels import attention
case = repository/'reproduction/attention/cases/dense/hip'
sources = {path.name.replace('.hip','.cu'):path.read_text()
           for path in case.iterdir() if path.is_file()}
rendered = attention.render(*attention.prepare(sources))
block = rendered[rendered.rindex('namespace LarkCertificate'):]
block = block[:block.index('theorem segmentation_data')]
prefix = HEADER+block
body = '''open Lean Meta Elab
elab "#probe_source" : command => Command.liftTermElabM do
  withLocalDeclD `buffers (mkConst ``LarkBenchmarkFloatAudit.Inputs) fun inputVariable => do
    let scoreType ← Term.elabType (← `(Array Float))
    withLocalDeclD `scores scoreType fun scoreVariable => do
      let shape := mkConst `LarkCertificate.shape
      let inputFunction := mkApp (mkConst ``LarkBenchmarkFloatAudit.checkedInput) inputVariable
      REPLACEMENT
      let expression := mkAppN (mkConst ``LarkAttention.spec)
        #[mkConst ``LarkBenchmarkFloatAudit.Checked,shapeArgument,operationArgument,inputArgument]
      let (selected,_) ← (LarkBenchmarkRealAudit.listAt expression 0).run #[] |>.run {}
      let _ ← LarkBenchmarkFloatAudit.replaceScores selected shape inputFunction scoreVariable
      throwError "unexpected source replacement success"
#probe_source
end LarkCertificate
'''
variants = {
    'different-ops': '''let operationArgument ← Term.elabTerm
        (← `({ LarkBenchmarkFloatAudit.ops with add := LarkBenchmarkFloatAudit.ops.sub })) none
      Term.synthesizeSyntheticMVarsNoPostponing
      let operationArgument ← instantiateMVars operationArgument
      let shapeArgument := shape
      let inputArgument := inputFunction''',
    'different-shape-expression': '''let shapeArgument ← mkAppM ``id #[shape]
      let operationArgument := mkConst ``LarkBenchmarkFloatAudit.ops
      let inputArgument := inputFunction''',
    'different-input-expression': '''let shifted ← withLocalDeclD `buffer (mkConst ``Nat) fun b => do
        withLocalDeclD `offset (mkConst ``Nat) fun i => do
          let position ← mkAppM ``Nat.add #[i,mkRawNatLit 1]
          mkLambdaFVars #[b,i] (mkAppN (mkConst ``LarkBenchmarkFloatAudit.checkedInput)
            #[inputVariable,b,position])
      let operationArgument := mkConst ``LarkBenchmarkFloatAudit.ops
      let shapeArgument := shape
      let inputArgument := shifted''',
}
for name, replacement in variants.items():
    cases.append((name, prefix+body.replace('REPLACEMENT', replacement),
                  'reference-audit unsupported score call for materialization', None))
report = {'status': 'materialization-controls-incomplete', 'module_bindings': bindings,
          'driver_sha256': sha(Path(__file__)), 'controls': [], 'new_certificates': 0,
          'original_paper_fully_reproduced': False}
for name, source, expected_error, expected_bits in cases:
    directory = OUT/name; directory.mkdir()
    (directory/'Main.lean').write_text(source)
    start = time.monotonic()
    run = subprocess.run([options.lean,'Main.lean'], cwd=directory,
                         env=environment, capture_output=True, text=True, timeout=180)
    log = run.stdout+run.stderr; (directory/'lean.log').write_text(log)
    if 'PANIC' in log or 'stacktrace:' in log:
        raise ValueError('Interpreter panic: '+name)
    if expected_error:
        if run.returncode == 0 or expected_error not in log or 'LARK_CACHE_CONTROL' in log:
            raise ValueError('Expected refusal missing: '+str(directory))
        outcome = 'refused'
    else:
        if run.returncode or 'LARK_CACHE_CONTROL '+expected_bits not in log:
            raise ValueError('Cache changed Float64 bits: '+str(directory))
        outcome = 'bit-identical'
    report['controls'].append({'control':name,'exit_code':run.returncode,
                               'outcome':outcome,'seconds':time.monotonic()-start,
                               'main_sha256':sha(directory/'Main.lean'),
                               'log_sha256':sha(directory/'lean.log')})
    (OUT/'results.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({'control':name,'outcome':outcome}),flush=True)
assert bindings == {name: sha(ROOT/name) for name in bindings}
report.update(status='materialization-controls-passed', positive_controls=1,
              negative_controls=len(cases)-1)
(OUT/'results.json').write_text(json.dumps(report,indent=2)+'\n')
