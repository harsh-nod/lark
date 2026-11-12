import hashlib
import importlib.util
import json
from pathlib import Path
import shutil
import struct

ROOT = Path('/tmp/lark-elaborated-reference-audit-20261112')
RAW = Path('/tmp/lark-elaborated-reference-source-replay-v1-20261112')
PACKET = ROOT/'reproduction/specification_validation/results/production-real-v1'
PRIVATE = Path('/tmp/lark-elaborated-reference-packet-v1-20261112')
OUT = Path('/tmp/lark-elaborated-reference-source-replay-receipt-v1-20261112')
OUT.mkdir(exist_ok=False)
spec = importlib.util.spec_from_file_location('packet_audit',ROOT/'reproduction/specification_validation/packet.py')
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)
runtime = audit.read(RAW/'results.json')
audit.require(runtime['status'] == 'source-only-numerical-recomputation-passed'
              and runtime['fresh_lean_executions'] == 64, 'Fresh replay did not complete')
fresh = audit.read(RAW/'recomputed/results.json')
original = audit.read(PACKET/'results.json')
latest_check = audit.audit(RAW/'recomputed/source',RAW/'recomputed',fresh)
audit.require(fresh['source_bindings'] == original['source_bindings'], 'Fresh own source set differs')
audit.require(fresh['module_compilation']['source_sha256'] == original['module_compilation']['source_sha256'],
              'Numerical evaluator source differs')
shared = {}
for name in ('source.tar.gz','source-manifest.json','evidence.tar.gz','evidence-manifest.json','results.json'):
    audit.require((PRIVATE/name).read_bytes() == (PACKET/name).read_bytes(),
                  'Runtime/public packet scientific payload differs: '+name)
    shared[name] = audit.sha(PACKET/name)
input_equal, mains_equal, bit_differences = 0, 0, 0
max_difference = 0.
for old, new in zip(original['checks'],fresh['checks']):
    audit.require((old['case'],old['stratum']) == (new['case'],new['stratum']), 'Case order differs')
    audit.require(old['input_sha256'] == new['input_sha256'], 'Input bits differ')
    audit.require(old['main_sha256'] == new['main_sha256'], 'Elaborated Main source differs')
    input_equal += 1
    mains_equal += 1
    for x,y in zip(old['samples'],new['samples']):
        bit_differences += x['float64_bits'] != y['float64_bits']
        max_difference = max(max_difference,abs(x['lean_float64']-y['lean_float64']))
audit.require(input_equal == 48 and mains_equal == 48, 'Replay case matrix incomplete')
result = {'schema':1,'status':'production-reference-source-replay-passed',
          'families':10,'variants':12,'strata':4,'repeated_samples':240,
          'numerical_positive_controls':1,'numerical_negative_controls':14,
          'direct_numerical_lean_processes':64,'numerical_module_compiled_fresh':True,
          'source_files':len(fresh['source_bindings']),
          'identical_input_files':input_equal,'identical_main_files':mains_equal,
          'lean_float64_bit_differences':bit_differences,'max_lean_float64_difference':max_difference,
          'packet_manifest_sha256':audit.sha(PACKET/'manifest.json'),
          'runtime_packet_manifest_sha256':audit.sha(PRIVATE/'manifest.json'),
          'runtime_verifier_sha256':audit.sha(PRIVATE/'packet.py'),
          'final_verifier_sha256':audit.sha(ROOT/'reproduction/specification_validation/packet.py'),
          'identical_runtime_and_public_payload':shared,
          'measured_module_compilation':original['module_compilation'],
          'recomputed_module_compilation':fresh['module_compilation'],
          'final_verifier_audit':latest_check,
          'trusted_import_scope':'Pinned Mathlib and SDK reference-library imports were reused only after SDK source/compiled-cache validation. This is not a cold rebuild of every imported proof or of Mathlib.',
          'wrapper_delta_scope':'The runtime and published packets have identical source/evidence archives, manifests and measurement report. Only the top-level verifier and outer manifest changed; the final stricter verifier also passed on the actual recomputed source and evidence.',
          'model_calls':0,'gpu_trials':0,'new_certificates':0,
          'formal_ieee_or_error_theorem':False,'original_paper_fully_reproduced':False}
audit.write(OUT/'results.json',result)
for source,name in ((RAW/'results.json','runtime-replay.json'),
                    (RAW/'recomputed/results.json','recomputed-results.json'),
                    (RAW/'recompute.log','recompute.log'),
                    (RAW/'recomputed/compile.log','module-compilation.log'),
                    (Path(__file__),'driver.py'),
                    (ROOT/'reproduction/specification_validation/packet.py','packet.py')):
    shutil.copyfile(source,OUT/name)
audit.write(OUT/'manifest.json',{p.name:audit.sha(p) for p in sorted(OUT.iterdir()) if p.is_file()})
print(json.dumps({k:result[k] for k in ('status','repeated_samples','direct_numerical_lean_processes',
                                      'identical_input_files','lean_float64_bit_differences','max_lean_float64_difference')}))
