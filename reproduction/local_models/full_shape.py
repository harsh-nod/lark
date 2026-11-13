"""Prepare bounded, source-bound proof tasks for all full-size benchmark families.

This preparation makes no model calls. SDK proofs are positive controls only;
they are excluded from the model-visible request. Actual model experiments must
archive their own requests, responses, checker receipts and runtime identities.
"""

import argparse
import hashlib
import importlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import certificate, real_backend
from reproduction.benchmark_specification_validation import study as benchmark
from reproduction.specification_validation import study as references

SLOTS = ('segmentation_data', 'segmentation', 'race_free', 'segment_equivalence')
TARGET = 'LarkReal.BenchmarkReferenceImports'
LIMITS = {'maxRecDepth': 10000, 'maxHeartbeats': 2000000, 'lean_timeout_seconds': 180}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(content):
    return hashlib.sha256(content).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def validate_proofs(proofs):
    require(isinstance(proofs, dict) and set(proofs) == set(SLOTS),
            'Exactly four full-shape proof slots are required')
    certificate.validate_proofs({name: proofs[name] for name in certificate.DEFAULT_PROOFS})
    # Reuse the same bounded tactic validator for the additional execution slot.
    certificate.validate_proofs({name: proofs['segmentation'] for name in certificate.DEFAULT_PROOFS})


def sdk_case(case):
    key, module, directory = case
    folder = ROOT/'reproduction'/directory
    sdk = importlib.import_module('lark_kernels.'+module)
    owned = {p.name: p.read_bytes() for p in folder.iterdir() if p.is_file()}
    text = lambda name: owned[name].decode()
    if module == 'feedforward':
        args = sdk.prepare(*(text(n) for n in ('up.hip', 'down.hip', 'reference.py',
                                               'up-task.json', 'down-task.json')))
    elif module in ('attention', 'swiglu'):
        args = sdk.prepare({n.replace('.hip', '.cu'): b.decode() for n, b in owned.items()})
    else:
        args = sdk.prepare(*(text(n) for n in ('kernel.hip', 'reference.py', 'task.json')))
    rendered = sdk.render(*args)
    block = rendered[rendered.rindex('namespace LarkCertificate'):]
    # Keep legacy imported libraries intact. Every generated Main uses the fixed
    # new limits, regardless of old settings in a renderer's final block.
    block = re.sub(r'(?m)^set_option (?:maxRecDepth|maxHeartbeats) [0-9]+\s*$', '', block)
    require('set_option' not in block, 'Unexpected local option in SDK certificate block')
    return block, {str((folder/n).relative_to(ROOT)): b for n, b in owned.items()}


def proof_spans(block):
    declarations = list(re.finditer(r'(?m)^(?:theorem|def|#print axioms|end LarkCertificate)\b', block))
    result = {}
    for name in SLOTS:
        matches = list(re.finditer(r'(?m)^theorem '+re.escape(name)+r'\b', block))
        require(len(matches) == 1, 'Ambiguous SDK proof declaration: '+name)
        start = matches[0].start()
        end = next((m.start() for m in declarations if m.start() > start), len(block))
        declaration = block[start:end]
        require(declaration.count(':= by') == 1, 'Unexpected SDK tactic declaration: '+name)
        body = start+declaration.index(':= by')+3
        result[name] = {'start': body, 'end': end, 'type': block[start:body],
                        'sdk_positive_control': block[body:end].strip()}
    return result


def render(block, proofs):
    validate_proofs(proofs)
    spans = proof_spans(block)
    result = block
    for name in sorted(SLOTS, key=lambda n: spans[n]['start'], reverse=True):
        span = spans[name]
        result = result[:span['start']]+proofs[name].strip()+'\n\n'+result[span['end']:]
    return ('import '+TARGET+'\nset_option maxRecDepth 10000\n'
            'set_option maxHeartbeats 2000000\n'+result)


def freeze_sources(output, selected, libraries):
    paths = set((ROOT/'lark_kernels').glob('*.py'))
    paths.update(ROOT/'reproduction/local_models'/n for n in ('full_shape.py', 'client.py'))
    paths.update(ROOT/n for n in ('reproduction/benchmark_specification_validation/study.py',
                                 'reproduction/benchmark_specification_validation/BenchmarkImports.lean',
                                 'reproduction/specification_validation/study.py',
                                 'lean-real/lean-toolchain', 'lean-real/lake-manifest.json'))
    for _, _, directory in selected:
        paths.update(p for p in (ROOT/'reproduction'/directory).iterdir() if p.is_file())
    sources = {str(p.relative_to(ROOT)): p.read_bytes() for p in paths}
    for name, content in libraries.items():
        name = ('lean-real/' if name.startswith('LarkReal/') else 'lean/')+name
        require(name not in sources or sources[name] == content, 'Conflicting library source')
        sources[name] = content
    for name, content in sorted(sources.items()):
        destination = output/'source'/name
        destination.parent.mkdir(parents=True, exist_ok=True)
        destination.write_bytes(content)
    manifest = {n: digest(b) for n, b in sorted(sources.items())}
    write(output/'source-manifest.json', manifest)
    return manifest


def prepare(output, lean, selected):
    require(not any((p/'.git').exists() for p in (output, *output.parents)),
            'Preparation outputs must be outside Git')
    output.mkdir(parents=True, exist_ok=False)
    libraries = benchmark.reference_libraries(references)
    bindings = freeze_sources(output, selected, libraries)
    version = subprocess.check_output([str(lean), '--version'], text=True, timeout=30).strip()
    require(version.startswith('Lean (version 4.19.0,'), 'Lean 4.19.0 is required')
    report = {'schema': 1, 'status': 'full-shape-fixture-preparation-in-progress',
              'protocol': 'full-shape-four-slots-v1', 'lean_version': version,
              'lean_binary_sha256': digest(lean.read_bytes()),
              'source_manifest_sha256': digest((output/'source-manifest.json').read_bytes()),
              'source_files': len(bindings), 'limits': LIMITS, 'proof_slots': list(SLOTS),
              'model_calls': 0, 'gpu_trials': 0, 'new_certificates': 0,
              'original_paper_fully_reproduced': False, 'cases': [],
              'scope': 'Independent full-shape proof-task preparation. SDK tactic bodies are positive controls, never model successes; masked proofs must fail. No source certificate is issued.'}
    write(output/'results.json', report)
    cache, environment = real_backend.prepare(libraries, str(lean), 600, target=TARGET)
    marker = json.loads((cache/'checked-build.json').read_text())
    write(output/'imports.json', {'target': TARGET, 'source_checked_cache': str(cache),
                                 'sources': marker['sources'], 'compiled': marker['compiled'],
                                 'sdk_import_cache_reused_or_source_checked': True,
                                 'cold_rebuild_of_all_imports_claimed': False})
    catalogue = {n: {'bytes': len(b), 'sha256': digest(b)} for n, b in sorted(libraries.items())}
    for case in selected:
        name = case[0]
        folder = output/'cases'/name
        folder.mkdir(parents=True)
        block, owned = sdk_case(case)
        spans = proof_spans(block)
        known = {n: spans[n]['sdk_positive_control'] for n in SLOTS}
        masked = {n: 'by fail' for n in SLOTS}
        (folder/'sdk-block.lean.txt').write_text(block)
        write(folder/'source-bindings.json', {n: digest(b) for n, b in sorted(owned.items())})
        request = {'schema': 1, 'case': name, 'proof_slots': list(SLOTS),
                   'immutable_main': render(block, masked), 'limits': LIMITS,
                   'theorem_types': {n: spans[n]['type'] for n in SLOTS},
                   'source_files': {n: b.decode() for n, b in sorted(owned.items())},
                   'available_lean_library_sources': catalogue,
                   'sdk_tactic_bodies_included': False,
                   'scope': 'Full-size independent source, four fixed proof slots, abstract scalar operations; original paper harness and kernels unavailable.'}
        write(folder/'request.json', request)
        row = {'case': name, 'request_sha256': digest((folder/'request.json').read_bytes()),
               'source_bindings_sha256': digest((folder/'source-bindings.json').read_bytes())}
        for label, proofs, wanted in [('sdk-positive', known, True), ('all-masked-negative', masked, False)]:
            destination = folder/label
            destination.mkdir()
            (destination/'Main.lean').write_text(render(block, proofs))
            ok, log = certificate.run_lean(destination, str(lean), 180, env=environment)
            (destination/'lean.log').write_text(log)
            require(ok is wanted and 'Lean timed out' not in log,
                    'Unexpected full-shape preparation outcome: '+name+'/'+label+'; see '+str(destination/'lean.log'))
            require(wanted or 'tactic \'fail\' failed' in log,
                    'Masked fixture did not fail at its proof hole: '+name)
            row[label] = {'accepted': ok, 'main_sha256': digest((destination/'Main.lean').read_bytes()),
                          'lean_log_sha256': digest(log.encode())}
        report['cases'].append(row)
        write(output/'results.json', report)
        print(json.dumps({'case': name, 'sdk_positive': True, 'masked_negative_rejected': True}), flush=True)
    report['status'] = 'full-shape-model-fixtures-prepared-and-baselines-checked'
    report['positive_lean_checks'] = report['masked_negative_lean_checks'] = len(selected)
    write(output/'results.json', report)
    write(output/'manifest.json', {str(p.relative_to(output)): digest(p.read_bytes())
                                   for p in sorted(output.rglob('*')) if p.is_file()})
    print(json.dumps({k: report[k] for k in ('status', 'positive_lean_checks',
                                           'masked_negative_lean_checks', 'model_calls')}))


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output', required=True, type=Path)
    parser.add_argument('--lean', required=True, type=Path)
    parser.add_argument('--case', action='append', choices=[c[0] for c in benchmark.CASES])
    args = parser.parse_args()
    binary = Path(certificate.lean_binary(str(args.lean)))
    selected = [c for c in benchmark.CASES if not args.case or c[0] in args.case]
    prepare(args.output.resolve(), binary, selected)


if __name__ == '__main__':
    main()
