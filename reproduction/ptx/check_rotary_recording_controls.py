"""Reject coherently rehashed false RoPE records before any fresh Lean work."""

import argparse
import copy
import json
from pathlib import Path
import shutil
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import ptx_rotary_certificate as checker  # noqa: E402
from lark_kernels.ir import Refusal  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('recording', 'output', 'lean'):
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    BASE, ORIGINAL = checker.fresh_output(args.output), args.recording.resolve()
    checker.check_inventory(ORIGINAL)
    baseline = checker.read(ORIGINAL / 'results.json')
    BASE.mkdir()
    (BASE / 'driver.py').write_bytes(Path(__file__).read_bytes())
    changes = [
        ('boolean-development-count', {'source_bound_development_proofs': True}),
        ('boolean-module-count', {'owned_Lean_modules_freshly_compiled': True}),
        ('NVIDIA-execution-overclaim', {'nvidia_execution': True}),
        ('original-paper-overclaim', {'original_paper_fully_reproduced': True}),
        ('legacy-certificate-overclaim', {'new_registered_source_certificates': 1}),
        ('heartbeat-budget-increased', {'limits': {**checker.LIMITS, 'maxHeartbeats': 4000000}}),
        ('recursion-budget-increased', {'limits': {**checker.LIMITS, 'maxRecDepth': 20000}}),
        ('CUDA-fuel-increased', {'unchanged_CUDA_contract_fuel': [9, 1, 1, 1]}),
        ('boolean-CUDA-fuel', {'unchanged_CUDA_contract_fuel': [8, True, 1, 1]}),
        ('boolean-launch', {'launch': {'grid': 32768, 'block': True, 'warp': 32}}),
        ('claimed-owned-cache-reuse', {'old_owned_olean_cache_used': True}),
        ('missing-reference-denotation-audit', {}),
        ('missing-library-audit', {}),
        ('coherently-rehashed-tensor-AST', {}),
        ('coherently-rehashed-Main', {}),
        ('coherently-rehashed-captured-Python', {}),
        ('coherently-rehashed-forbidden-axiom-log', {}),
    ]
    results = []
    for label, fields in changes:
        case = BASE / label
        recording = case / 'recording'
        shutil.copytree(ORIGINAL, recording)
        report = copy.deepcopy(baseline)
        report.update(fields)
        if label == 'missing-reference-denotation-audit':
            report['axiom_audits'].pop('LarkPtxRotaryCertificate.reference_denotation')
        elif label == 'missing-library-audit':
            report['library_axiom_audits'].pop(next(iter(report['library_axiom_audits'])))
        elif label == 'coherently-rehashed-tensor-AST':
            tree = checker.read(recording / 'reference-ast.json')

            def mutate(node):
                if isinstance(node, list):
                    if node == ['input', 1]:
                        node[1] = True
                        return True
                    return any(mutate(child) for child in node)
                return False

            assert mutate(tree)
            checker.write(recording / 'reference-ast.json', tree)
            report['reference_ast_sha256'] = checker.sha((recording / 'reference-ast.json').read_bytes())
        elif label == 'coherently-rehashed-Main':
            path = recording / 'Main.lean'
            source = path.read_text()
            assert source.count('by decide') == 1
            path.write_text(source.replace('by decide', 'by rfl', 1))
            report['main_sha256'] = checker.sha(path.read_bytes())
        elif label == 'coherently-rehashed-captured-Python':
            name = 'python/ptx_rotary_certificate.py'
            path = recording / 'owned-sources' / name
            path.write_text(path.read_text() + '\nraise AssertionError("captured Python executed")\n')
            bindings = checker.read(recording / 'source-bindings.json')
            bindings[name] = checker.sha(path.read_bytes())
            checker.write(recording / 'source-bindings.json', bindings)
            report['source_bindings_sha256'] = checker.sha((recording / 'source-bindings.json').read_bytes())
        elif label == 'coherently-rehashed-forbidden-axiom-log':
            path = recording / 'Main.log'
            text = path.read_text()
            assert 'Quot.sound' in text
            path.write_text(text.replace('Quot.sound', 'sorryAx', 1))
            report['main_check']['log_sha256'] = checker.sha(path.read_bytes())
        checker.write(recording / 'results.json', report)
        checker.manifest(recording)
        destination = case / 'unexpected-fresh-replay'
        try:
            checker.check_export(recording, destination, args.lean)
        except Refusal as error:
            result = {'name': label, 'status': 'rejected-before-fresh-Lean-work',
                      'code': error.code, 'detail': error.detail,
                      'output_created': destination.exists(),
                      'complete_false_recording_manifest_sha256': checker.sha((recording / 'manifest.json').read_bytes())}
            assert not destination.exists(), label
        else:
            raise AssertionError('False recording unexpectedly accepted: ' + label)
        checker.write(case / 'results.json', result)
        checker.manifest(case)
        results.append(result)
    checker.write(BASE / 'results.json', {'status': 'all17-coherently-rehashed-RoPE-controls-rejected',
                  'checks': results, 'negative_controls': 17, 'fresh_Lean_checks': 0,
                  'GPU_trials': 0, 'model_calls': 0, 'all_false_payloads_retained': True,
                  'original_paper_fully_reproduced': False})
    checker.manifest(BASE)
    print(json.dumps({'status': 'all17-coherently-rehashed-RoPE-controls-rejected',
                      'negative_controls': 17, 'fresh_Lean_checks': 0}), flush=True)


if __name__ == '__main__':
    main()
