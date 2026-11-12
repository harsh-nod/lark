"""Reject fully rehashed AWQ proof-scope changes before archive extraction."""

import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

from replay_native_real import sha


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lean-bin', type=Path, required=True)
    parser.add_argument('--dependency-project', type=Path, required=True)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=False)
    mutations = {
        'invented-ieee-proof': ('ieee_equivalence_proved', True),
        'invented-error-bound': ('floating_point_error_bound_proved', True),
        'invented-paper-completion': ('original_paper_fully_reproduced', True),
        'invented-model-calls': ('model_calls', 1),
        'invented-gpu-trials': ('gpu_trials', 1),
        'boolean-model-calls': ('model_calls', False),
        'unknown-report-field': ('unsupported_extra_field', False),
        'boolean-schema': ('schema', True),
        'boolean-module-count': ('local_lean_modules', True),
        'wrong-module-count': ('local_lean_modules', 82),
        'wrong-real-module-count': ('local_real_modules', 2),
        'boolean-certificate-count': ('source_certificates', True),
        'wrong-certificate-count': ('source_certificates', 3),
        'wrong-export-cases': ('export_cases', ['m17_k32_n64']),
        'wrong-source-hashes': ('source_sha256', {}),
        'wrong-shape-contract': ('shape_contract', 'all positive dimensions'),
        'wrong-model-profile': ('model_profile', 'native-awq-gemm-real-v25'),
        'wrong-block-size': ('block', 32),
        'boolean-block-size': ('block', True),
        'wrong-physical-wave': ('physical_warp', 32),
        'missing-original-fuel': ('original_fuel_preserved', False),
        'missing-parameterized-certificate': ('parameterized_source_certificate', False),
        'missing-whole-launch': ('whole_kernel_execution_proved', False),
        'missing-actual-race-freedom': ('actual_trace_race_freedom_proved', False),
        'missing-source-reference': ('source_reference_equality_proved', False),
        'wrong-false-lean-count': ('false_lean_claims_rejected', 13),
        'wrong-refusal-count': ('false_claims_rejected', 37),
        'missing-library-audits': ('library_axiom_audits', {}),
        'missing-main-audits': ('main_axiom_audits', {}),
        'missing-export-audits': ('export_axiom_audits', {}),
        'missing-control-receipts': ('checks', []),
    }
    original = json.loads((args.packet/'results.json').read_text())
    for name, declaration in (
        ('missing-source-correct-audit', 'LarkNativeAwqGemm.source_correct'),
        ('missing-actual-race-audit', 'LarkNativeAwqGemm.initialized_whole_grid_race_free'),
        ('missing-canonical-correct-audit', 'LarkReal.NativeAwqGemm.canonical_correct'),
    ):
        changed = dict(original['library_axiom_audits'])
        changed.pop(declaration)
        changed['Invented.replacement'] = ''
        mutations[name] = ('library_axiom_audits', changed)
    for name, update in (
        ('accepted-negative-control', {'accepted': True}),
        ('timed-out-negative-control', {'timed_out': True}),
        ('renamed-control-receipt', {'name': 'unexecuted-control'}),
        ('nonfinite-control-duration', {'seconds': float('inf')}),
    ):
        changed = [dict(item) for item in original['checks']]
        changed[8].update(update)
        mutations[name] = ('checks', changed)
    records = []
    with tempfile.TemporaryDirectory(prefix='lark-awq-real-stage-guards-') as temporary:
        base = Path(temporary)
        for name, (key, value) in mutations.items():
            packet, output = base/name, base/(name+'-replay')
            packet.mkdir()
            for path in args.packet.iterdir():
                if path.is_file():
                    shutil.copyfile(path, packet/path.name)
            report = json.loads((packet/'results.json').read_text())
            report[key] = value
            (packet/'results.json').write_text(json.dumps(report, indent=2)+'\n')
            manifest = json.loads((packet/'manifest.json').read_text())
            manifest['results.json'] = sha(packet/'results.json')
            (packet/'manifest.json').write_text(json.dumps(manifest, indent=2)+'\n')
            run = subprocess.run([
                sys.executable, str(Path(__file__).with_name('replay_native_real.py')),
                '--packet', str(packet), '--output', str(output),
                '--lean-bin', str(args.lean_bin), '--dependency-project', str(args.dependency_project),
            ], capture_output=True, text=True, timeout=30)
            log = run.stdout+run.stderr
            (args.output/(name+'.log')).write_text(log)
            if run.returncode == 0 or output.exists() or 'Unsupported AWQ real stage/scope metadata' not in log:
                raise ValueError('Wrong scope-guard outcome: '+name)
            records.append({'name': name, 'accepted': False, 'fully_rehashed': True,
                            'rejected_before_extraction': True})
    result = {
        'schema': 1, 'status': 'fully-rehashed-native-awq-real-claims-rejected-before-extraction',
        'checks': records, 'negative_controls': len(records), 'model_calls': 0, 'gpu_trials': 0,
        'original_paper_fully_reproduced': False,
        'source_packet_manifest_sha256': sha(args.packet/'manifest.json'),
        'replayer_sha256': sha(Path(__file__).with_name('replay_native_real.py')),
        'checker_sha256': sha(Path(__file__)),
    }
    (args.output/'results.json').write_text(json.dumps(result, indent=2)+'\n')
    shutil.copyfile(Path(__file__), args.output/'checker.py')
    (args.output/'manifest.json').write_text(json.dumps({
        p.name: sha(p) for p in sorted(args.output.iterdir()) if p.is_file()
    }, indent=2)+'\n')
    print(json.dumps({'status': result['status'], 'negative_controls': len(records)}))


if __name__ == '__main__':
    main()
