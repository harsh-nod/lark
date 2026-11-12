"""Reject fully rehashed false AWQ stage claims before creating a proof project."""

import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def write(path, value):
    path.write_text(json.dumps(value, indent=2)+'\n')


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lean-bin', type=Path, required=True)
    args = parser.parse_args()
    packet, out = args.packet.resolve(), args.output.resolve()
    out.mkdir(parents=True, exist_ok=False)
    original = json.loads((packet/'results.json').read_text())
    stage = original['stage']
    assert stage in ('a-staging-v3', 'lane-staging-v4', 'block-staging-v5')
    manifest = json.loads((packet/'manifest.json').read_text())
    for name, digest in manifest.items():
        assert sha(packet/name) == digest
    controls = []
    for name in ('whole_kernel_execution_proved', 'actual_whole_trace_race_freedom_proved',
                 'source_reference_equality_proved', 'ieee_equivalence_proved', 'original_paper_fully_reproduced'):
        controls.append(('invented-'+name, name, True, 'Unsupported component claim'))
    later = ('matrix_execution_proved', 'k_loop_execution_proved')
    if stage == 'a-staging-v3':
        later += ('b_staging_execution_proved',)
    elif stage == 'lane-staging-v4':
        later += ('block_staging_execution_proved', 'middle_block_barrier_resumption_proved')
    else:
        later += ('matrix_fragment_scalar_loads_executed',)
    for name in later:
        controls.append(('invented-'+name, name, True, 'Unsupported later-stage claim'))
    controls += [
        ('invented-certificate', 'source_certificates', 1, 'Component packet scope'),
        ('boolean-certificate-count', 'source_certificates', False, 'Component packet scope'),
        ('invented-model-call', 'model_calls', 1, 'Component packet scope'),
        ('boolean-model-call-count', 'model_calls', False, 'Component packet scope'),
        ('invented-gpu-trial', 'gpu_trials', 1, 'Component packet scope'),
        ('invented-audit-count', 'axiom_audit_occurrences', original['axiom_audit_occurrences']+1, 'Component packet scope'),
        ('wrong-owned-module-count', 'owned_lean_modules', original['owned_lean_modules']-1, 'Component packet scope'),
        ('wrong-a-stage-cell-count', 'a_staging_cells_per_lane', 7, 'A staging shape/count scope'),
        ('wrong-a-stage-step-count', 'a_staging_scalar_steps', [36, 36], 'A staging shape/count scope'),
        ('erased-a-stage-values', 'a_staging_shared_values_proved', False, 'A staging claim'),
        ('unknown-stage', 'stage', 'complete-awq-v99', 'Unknown component stage'),
        ('missing-library-audit', 'drop-library', None, 'Stage audit coverage'),
        ('missing-source-stage-audit', 'rename-source', None, 'Stage audit coverage'),
    ]
    if stage in ('lane-staging-v4', 'block-staging-v5'):
        controls += [
            ('wrong-b-chunk-count', 'b_staging_chunks_per_lane', [4, 9], 'Lane staging shape/count/order scope'),
            ('wrong-b-cell-count', 'b_staging_cells_per_chunk', 7, 'Lane staging shape/count/order scope'),
            ('wrong-b-step-count', 'b_staging_scalar_steps', [157, 314], 'Lane staging shape/count/order scope'),
            ('raised-lane-fuel', 'lane_staging_fuel', 513, 'Lane staging shape/count/order scope'),
            ('wrong-lane-step-count', 'lane_staging_scalar_steps', [194, 350], 'Lane staging shape/count/order scope'),
            ('regrouped-staging-order', 'lane_staging_order', 'all-a-then-all-b', 'Lane staging shape/count/order scope'),
            ('erased-b-values', 'b_staging_shared_values_proved', False, 'Lane staging claim'),
            ('erased-lane-execution', 'lane_staging_source_execution_proved', False, 'Lane staging claim'),
            ('erased-middle-barrier', 'middle_barrier_reached_per_lane_proved', False, 'Lane staging claim'),
        ]
    if stage == 'block-staging-v5':
        for field in ('block_staging_execution_proved', 'middle_block_barrier_resumption_proved',
                      'actual_initial_through_middle_barrier_proved', 'staging_dense_shared_tiles_proved',
                      'native_fragment_shared_values_proved'):
            controls.append(('erased-'+field, field, False, 'Block staging claim'))
    checks = []
    reader = Path(__file__).with_name('replay_components.py')
    for name, field, value, expected in controls:
        folder = out/name
        folder.mkdir()
        for file in manifest:
            shutil.copyfile(packet/file, folder/file)
        metadata = json.loads(json.dumps(original))
        if field == 'drop-library':
            metadata['library_axiom_audits'].pop(next(iter(metadata['library_axiom_audits'])))
        elif field == 'rename-source':
            audit = metadata['source_axiom_audits']['m17_k32_n64']
            audit['AwqSource.unrelated_claim'] = audit.pop(
                'AwqSource.initial_through_staging' if stage == 'block-staging-v5' else
                'AwqSource.lane_staging_execution' if stage == 'lane-staging-v4' else 'AwqSource.a_staging_execution')
        else:
            metadata[field] = value
        write(folder/'results.json', metadata)
        write(folder/'manifest.json', {file: sha(folder/file) for file in manifest})
        replay = folder/'proof-must-not-be-created'
        result = subprocess.run([sys.executable, str(reader), '--packet', str(folder),
                                 '--archive', str(folder/'source-project.tar.gz'), '--output', str(replay),
                                 '--lean-bin', str(args.lean_bin.resolve())], capture_output=True, text=True, timeout=20)
        log = result.stdout+result.stderr
        assert result.returncode != 0 and expected in log, name+'\n'+log
        assert not replay.exists(), name+' was not refused before extraction'
        (out/(name+'.log')).write_text(log)
        checks.append({'name': name, 'accepted': False, 'fully_rehashed': True,
                       'expected_refusal': expected, 'refused_before_project_creation': True})
    report = {'schema': 1, 'status': 'native-awq-'+stage+'-scope-guards-checked', 'stage': stage,
              'rejected': len(checks), 'all_refused_before_extraction': True, 'proof_builds_started': 0,
              'source_certificates': 0, 'gpu_trials': 0, 'model_calls': 0,
              'original_paper_fully_reproduced': False, 'checks': checks}
    write(out/'results.json', report)
    shutil.copyfile(Path(__file__), out/'checker.py')
    write(out/'manifest.json', {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
    print(json.dumps({k: report[k] for k in ('status', 'rejected', 'proof_builds_started')}))


if __name__ == '__main__':
    main()
