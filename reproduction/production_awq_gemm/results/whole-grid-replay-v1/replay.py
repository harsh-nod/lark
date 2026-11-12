"""Replay the standalone AWQ component archive without Git or an owned cache."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import tarfile
import time

CASES = ('m17_k32_n64', 'm17_k32_n128', 'm33_k64_n192', 'm33_k64_n256')
CONTROLS = ('wrong-matrix-operand', 'missing-first-barrier', 'missing-middle-barrier',
            'wrong-shared-a-stride', 'wrong-shared-b-stride', 'aliased-output-column')
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
BASE_MODELS = ('Nonlinear', 'MFMA', 'NativeAwqGemmAddress', 'NativeAwqGemmGlobal', 'NativeAwqGemmProgram',
               'NativeAwqGemmGeometry', 'NativeAwqGemmState', 'NativeAwqGemmPrefix')
INITIAL_MODELS = ('NativeAwqGemmIndexEval', 'NativeAwqGemmIndices', 'NativeAwqGemmInitRegisters',
                  'NativeAwqGemmInitial', 'NativeAwqGemmInitialBlock')
A_MODELS = ('NativeAwqGemmMemory', 'NativeAwqGemmAIndex', 'NativeAwqGemmAStore', 'NativeAwqGemmARound',
            'NativeAwqGemmALoop', 'NativeAwqGemmAStage', 'NativeAwqGemmAValues')
B_MODELS = ('NativeAwqGemmBIndex', 'NativeAwqGemmBStore', 'NativeAwqGemmBRound', 'NativeAwqGemmBLoop',
            'NativeAwqGemmBEntry', 'NativeAwqGemmBChunk', 'NativeAwqGemmBStage', 'NativeAwqGemmBValues',
            'NativeAwqGemmStaging')
BLOCK_MODELS = ('NativeAwqGemmStagingFrame', 'NativeAwqGemmStagingFold', 'NativeAwqGemmStagingBlock',
                'NativeAwqGemmStagingMemory', 'NativeAwqGemmStagingTiles')
MATRIX_MODELS = ('NativeAwqGemmMatrixProgram', 'NativeAwqGemmFragmentIndex', 'NativeAwqGemmFragmentValues',
                 'NativeAwqGemmFragmentLoad', 'NativeAwqGemmOperandLoop', 'NativeAwqGemmOperandLane',
                 'NativeAwqGemmOperandFold', 'NativeAwqGemmOperandBlock', 'NativeAwqGemmMMAElement',
                 'NativeAwqGemmMMAValues', 'NativeAwqGemmMMABank', 'NativeAwqGemmMMAFold',
                 'NativeAwqGemmMatrixPass', 'NativeAwqGemmMatrixPhase', 'NativeAwqGemmMatrixIteration')
GRID_MODELS = ('NativeAwqGemmTailProgram', 'NativeAwqGemmKControl', 'NativeAwqGemmOutputIndex',
               'NativeAwqGemmOutputStore', 'NativeAwqGemmOutputRound', 'NativeAwqGemmOutputLoop',
               'NativeAwqGemmOutputLane', 'NativeAwqGemmTailFold', 'NativeAwqGemmTailBlock',
               'NativeAwqGemmTileStep', 'NativeAwqGemmKLoop', 'NativeAwqGemmBlockFrames', 'NativeAwqGemmGrid')
BASE_SOURCE_AUDITS = {'AwqSource.'+name for name in ('source_binding', 'layout_binding', 'geometry_binding', 'fuel_binding',
                      'first_barrier', 'middle_barrier', 'halt_site', 'matrix_sites', 'source_length')}
INITIAL_SOURCE_AUDITS = {'AwqSource.initial_execution', 'AwqSource.initial_block_execution'}
STAGES = {
    'initial-decode-v1': {'models': BASE_MODELS, 'audits': 90, 'library_audits': 54, 'steps': 6,
                          'root': 'NativeAwqGemmPrefix', 'source_audits': BASE_SOURCE_AUDITS},
    'initial-block-v2': {'models': BASE_MODELS+INITIAL_MODELS, 'audits': 166, 'library_audits': 122,
                         'steps': [31, 47], 'root': 'NativeAwqGemmInitialBlock',
                         'source_audits': BASE_SOURCE_AUDITS|INITIAL_SOURCE_AUDITS},
    'a-staging-v3': {'models': BASE_MODELS+INITIAL_MODELS+A_MODELS, 'audits': 256, 'library_audits': 208,
                     'steps': [31, 47], 'root': 'NativeAwqGemmAValues',
                     'source_audits': BASE_SOURCE_AUDITS|INITIAL_SOURCE_AUDITS|{'AwqSource.a_staging_execution'}},
    'lane-staging-v4': {'models': BASE_MODELS+INITIAL_MODELS+A_MODELS+B_MODELS, 'audits': 363, 'library_audits': 311,
                       'steps': [31, 47], 'root': 'NativeAwqGemmStaging',
                       'source_audits': BASE_SOURCE_AUDITS|INITIAL_SOURCE_AUDITS|
                           {'AwqSource.a_staging_execution', 'AwqSource.lane_staging_execution'}},
    'block-staging-v5': {'models': BASE_MODELS+INITIAL_MODELS+A_MODELS+B_MODELS+BLOCK_MODELS,
                        'audits': 418, 'library_audits': 358, 'steps': [31, 47],
                        'root': 'NativeAwqGemmStagingTiles',
                        'source_audits': BASE_SOURCE_AUDITS|INITIAL_SOURCE_AUDITS|
                            {'AwqSource.a_staging_execution', 'AwqSource.lane_staging_execution',
                             'AwqSource.block_staging_execution', 'AwqSource.initial_through_staging'}},
    'native-matrix-phase-v6': {'models': BASE_MODELS+INITIAL_MODELS+A_MODELS+B_MODELS+BLOCK_MODELS+MATRIX_MODELS,
                             'audits': 525, 'library_audits': 461, 'steps': [31, 47],
                             'root': 'NativeAwqGemmMatrixIteration',
                             'source_audits': BASE_SOURCE_AUDITS|INITIAL_SOURCE_AUDITS|
                                 {'AwqSource.a_staging_execution', 'AwqSource.lane_staging_execution',
                                  'AwqSource.block_staging_execution', 'AwqSource.initial_through_staging',
                                  'AwqSource.matrix_iteration_execution'}},
    'whole-grid-execution-v7': {'models': BASE_MODELS+INITIAL_MODELS+A_MODELS+B_MODELS+BLOCK_MODELS+MATRIX_MODELS+GRID_MODELS,
                              'audits': 644, 'library_audits': 572, 'steps': [31, 47],
                              'root': 'NativeAwqGemmGrid',
                              'source_audits': BASE_SOURCE_AUDITS|INITIAL_SOURCE_AUDITS|
                                  {'AwqSource.a_staging_execution', 'AwqSource.lane_staging_execution',
                                   'AwqSource.block_staging_execution', 'AwqSource.initial_through_staging',
                                   'AwqSource.matrix_iteration_execution', 'AwqSource.whole_block_execution',
                                   'AwqSource.whole_grid_execution'}},
}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def audits(log):
    entries = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
    if len(dict(entries)) != len(entries) or any(
            not set(a.strip() for a in axioms.split(',') if a.strip()) <= ALLOWED
            for _, axioms in entries):
        raise ValueError('Unapproved or repeated axiom audit')
    return dict(entries)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--packet', type=Path, required=True)
    parser.add_argument('--archive', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--lean-bin', type=Path, required=True)
    args = parser.parse_args()
    packet, out, lean = args.packet.resolve(), args.output.resolve(), args.lean_bin.resolve()
    if any((p/'.git').exists() for p in (out, *out.parents)) or shutil.which('git', path=str(lean)):
        raise ValueError('Fresh replay outside Git with controlled Lean-only PATH required')
    for name, expected in json.loads((packet/'manifest.json').read_text()).items():
        path = (packet/name).resolve()
        if not path.is_relative_to(packet) or sha(path) != expected:
            raise ValueError('Packet hash: '+name)
    recorded = json.loads((packet/'results.json').read_text())
    stage_name = recorded.get('stage', 'initial-decode-v1')
    if stage_name not in STAGES:
        raise ValueError('Unknown component stage')
    stage = STAGES[stage_name]
    if (recorded['owned_lean_modules'] != len(stage['models']) or recorded['axiom_audit_occurrences'] != stage['audits']
            or type(recorded['source_certificates']) is not int or recorded['source_certificates'] != 0
            or type(recorded['model_calls']) is not int or recorded['model_calls'] != 0
            or type(recorded['gpu_trials']) is not int or recorded['gpu_trials'] != 0
            or recorded['source_instances'] != 4 or recorded['false_source_identity_claims_rejected'] != 6
            or recorded['initial_scalar_instructions_executed'] != stage['steps']):
        raise ValueError('Component packet scope')
    if (len(recorded['library_axiom_audits']) != stage['library_audits']
            or set(recorded['source_axiom_audits']) != set(CASES)
            or any(set(recorded['source_axiom_audits'][case]) != stage['source_audits'] for case in CASES)):
        raise ValueError('Stage audit coverage')
    if len(recorded['library_axiom_audits'])+sum(map(len, recorded['source_axiom_audits'].values())) != stage['audits']:
        raise ValueError('Derived audit count')
    if stage_name in ('a-staging-v3', 'lane-staging-v4', 'block-staging-v5', 'native-matrix-phase-v6', 'whole-grid-execution-v7'):
        for field in ('a_staging_source_execution_proved', 'a_staging_shared_values_proved', 'a_staging_outside_memory_preserved'):
            if recorded[field] is not True:
                raise ValueError('A staging claim: '+field)
        if recorded['a_staging_cells_per_lane'] != 8 or recorded['a_staging_scalar_steps'] != [35, 36]:
            raise ValueError('A staging shape/count scope')
    else:
        for field in ('a_staging_source_execution_proved', 'a_staging_shared_values_proved', 'a_staging_outside_memory_preserved',
                      'b_staging_execution_proved', 'matrix_execution_proved', 'k_loop_execution_proved'):
            if recorded.get(field, False) is not False:
                raise ValueError('Unsupported later-stage claim: '+field)
    if stage_name in ('lane-staging-v4', 'block-staging-v5', 'native-matrix-phase-v6', 'whole-grid-execution-v7'):
        for field in ('b_staging_execution_proved', 'b_staging_shared_values_proved', 'b_staging_outside_memory_preserved',
                      'lane_staging_source_execution_proved', 'middle_barrier_reached_per_lane_proved'):
            if recorded[field] is not True:
                raise ValueError('Lane staging claim: '+field)
        if (recorded['b_staging_chunks_per_lane'] != [4, 8] or recorded['b_staging_cells_per_chunk'] != 8
                or recorded['b_staging_scalar_steps'] != [158, 314] or recorded['lane_staging_fuel'] != 512
                or recorded['lane_staging_scalar_steps'] != [193, 194, 349, 350]
                or recorded['lane_staging_order'] != 'a-then-b-per-lane'):
            raise ValueError('Lane staging shape/count/order scope')
    else:
        for field in ('b_staging_execution_proved', 'b_staging_shared_values_proved', 'b_staging_outside_memory_preserved',
                      'lane_staging_source_execution_proved', 'middle_barrier_reached_per_lane_proved'):
            if recorded.get(field, False) is not False:
                raise ValueError('Unsupported later-stage claim: '+field)
    block_fields = ('block_staging_execution_proved', 'middle_block_barrier_resumption_proved',
                    'actual_initial_through_middle_barrier_proved', 'staging_dense_shared_tiles_proved',
                    'native_fragment_shared_values_proved')
    for field in block_fields:
        if stage_name in ('block-staging-v5', 'native-matrix-phase-v6', 'whole-grid-execution-v7'):
            if recorded[field] is not True:
                raise ValueError('Block staging claim: '+field)
        elif recorded.get(field, False) is not False:
            raise ValueError('Unsupported later-stage claim: '+field)
    matrix_fields = ('matrix_execution_proved', 'matrix_fragment_scalar_loads_executed',
                     'native_mfma_snapshot_execution_proved', 'matrix_accumulator_values_proved',
                     'matrix_memory_indices_epochs_preserved', 'matrix_uses_original_warp_fuel')
    for field in matrix_fields:
        if stage_name in ('native-matrix-phase-v6', 'whole-grid-execution-v7'):
            if recorded[field] is not True:
                raise ValueError('Native matrix phase claim: '+field)
        elif recorded.get(field, False) is not False:
            raise ValueError('Unsupported later-stage claim: '+field)
    if stage_name in ('native-matrix-phase-v6', 'whole-grid-execution-v7'):
        if (recorded['matrix_phase_k_extent'] != 32 or recorded['matrix_half_passes'] != 2
                or recorded['matrix_native_instructions_per_iteration'] != [8, 16]
                or recorded['matrix_execution_scope'] != 'one-k32-iteration'):
            raise ValueError('Native matrix phase extent/count/scope')
    grid_fields = ('k_loop_execution_proved', 'k_counter_and_backedge_execution_proved',
                   'guarded_output_stores_execution_proved', 'whole_block_execution_proved',
                   'whole_grid_termination_proved', 'initialized_whole_grid_execution_proved',
                   'original_fuel_preserved', 'output_fp32_to_half_conversion_retained')
    for field in grid_fields:
        if stage_name == 'whole-grid-execution-v7':
            if recorded[field] is not True:
                raise ValueError('Whole grid execution claim: '+field)
        elif recorded.get(field, False) is not False:
            raise ValueError('Unsupported later-stage claim: '+field)
    if stage_name == 'whole-grid-execution-v7':
        if (any(type(recorded[field]) is not int for field in ('output_scalar_steps_upper_bound', 'lane_fuel', 'grid_fuel'))
                or recorded['k_loop_execution_scope'] != 'all-k32-iterations'
                or recorded['k_loop_iteration_count'] != 'K/32' or recorded['block_visit_count'] != '2*(K/32)+1'
                or recorded['output_pairs_per_lane'] != [16, 32] or recorded['output_scalar_steps_upper_bound'] != 64
                or recorded['lane_fuel'] != 512 or recorded['warp_fuel'] != 'tileN/8+1'
                or recorded['block_fuel'] != '2*(K/32)+1' or recorded['grid_fuel'] != 1
                or recorded['execution_semantics'] != 'LarkMFMA.runGrid'):
            raise ValueError('Whole grid count/fuel/semantics scope')
    if recorded['whole_kernel_execution_proved'] is not (stage_name == 'whole-grid-execution-v7'):
        raise ValueError('Unsupported component claim: whole_kernel_execution_proved')
    if recorded.get('runLaunch_acceptance_proved', False) is not False:
        raise ValueError('Unsupported component claim: runLaunch_acceptance_proved')
    for field in ('actual_whole_trace_race_freedom_proved',
                  'source_reference_equality_proved', 'ieee_equivalence_proved', 'original_paper_fully_reproduced'):
        if recorded[field] is not False:
            raise ValueError('Unsupported component claim: '+field)
    out.mkdir(parents=True, exist_ok=False)
    project = out/'project'
    project.mkdir()
    with tarfile.open(args.archive) as archive:
        names = set()
        for member in archive.getmembers():
            path = (project/member.name).resolve()
            if (not member.isfile() or not path.is_relative_to(project) or member.name in names
                    or '.lake' in path.parts or member.name.endswith(('.olean', '.ilean'))):
                raise ValueError('Unsafe or compiled archive member')
            names.add(member.name)
        expected = json.loads((packet/'source-sha256.json').read_text())
        if names != set(expected):
            raise ValueError('Archive source closure differs')
        if {name for name in names if name.startswith('Lark/') and name.endswith('.lean')} != {
                'Lark/'+name+'.lean' for name in stage['models']}:
            raise ValueError('Stage model closure differs')
        archive.extractall(project, filter='data')
    for name, digest in expected.items():
        if sha(project/name) != digest:
            raise ValueError('Frozen source differs: '+name)
    for path in (project/'Lark').glob('NativeAwqGemm*.lean'):
        source = path.read_text()
        if (source.count('set_option maxRecDepth 10000') != 1
                or source.count('set_option maxHeartbeats 2000000') != 1
                or re.search(r'\b(?:sorry|admit|native_decide)\b|(?m:^\s*axiom\b)', source)):
            raise ValueError('New-module proof policy: '+path.name)
    env = dict(os.environ, PATH=str(lean))
    env.pop('LEAN_PATH', None)
    checks = []

    def run(name, command, accepted):
        start = time.monotonic()
        result = subprocess.run(command, cwd=project, env=env, capture_output=True, text=True, timeout=180)
        log = result.stdout+result.stderr
        (out/(name+'.log')).write_text(log)
        actual = result.returncode == 0 and 'error:' not in log and 'sorryAx' not in log
        if actual is not accepted:
            raise ValueError(name+' unexpected result\n'+log[-4000:])
        if not accepted and ('is false' not in log or 'source_binding' not in log
                             or any(s in log for s in ('maximum recursion', 'maximum number of heartbeats', 'Stack overflow'))):
            raise ValueError(name+' did not fail on the false source identity')
        checks.append({'name': name, 'accepted': actual, 'exit_code': result.returncode,
                       'seconds': time.monotonic()-start})
        return log

    library = audits(run('fresh-library-build', [str(lean/'lake'), 'build', 'Lark.'+stage['root']], True))
    if library != recorded['library_axiom_audits']:
        raise ValueError('Library audits differ')
    source_audits = {}
    for case in CASES:
        source = audits(run(case, [str(lean/'lake'), 'env', 'lean', case+'.lean'], True))
        if source != recorded['source_axiom_audits'][case]:
            raise ValueError('Source audit differs: '+case)
        source_audits[case] = source
    for case in CONTROLS:
        run(case, [str(lean/'lake'), 'env', 'lean', case+'.lean'], False)
    result = {'schema': 1, 'stage': stage_name, 'status': 'native-awq-standalone-source-components-replayed',
              'source_instances': len(source_audits), 'false_source_claims_rejected': len(CONTROLS),
              'axiom_audit_occurrences': len(library)+sum(map(len, source_audits.values())),
              'archive_sha256': sha(args.archive), 'git_available_on_proof_path': False,
              'owned_compiled_cache_seeded': False, 'source_certificates': 0,
              'whole_kernel_execution_proved': stage_name == 'whole-grid-execution-v7',
              'execution_semantics': recorded.get('execution_semantics'),
              'runLaunch_acceptance_proved': False, 'actual_whole_trace_race_freedom_proved': False,
              'source_reference_equality_proved': False, 'ieee_equivalence_proved': False,
              'original_paper_fully_reproduced': False, 'model_calls': 0, 'gpu_trials': 0, 'checks': checks}
    (out/'results.json').write_text(json.dumps(result, indent=2)+'\n')
    shutil.copyfile(Path(__file__), out/'replay.py')
    (out/'manifest.json').write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('status', 'source_instances', 'axiom_audit_occurrences')}))


if __name__ == '__main__':
    main()
