"""Extend the immutable v23 ledger after the complete published GEMV gates exist.

No model, Lean or GPU experiment is run. Existing snapshots remain untouched.
"""

import argparse
import copy
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from reproduction.paper_results.full_shape_evidence import check_full_shape_evidence  # noqa: E402
from reproduction.paper_results.ptx_pointwise_evidence import check_ptx_pointwise_evidence  # noqa: E402
from reproduction.paper_results.ptx_dot_evidence import (  # noqa: E402
    CI, PREFIX, PUBLICATION, check_ptx_dot_evidence,
)

BASELINE = 'reproduction/paper_results/snapshots/20261113-v23'
REFRESH = 'reproduction/paper_results/original-artifact-refresh-20261113-1745'
MAIN_RECEIPT = 'reproduction/ptx/results/full-size-gemv-proof-ci-main-v1'
REQUIRED = (PREFIX, PUBLICATION, CI, MAIN_RECEIPT, REFRESH,
            'reproduction/paper_results/snapshot-v23-ci-main-v1')


def require(condition, message):
    if not condition:
        raise ValueError(message)


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def augment_auditor(source):
    replacements = (
        ('    ptx_checks = check_ptx_pointwise_evidence(config)\n',
         '    ptx_checks = check_ptx_pointwise_evidence(config)\n'
         '    from ptx_dot_evidence import check_ptx_dot_evidence\n'
         '    gemv_checks = check_ptx_dot_evidence(config)\n'),
        ('        "ptx_pointwise_evidence_checks": ptx_checks,\n',
         '        "ptx_pointwise_evidence_checks": ptx_checks,\n'
         '        "ptx_dot_evidence_checks": gemv_checks,\n'),
        ('    ptx = report["ptx_pointwise_evidence_checks"]\n',
         '    ptx = report["ptx_pointwise_evidence_checks"]\n'
         '    gemv = report["ptx_dot_evidence_checks"]\n'),
        ('        link("reproduction/paper_results/level2-cost-arithmetic-v1/RESULTS.md",\n',
         '        link("reproduction/ptx/results/full-size-gemv-proof-v1/RESULTS.md",\n'
         '             "Exact-source complete compiled FP16 GEMV proof")\n'
         '        + " adds one independent 512x1024 development proof covering all 119 instructions, "\n'
         '        + "the actual 64-iteration backward loop, all 512 active lanes, actual-trace race "\n'
         '        + "freedom and all extracted reference outputs. Its "\n'
         '        + str(gemv["positive_rechecks"]) + " positive rechecks and "\n'
         '        + str(gemv["direct_Lean_negative_controls"])\n'
         '        + " direct Lean source-binding controls remain repeated checks of one kernel. "\n'
         '        + gemv["scope"] + "\\n",\n'
         '        link("reproduction/paper_results/original-artifact-refresh-20261113-1745/results.json",\n'
         '             "Later November13 bounded original-artifact observations")\n'
         '        + " preserve the empty named repository/default-ref response and original v1 labels; "\n'
         '        + "this is no proof of global absence or new scientific experiment.\\n",\n'
         '        link("reproduction/paper_results/level2-cost-arithmetic-v1/RESULTS.md",\n'),
    )
    for before, after in replacements:
        require(source.count(before) == 1, 'Frozen v23 auditor integration point differs')
        source = source.replace(before, after)
    compile(source, 'frozen-complete-PTX-auditor.py', 'exec')
    return source


def prepare_snapshot(*, evidence_commit, source_archive, snapshot, root=ROOT):
    root = Path(root).resolve()
    # Require actual source-CI/publication/main receipts before any output exists.
    require(all((root / prefix / 'manifest.json').is_file() for prefix in REQUIRED),
            'Complete actual GEMV publication, twenty-job CI, main receipt and artifact observations required')
    require(re.fullmatch('[0-9a-f]{40}', evidence_commit) is not None, 'Concrete evidence checkpoint required')
    require(subprocess.check_output(['git', 'rev-parse', 'HEAD'], cwd=root, text=True).strip() == evidence_commit
            and not subprocess.check_output(['git', 'status', '--porcelain'], cwd=root, text=True).strip(),
            'Clean concrete evidence checkout required')
    snapshot = Path(snapshot)
    snapshot = (root / snapshot).resolve() if not snapshot.is_absolute() else snapshot.resolve()
    require(snapshot.is_relative_to(root / 'reproduction/paper_results/snapshots') and not snapshot.exists(),
            'Fresh snapshot inside repository required')
    config = copy.deepcopy(read(root / BASELINE / 'targets.json'))
    archive = Path(source_archive).resolve()
    require(hashlib.sha256(archive.read_bytes()).hexdigest() == config['source_archive_sha256'],
            'Pinned original manuscript source required')
    before = {p for group in config['evidence_groups'].values() for p in group}
    config['evidence_commit'] = evidence_commit
    later = subprocess.check_output(['git', 'ls-tree', '-r', '--name-only', evidence_commit,
                                     '--', *REQUIRED], cwd=root, text=True).splitlines()
    require(all(any(p.startswith(prefix + '/') for p in later) for prefix in REQUIRED), 'Later receipts missing')
    config['evidence_groups']['later_artifacts'] = sorted(set(config['evidence_groups']['later_artifacts']) | set(later))
    config['ptx_dot_proof'] = {'prefix': PREFIX, 'publication_prefix': PUBLICATION, 'ci_prefix': CI}
    config['evidence_groups']['ptx_dot_proof'] = [
        'reproduction/paper_results/ptx_dot_evidence.py',
        *[p for p in later if any(p.startswith(prefix + '/') for prefix in (PREFIX, PUBLICATION, CI))],
    ]
    require(before <= {p for group in config['evidence_groups'].values() for p in group},
            'All earlier evidence must be retained')
    gemv = check_ptx_dot_evidence(config, root=root)
    models = check_full_shape_evidence(config, root=root)
    check_ptx_pointwise_evidence(config, root=root)
    require(models['complete_independent_cohorts'] == 6 and models['all_six_independent_cohorts_present'] is True,
            'All six actual independent cohorts required')
    from reproduction.local_models import compare_full_shape
    spec = config['full_shape_models']
    fresh = compare_full_shape.compare([root / p['prefix'] for p in spec['packets']])
    recorded = read(root / spec['comparison_prefix'] / 'results.json')
    require({k: v for k, v in fresh.items() if k != 'created_at_utc'}
            == {k: v for k, v in recorded.items() if k != 'created_at_utc'}
            and compare_full_shape.markdown(fresh) == (root / spec['comparison_prefix'] / 'RESULTS.md').read_text(),
            'All six raw and fresh-audit packets must regenerate the comparison')
    promotion = read(root / MAIN_RECEIPT / 'results.json')
    require(promotion['source_checkpoint'] == gemv['source_commit'] and promotion['source_CI_jobs'] == 20
            and promotion['original_paper_fully_reproduced'] is False,
            'Actual completed GEMV main-promotion receipt required')
    old = 'The other full-size generated families remain unsupported.'
    value = config['floats']['tab:instr-cats']['available_evidence']
    require(value.count(old) == 1, 'Earlier authored PTX assessment differs')
    config['floats']['tab:instr-cats']['available_evidence'] = value.replace(old,
        'A later complete compiled FP16 GEMV profile also covers all 119 instructions, the real '
        '64-iteration backward loop, all 512 active lanes, actual-trace race freedom and all reference '
        'outputs. The remaining generated families, general signatures and original optimized PTX remain uncovered.')
    descriptions = {
        'tab:instr-cats': '',
        'tab:task-configs': 'The later GEMV development proof preserves [512,1024] @ [1024,1] -> [512,1] '
            'FP16 shapes, grid512/block1/warp32 and the unchanged independent CUDA fuel[4102,1,1,1] as separate data.',
        'tab:retarget': 'The separate full-size GEMV development model adds typed pointer/integer/predicate '
            'control and a complete actual-source backward loop. Its one proof, three rechecks and four '
            'source-binding controls establish no original code-sharing percentage or implementation history.',
        'tab:trust': 'The full-size GEMV packet adds complete actual-source launch, memory-event race freedom '
            'and extracted-output equality against a closed reference AST. Four fresh positive checks rebuild '
            'sixteen owned modules and accept only standard axioms; four typed source mutants fail directly '
            'in Lean. Parsing/reference formalization, abstract scalar/ABI correspondence and aligned disjoint '
            'non-wrapping allocations remain trusted. No NVIDIA or original-result claim is made.',
    }
    for label, description in descriptions.items():
        row = config['floats'][label]
        if description:
            row['available_evidence'] += ' ' + description
        row['evidence_groups'] = list(dict.fromkeys([*row['evidence_groups'], 'ptx_dot_proof']))
    config['dependencies']['semantics'] += (
        ' The later full-size compiled GEMV study adds an independent complete 119-instruction, '
        '64-iteration, 512-active-lane FP16 proof under the declared abstract scalar interpretation. '
        'It and the ReLU study are two development kernels, each with four retained checks; they add '
        'no registered legacy profiles, model success or original paper result. Other full-size '
        'PTX families, general instruction/signature coverage and original optimized programs remain gaps.')
    config['evidence_links'] = {name: 'https://github.com/harsh-nod/lark/blob/' + evidence_commit + '/' + name
                                for group in config['evidence_groups'].values() for name in group}
    auditor = augment_auditor((root / BASELINE / 'auditor.py').read_text())
    snapshot.mkdir(parents=True, exist_ok=False)
    (snapshot / 'auditor.py').write_text(auditor)
    write(snapshot / 'targets.json', config)
    subprocess.run([sys.executable, str(root / 'reproduction/paper_results/replay_snapshot.py'),
                    '--snapshot', str(snapshot), '--source-archive', str(archive), '--build'],
                   cwd=root, check=True, timeout=600)
    return {'status': 'two-independent-PTX-proof-ledger-prepared', 'snapshot': str(snapshot),
            'complete_independent_cohorts': 6, 'original_paper_fully_reproduced': False,
            'fresh_Lean_GPU_model_experiments': 0}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--evidence-commit', required=True)
    parser.add_argument('--source-archive', type=Path, required=True)
    parser.add_argument('--snapshot', type=Path, default=Path('reproduction/paper_results/snapshots/20261113-v24'))
    print(json.dumps(prepare_snapshot(**vars(parser.parse_args()))))


if __name__ == '__main__':
    main()
