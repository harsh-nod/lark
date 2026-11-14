"""Four direct Lean refusals for actual source/reference binding changes."""

import argparse
from datetime import datetime, timezone
import os
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT))
from lark_kernels import ptx_rotary as reader  # noqa: E402
from lark_kernels import ptx_rotary_certificate as checker  # noqa: E402


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    for name in ('recording', 'output', 'lean'):
        parser.add_argument('--' + name, type=Path, required=True)
    args = parser.parse_args()
    BASE, ORIGINAL = checker.fresh_output(args.output), args.recording.resolve()
    SOURCE = os.environ.get('GITHUB_SHA', 'local-source-not-recorded-as-Git-provenance')
    checker.check_inventory(ORIGINAL)
    assert checker.read(ORIGINAL / 'results.json')['source_bound_proof_accepted'] is True
    assert checker.read(ORIGINAL / 'source-bindings.json') == {n: checker.sha(v) for n, v in checker.own_sources().items()}
    inputs = {name: (ORIGINAL / name).read_bytes() for name in checker.INPUTS}
    main_source = reader.render(*reader.prepare_certificate(*(inputs[n].decode() for n in checker.INPUTS)))
    assert main_source.encode() == (ORIGINAL / 'Main.lean').read_bytes()
    lean, _ = checker.toolchain(args.lean)
    BASE.mkdir()
    (BASE / 'driver.py').write_bytes(Path(__file__).read_bytes())
    replay = BASE / 'positive-source-only-replay'
    checker.check_export(ORIGINAL, replay, args.lean)
    environment = dict(os.environ, LEAN_PATH=str(replay / 'modules'))
    source = inputs['kernel.ptx'].decode()
    changes = [
        ('predicate-initializer-flipped', '%p2, 0;', '%p2, 1;', 'source_program'),
        ('unconditional-branch-wrong-target', '$L__BB0_1;', '$L__BB0_2;', 'source_program'),
        ('cosine-parameter-replaced-by-sine', '[induction_rotary_cuda_256_128_param_1]',
         '[induction_rotary_cuda_256_128_param_2]', 'source_program'),
        ('reference-subtraction-replaced-by-addition', '(.binary .sub', '(.binary .add', 'reference_body'),
    ]
    results = []
    for label, before, after, gate in changes:
        case = BASE / label
        case.mkdir()
        for name, content in inputs.items():
            (case / name).write_bytes(content)
        if gate == 'source_program':
            assert source.count(before) == 1, label
            changed = source.replace(before, after)
            (case / 'kernel.ptx').write_text(changed)
            prepared = reader.prepare_certificate(changed, inputs['reference.py'].decode(), inputs['contract.json'].decode())
            generated = reader.render(*prepared)
            checker.write(case / 'translation.json', prepared[1].data())
        else:
            assert main_source.count(before) == 1
            generated = main_source.replace(before, after)
            checker.write(case / 'bypass.json', {'scope': 'Direct Main reference mutation bypasses Python preflight',
                          'input_source_and_reference_unchanged': True, 'before': before, 'after': after})
        (case / 'Main.lean').write_text(generated)
        line = next(i+1 for i, text in enumerate(generated.splitlines()) if text.startswith('theorem ' + gate + ' '))
        checker.write(BASE / 'progress.json', {'pid': os.getpid(), 'stage': 'direct-Lean-negative-control',
                      'case': label, 'source_commit': SOURCE, 'expected_gate': gate,
                      'expected_Main_line': line, 'at_utc': datetime.now(timezone.utc).isoformat()})
        row, log = checker.run_lean(lean, ['Main.lean'], case, environment, case / 'Main.log')
        at_gate = line in [int(n) for n in re.findall(r'Main\.lean:([0-9]+):[0-9]+: error:', log)]
        resource_failure = any(marker.lower() in log.lower() for marker in
                               ['Stack overflow', 'maximum number of heartbeats', 'maximum recursion depth', 'deep recursion'])
        passed = row['exit_code'] != 0 and not row['timed_out'] and at_gate and not resource_failure
        result = {'name': label, 'expected_gate': gate, 'expected_Main_line': line,
                  'check': row, 'rejected_at_expected_gate': at_gate, 'resource_failure': resource_failure,
                  'expected_rejection_verified': passed, 'main_sha256': checker.sha(generated.encode()),
                  'input_bindings': {n: checker.sha((case / n).read_bytes()) for n in checker.INPUTS},
                  'imports': 'Fresh trusted-source positive replay; cached only for these negative controls',
                  'new_kernel_proofs': 0, 'original_paper_fully_reproduced': False}
        checker.write(case / 'results.json', result)
        checker.manifest(case)
        results.append(result)
        checker.write(BASE / 'partial-results.json', results)
        assert passed, label
    checker.write(BASE / 'results.json', {'status': 'all-four-direct-Lean-RoPE-controls-rejected',
                  'source_commit': SOURCE, 'controls': results, 'negative_controls': 4,
                  'positive_replay': checker.read(replay / 'replay.json'),
                  'negative_timeouts': 0, 'resource_limit_failures': 0,
                  'model_calls': 0, 'GPU_trials': 0, 'new_kernel_proofs': 0,
                  'original_paper_fully_reproduced': False})
    checker.manifest(BASE)
    print((BASE / 'results.json').read_text(), flush=True)


if __name__ == '__main__':
    main()
