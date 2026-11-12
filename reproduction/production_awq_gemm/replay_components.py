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
    if (recorded['owned_lean_modules'] != 8 or recorded['axiom_audit_occurrences'] != 90
            or type(recorded['source_certificates']) is not int or recorded['source_certificates'] != 0
            or recorded['model_calls'] != 0 or recorded['gpu_trials'] != 0
            or recorded['initial_scalar_instructions_executed'] != 6):
        raise ValueError('Component packet scope')
    for field in ('whole_kernel_execution_proved', 'actual_whole_trace_race_freedom_proved',
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

    library = audits(run('fresh-library-build', [str(lean/'lake'), 'build', 'Lark.NativeAwqGemmPrefix'], True))
    if library != recorded['library_axiom_audits']:
        raise ValueError('Library audits differ')
    for case in CASES:
        source = audits(run(case, [str(lean/'lake'), 'env', 'lean', case+'.lean'], True))
        if source != recorded['source_axiom_audits'][case]:
            raise ValueError('Source audit differs: '+case)
    for case in CONTROLS:
        run(case, [str(lean/'lake'), 'env', 'lean', case+'.lean'], False)
    result = {'schema': 1, 'status': 'native-awq-standalone-source-components-replayed',
              'source_instances': 4, 'false_source_claims_rejected': 6, 'axiom_audit_occurrences': 90,
              'archive_sha256': sha(args.archive), 'git_available_on_proof_path': False,
              'owned_compiled_cache_seeded': False, 'source_certificates': 0,
              'whole_kernel_execution_proved': False, 'actual_whole_trace_race_freedom_proved': False,
              'source_reference_equality_proved': False, 'ieee_equivalence_proved': False,
              'original_paper_fully_reproduced': False, 'model_calls': 0, 'gpu_trials': 0, 'checks': checks}
    (out/'results.json').write_text(json.dumps(result, indent=2)+'\n')
    shutil.copyfile(Path(__file__), out/'replay.py')
    (out/'manifest.json').write_text(json.dumps({p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()}, indent=2)+'\n')
    print(json.dumps({k: result[k] for k in ('status', 'source_instances', 'axiom_audit_occurrences')}))


if __name__ == '__main__':
    main()
