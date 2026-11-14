"""Exercise real complete FFN packet captures and semantic refusal boundaries."""
import json
from pathlib import Path
import shutil
import subprocess
import sys
import time

REPO = Path('/tmp/lark-paper-v27-20261113')
SOURCE = REPO / 'reproduction/paper_results'
PACKET = REPO / 'reproduction/ptx/results/full-size-ffn-certificate-payloads-v1'
OUTPUT = Path('/tmp/lark-ffn-complete-reader-adversarial-validation-v2-20261114')
sys.path.insert(0, str(SOURCE))
from ptx_ffn_packet import Packet
from ptx_ffn_evidence import sha


def encoded(value):
    return (json.dumps(value, indent=2) + '\n').encode()


def manifest(entries):
    entries['manifest.json'] = encoded({n: sha(b) for n, b in entries.items() if n != 'manifest.json'})


def main():
    assert not OUTPUT.exists()
    OUTPUT.mkdir()
    started = time.monotonic()
    packet = Packet(PACKET)
    report = packet.read('results.json')
    export = packet.archive('export', report['archives']['export'])
    direct = packet.archive('source-controls-and-fresh-replay', report['archives']['source-controls-and-fresh-replay'])
    mutations = [
        ('accepted-exit-code', lambda row, part: row['Lean'].update(exit_code=0)),
        ('boolean-exit-code', lambda row, part: row['Lean'].update(exit_code=True)),
        ('timed-out-refusal', lambda row, part: row['Lean'].update(timed_out=True)),
        ('increased-timeout', lambda row, part: row['Lean'].update(timeout_seconds=181)),
        ('different-checked-source', lambda row, part: row['Lean'].update(command=['/tmp/lean', 'Other.lean'])),
        ('nonfinite-elapsed-time', lambda row, part: row['Lean'].update(seconds=float('inf'))),
        ('false-gate-lines', lambda row, part: row.update(expected_lines=[True, 10])),
    ]

    def wrong_gate(row, part):
        part['Lean.log'] = part['Lean.log'].replace(b'Main.lean:10:', b'Main.lean:10000:')
        row['Lean']['log_sha256'] = sha(part['Lean.log'])

    def resource_failure(row, part):
        part['Lean.log'] += b'\nmaximum number of heartbeats reached\n'
        row['Lean']['log_sha256'] = sha(part['Lean.log'])

    mutations += [('failure-outside-required-theorem', wrong_gate), ('resource-failure-as-refusal', resource_failure)]
    results = []
    for name, change in mutations:
        forged = dict(direct)
        summary = json.loads(forged['results.json'])
        row = summary['negative_controls'][0]
        prefix = row['control'] + '/'
        part = {n[len(prefix):]: b for n, b in forged.items() if n.startswith(prefix)}
        change(row, part)
        part['results.json'] = encoded(row)
        manifest(part)
        forged.update({prefix + n: b for n, b in part.items()})
        forged['results.json'] = encoded(summary)
        manifest(forged)
        packet.recording(forged).inventory()
        try:
            packet.direct_controls(forged, export)
        except ValueError as exc:
            assert 'inventory' not in str(exc).lower(), str(exc)
            results.append({'case': name, 'coherently_rehashed': True, 'rejected': True, 'gate': str(exc)})
        else:
            raise AssertionError('False direct control accepted: ' + name)
    isolated = OUTPUT / 'trusted-reader'
    isolated.mkdir()
    for name in ('ptx_ffn_packet.py', 'ptx_ffn_evidence.py', 'ptx_ffn_protocol.json'):
        shutil.copyfile(SOURCE / name, isolated / name)
    # No SDK, Git, Lean, compiler, environment imports or model/GPU endpoints.
    run_started = time.monotonic()
    completed = subprocess.run([
        sys.executable, '-I', str(isolated / 'ptx_ffn_packet.py'),
        '--packet', str(PACKET), '--output', str(OUTPUT / 'isolated-full-packet-result'),
    ], cwd=OUTPUT, env={'PATH': '/nonexistent'},
        capture_output=True, timeout=120)
    (OUTPUT / 'isolated.stdout').write_bytes(completed.stdout)
    (OUTPUT / 'isolated.stderr').write_bytes(completed.stderr)
    assert completed.returncode == 0, completed.stderr.decode()
    isolated_result = json.loads((OUTPUT / 'isolated-full-packet-result/results.json').read_text())
    assert isolated_result['archive_members_checked'] == 4416
    assert len(isolated_result['recorded_positive_checks']) == 3
    assert len(isolated_result['independent_false_recording_refusals']) == 31
    assert isolated_result['recorded_direct_Lean_refusals'] == 4
    result = {
        'status': 'complete-FFN-reader-standalone-and-nine-semantic-forgeries-passed',
        'source_files': {n: sha((SOURCE / n).read_bytes()) for n in (
            'ptx_ffn_packet.py', 'ptx_ffn_evidence.py', 'ptx_ffn_protocol.json')},
        'complete_packet_result': isolated_result,
        'isolated_packet_seconds': time.monotonic() - run_started,
        'additional_complete_rehashed_direct_controls': results,
        'isolated_Python': True, 'outside_Git': True, 'SDK_available': False,
        'PATH': '/nonexistent', 'recorded_kernel_identity_count': 1,
        'captured_code_executed': False, 'fresh_Lean_checks': 0, 'model_calls': 0,
        'GPU_trials': 0, 'new_registered_source_certificates': 0,
        'original_paper_fully_reproduced': False,
        'whole_ledger_CI_and_publication_integration_complete': False,
        'seconds': time.monotonic() - started,
    }
    (OUTPUT / 'results.json').write_bytes(encoded(result))
    shutil.copyfile(__file__, OUTPUT / 'driver.py')
    manifest_map = {p.relative_to(OUTPUT).as_posix(): sha(p.read_bytes())
                    for p in OUTPUT.rglob('*') if p.is_file()}
    (OUTPUT / 'manifest.json').write_bytes(encoded(manifest_map))
    print(json.dumps({k: result[k] for k in ('status', 'isolated_packet_seconds', 'seconds')}), flush=True)


if __name__ == '__main__':
    main()
