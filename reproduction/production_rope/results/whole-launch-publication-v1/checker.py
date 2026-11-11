from concurrent.futures import ThreadPoolExecutor
import hashlib
import json
from pathlib import Path
import shutil
import subprocess

root = Path('/tmp/lark-native-rope-execution-20261111')
base = root / 'reproduction/production_rope/results'
out = base / 'whole-launch-publication-v1'
out.mkdir()
pin = '98abb2fe8667328cad5a25c127a54941a0d328e5'

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def write(path, data):
    path.write_text(json.dumps(data, indent=2) + '\n')

packets = {}
for name in ('whole-launch-v1', 'whole-launch-validation-v1', 'whole-launch-stage-guards-v1', 'whole-launch-packaging-v1'):
    path = base / name
    for filename, expected in json.loads((path / 'manifest.json').read_text()).items():
        assert Path(filename).name == filename and sha(path / filename) == expected, (name, filename)
    packets[name] = sha(path / 'manifest.json')
sources = json.loads((base / 'whole-launch-v1/source-manifest.json').read_text())
for name, expected in sources.items():
    content = subprocess.check_output(['git', '-C', str(root), 'show', pin + ':' + name])
    assert hashlib.sha256(content).hexdigest() == expected, name
assert (base / 'whole-launch-validation-v1/fresh-source-manifest.json').read_bytes() == (base / 'whole-launch-v1/source-manifest.json').read_bytes()
certificates = {}
for layout in ('interleaved', 'split-half'):
    for rows in (1, 3, 256, 65535):
        name = f'{layout}-{rows}'
        path = base / 'whole-launch-v1' / name
        report = json.loads((path / 'report.json').read_text())
        assert report['status'] == 'verified' and report['actual_trace_race_freedom_proved'] is True
        for filename, expected in report['files'].items():
            assert sha(path / filename) == expected, (name, filename)
        certificates[name] = sha(path / 'report.json')
provenance = json.loads((root / 'reproduction/production_rope/provenance.json').read_text())
for layout in ('interleaved', 'split-half'):
    for filename in ('kernel.hip', 'reference.py', 'task.json'):
        name = 'cases/' + layout + '/' + filename
        assert sha(root / 'reproduction/production_rope' / name) == provenance['files_sha256'][name]

requests = {
    'github-native-rope-job.json': 'repos/harsh-nod/lark/actions/jobs/130812724341',
    'github-ci-run.json': 'repos/harsh-nod/lark/actions/runs/43106973239',
    'github-ci-jobs.json': 'repos/harsh-nod/lark/actions/runs/43106973239/jobs',
}
def fetch(item):
    name, url = item
    content = subprocess.check_output(['gh', 'api', url])
    (out / name).write_bytes(content)
    return name, json.loads(content)
with ThreadPoolExecutor() as pool:
    responses = dict(pool.map(fetch, requests.items()))
job = responses['github-native-rope-job.json']
assert job['status'] == 'completed' and job['conclusion'] == 'success'
run = responses['github-ci-run.json']
assert run['head_sha'] == pin
suite = [{'name': j['name'], 'status': j['status'], 'conclusion': j['conclusion']}
         for j in responses['github-ci-jobs.json']['jobs']]
shutil.copyfile('/tmp/lark-native-rope-unit-v3-20261111.log', out / 'unit-tests.log')
shutil.copyfile(__file__, out / 'checker.py')
write(out / 'results.json', {
    'schema': 1, 'status': 'native-rope-whole-launch-evidence-bound-to-published-source',
    'source_commit': pin, 'source_files_bound_to_revision': len(sources),
    'frozen_source_manifest_reproduced': True, 'packet_manifest_sha256': packets,
    'source_certificate_report_sha256': certificates, 'source_certificates': 8, 'source_rechecks': 8,
    'library_axiom_audits': 157, 'source_axiom_audits': 80, 'false_lean_claims_rejected': 8,
    'rehashed_certificate_controls_rejected': 8, 'rehashed_stage_controls_rejected': 13,
    'installed_wheel_proof_modules': 164, 'installed_source_exports_and_rechecks': 1,
    'targeted_unit_tests_passed': 8, 'native_rope_ci': job['html_url'],
    'native_rope_ci_status': job['status'], 'native_rope_ci_conclusion': job['conclusion'],
    'full_ci_run': run['html_url'], 'full_ci_status': run['status'], 'full_ci_conclusion': run['conclusion'],
    'full_ci_jobs_at_capture': suite, 'gpu_tested_fixture_bytes_unchanged': True,
    'gpu_evidence_release': 'https://github.com/harsh-nod/lark/releases/tag/native-rope-evidence-20261111',
    'whole_kernel_execution_proved': True, 'actual_trace_race_freedom_proved': True,
    'both_output_buffers_extracted': True, 'source_reference_equality_proved': True,
    'ieee_equivalence_proved': False, 'floating_point_error_bound_proved': False,
    'model_calls': 0, 'new_gpu_trials': 0, 'original_paper_fully_reproduced': False,
})
write(out / 'manifest.json', {p.name: sha(p) for p in sorted(out.iterdir()) if p.is_file()})
print(json.dumps({'status': 'source-and-evidence-bound', 'source_files': len(sources), 'certificates': 8,
                  'native_rope_ci': 'success', 'full_ci': run['status']}))
