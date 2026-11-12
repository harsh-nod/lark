import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import shutil
import subprocess
import sys
import tarfile

parser = argparse.ArgumentParser()
parser.add_argument('--packet', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--lean-bin', type=Path, required=True)
args = parser.parse_args()
packet, out, lean_bin = args.packet.resolve(), args.output.resolve(), args.lean_bin.resolve()
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
manifest = json.loads((packet / 'manifest.json').read_text())
for name, digest in manifest.items():
    path = packet / name
    if path.is_symlink() or not path.resolve().is_relative_to(packet) or sha(path) != digest:
        raise ValueError('Frozen packet differs: ' + name)
report = json.loads((packet / 'results.json').read_text())
if report['status'] != 'native-qknorm-rope-interleaved-whole-launch-source-order-checked':
    raise ValueError('Unexpected proof stage')
for key in ('whole_kernel_execution_proved', 'complete_actual_trace_classification_proved',
            'source_reference_equality_proved', 'whole_block_execution_proved',
            'whole_grid_execution_proved', 'original_paper_fully_reproduced'):
    if report[key] is not False:
        raise ValueError('Unsupported promoted scope: ' + key)
for key, expected in {'source_certificates': 0, 'model_calls': 0, 'gpu_trials': 0,
                      'local_lean_modules': 47, 'library_axiom_audits': 416,
                      'source_instances': 8, 'false_lean_claims_rejected': 7}.items():
    if type(report[key]) is not int or report[key] != expected:
        raise ValueError('Unexpected stage count: ' + key)
if (sha(packet / 'source.tar.gz') != report['source_archive_sha256'] or
        sha(packet / 'source-manifest.json') != report['source_manifest_sha256']):
    raise ValueError('Source packet binding differs')
for key in ('interleaved_whole_block_execution_proved', 'interleaved_whole_grid_execution_proved',
            'interleaved_whole_launch_source_order_correct', 'interleaved_complete_output_extraction_proved',
            'unqualified_whole_kernel_flags_require_both_layouts'):
    if report[key] is not True:
        raise ValueError('Missing checked interleaved source-order scope: ' + key)
out.mkdir(parents=True, exist_ok=False)
source = out / 'frozen-source'
source.mkdir()
hashes = json.loads((packet / 'source-manifest.json').read_text())
extracted = set()
with tarfile.open(packet / 'source.tar.gz') as archive:
    for entry in archive:
        name = PurePosixPath(entry.name)
        if (not entry.isfile() or entry.size > 10000000 or name.is_absolute() or '..' in name.parts
                or entry.name not in hashes or entry.name in extracted or '.lake' in name.parts
                or entry.name.endswith(('.olean', '.ilean'))):
            raise ValueError('Unexpected archive entry')
        data = archive.extractfile(entry).read()
        if hashlib.sha256(data).hexdigest() != hashes[entry.name]:
            raise ValueError('Archived source differs')
        dest = source / name
        dest.parent.mkdir(parents=True, exist_ok=True)
        dest.write_bytes(data)
        extracted.add(entry.name)
if extracted != set(hashes):
    raise ValueError('Incomplete source archive')
bin_dir = out / 'bin'
bin_dir.mkdir()
for name in ('lake', 'lean'):
    (bin_dir / name).symlink_to(lean_bin / name)
env = dict(os.environ, PATH=str(bin_dir), PYTHONNOUSERSITE='1')
env.pop('PYTHONPATH', None)
env.pop('LEAN_PATH', None)
if shutil.which('git', path=env['PATH']) is not None:
    raise ValueError('Git unexpectedly available')
run = subprocess.run([sys.executable, str(source / 'reproduction/production_qknorm_rope/check_interleaved_launch.py'),
                      '--output', str(out / 'fresh'), '--lean-bin', str(bin_dir)],
                     cwd=source, env=env, capture_output=True, text=True, timeout=750)
(out / 'replay.log').write_text(run.stdout + run.stderr)
if run.returncode:
    raise ValueError('Frozen-source replay failed: ' + (run.stdout + run.stderr)[-12000:])
fresh = json.loads((out / 'fresh/results.json').read_text())
for key in set(report) | set(fresh):
    if key != 'source_archive_sha256' and fresh.get(key) != report.get(key):
        raise ValueError('Replayed proof/count/scope/source binding differs: ' + key)
result = {'schema': 1, 'status': 'frozen-native-interleaved-launch-source-order-replayed',
          'git_available': False, 'seeded_owned_proof_cache': False,
          'source_archive_files': len(extracted), 'source_manifest_sha256': report['source_manifest_sha256'],
          'library_axiom_audits': 416, 'source_axiom_audits': 156, 'false_lean_claims_rejected': 7,
          'checks_axioms_scope_and_source_bindings_match': True, 'whole_kernel_execution_proved': False,
          'source_reference_equality_proved': False, 'source_certificates': 0}
(out / 'results.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps(result))
