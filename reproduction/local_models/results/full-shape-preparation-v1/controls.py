"""Repeat proof-slot refusals and inspect all prepared model-visible requests."""
import argparse
import hashlib
import importlib
import json
from pathlib import Path, PurePosixPath
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--repository', required=True, type=Path)
parser.add_argument('--prepared', required=True, type=Path)
parser.add_argument('--output', required=True, type=Path)
args = parser.parse_args()
root, prepared, output = args.repository.resolve(), args.prepared.resolve(), args.output.resolve()
output.mkdir(parents=True, exist_ok=False)
sys.path.insert(0, str(root))
module = importlib.import_module('reproduction.local_models.full_shape')
assert Path(module.__file__).resolve() == root/'reproduction/local_models/full_shape.py'
source_hash = hashlib.sha256(Path(module.__file__).read_bytes()).hexdigest()
source_manifest = json.loads((prepared/'source-manifest.json').read_text())
assert source_manifest['reproduction/local_models/full_shape.py'] == source_hash
manifest = json.loads((prepared/'manifest.json').read_text())
for name, expected in manifest.items():
    path = PurePosixPath(name)
    assert path.parts and not path.is_absolute() and '..' not in path.parts and str(path) == name
    assert not (prepared/name).is_symlink()
    assert hashlib.sha256((prepared/name).read_bytes()).hexdigest() == expected
base = {n: 'by fail' for n in module.SLOTS}
module.validate_proofs(base)
checks = []
cases = [(label, {**base, 'segmentation': value}) for label, value in [
    ('admission', 'by sorry'),
    ('resource-override', 'by set_option maxHeartbeats 3000000 in exact False.elim (by fail)'),
    ('unchecked-evaluation', 'by native_decide'),
    ('declaration', 'by\naxiom bad : False'),
    ('non-proof', 17),
]]
cases += [('missing-slot', {n:p for n,p in base.items() if n != 'segmentation'}),
          ('extra-slot', {**base, 'other':'by rfl'})]
for label, candidate in cases:
    try:
        module.validate_proofs(candidate)
    except (ValueError, TypeError) as error:
        checks.append({'name':label, 'proposal':candidate, 'rejected':True, 'reason':str(error)})
    else:
        raise RuntimeError('Accepted invalid proposal: '+label)
report = json.loads((prepared/'results.json').read_text())
assert report['status'] == 'full-shape-model-fixtures-prepared-and-baselines-checked'
assert report['positive_lean_checks'] == report['masked_negative_lean_checks'] == len(report['cases']) == 17
for case in report['cases']:
    request = json.loads((prepared/'cases'/case['case']/'request.json').read_text())
    spans = module.proof_spans(request['immutable_main'])
    assert all(spans[n]['sdk_positive_control'] == 'by fail' for n in module.SLOTS)
    assert request['immutable_main'].count('set_option maxRecDepth 10000\n') == 1
    assert request['immutable_main'].count('set_option maxHeartbeats 2000000\n') == 1
    assert request['sdk_tactic_bodies_included'] is False
    assert all(not n.endswith('.lean') for n in request['source_files'])
record = {'status':'passed', 'positive_syntax_controls':1, 'negative_controls':7,
          'masked_requests_checked':17, 'checks':checks, 'validator_source_sha256':source_hash,
          'driver_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
          'preparation_manifest_sha256':hashlib.sha256((prepared/'manifest.json').read_bytes()).hexdigest(),
          'model_calls':0, 'gpu_trials':0, 'new_certificates':0, 'fresh_lean_checks':0,
          'original_paper_fully_reproduced':False,
          'scope':'Proposal syntax and frozen request integrity only; baseline Lean checks are recorded separately.'}
(output/'results.json').write_text(json.dumps(record, indent=2)+'\n')
print(json.dumps({'status':'passed', 'negative_controls':7, 'masked_requests_checked':17}))
