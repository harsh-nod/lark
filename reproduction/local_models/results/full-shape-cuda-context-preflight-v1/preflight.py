import argparse
import hashlib
import json
from pathlib import Path
import shutil
import sys

ROOT = Path('/tmp/lark-full-shape-cuda-models-20261113')
sys.path.insert(0, str(ROOT))
from reproduction.local_models import full_shape_run as run

parser = argparse.ArgumentParser()
parser.add_argument('--server', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
prepared = Path('/tmp/lark-full-shape-cuda-model-preflight-v1-20261113')
sources = run.verify_preparation(prepared)
assert run.sha(prepared / 'manifest.json') == run.CUDA_PREPARATION_SHA256
server = json.loads(args.server.read_text())
assert server['status'] == 'ready' and server['image'] == run.IMAGE
assert server['revision'] == run.MODELS[server['model']]
run.client.check_health(server['endpoint'], server['model'])
args.output.mkdir(exist_ok=False)
shutil.copyfile(args.server, args.output / 'server.json')
rows = []
for name, *_ in run.full_shape.benchmark.CASES:
    folder = args.output / name
    folder.mkdir()
    request = json.loads((prepared / 'cases' / name / 'request.json').read_text())
    _, catalogue = run.library_context(name, sources)
    messages = run.messages(request, catalogue, [],
        'No candidate yet. Inspect generic libraries as needed and prove all four fixed goals.', '',
        {'model_requests': 16, 'proof_checks': 3, 'library_reads': 8})
    count, limit = run.tokenize(server['endpoint'], server['model'], messages, folder)
    assert count + run.PROTOCOL['max_tokens'] + run.PROTOCOL['context_margin'] <= min(
        limit, server['max_model_len'], run.PROTOCOL['context_limit'])
    rows.append({'case': name, 'input_tokens': count, 'reported_context': limit,
                 'messages_sha256': hashlib.sha256(run.encoded(messages)).hexdigest()})
run.write(args.output / 'results.json', {
    'schema': 1, 'status': 'all-seventeen-full-size-cuda-initial-contexts-fit',
    'source_checkpoint': '1b22551bc295431707dc81288a57ac9a2e6f9475',
    'source_language': 'cuda', 'model': server['model'], 'revision': server['revision'],
    'server_record_sha256': run.sha(args.server), 'controller_sha256': run.sha(Path(run.__file__)),
    'driver_sha256': run.sha(Path(__file__)), 'preparation_manifest_sha256': run.CUDA_PREPARATION_SHA256,
    'cases': rows, 'max_initial_prompt_tokens': max(x['input_tokens'] for x in rows),
    'context_limit': run.PROTOCOL['context_limit'], 'tokenization_requests': 17,
    'model_inference_calls': 0, 'gpu_trials': 0, 'new_source_certificates': 0,
    'original_paper_fully_reproduced': False,
    'scope': 'CUDA prompt tokenization only on an already-owned MI350 runtime. No generation, proof attempt, CUDA execution or NVIDIA measurement.'})
print(json.dumps({'model': server['model'], 'cases': len(rows), 'model_inference_calls': 0,
                  'max_initial_prompt_tokens': max(x['input_tokens'] for x in rows)}))
