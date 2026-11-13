import hashlib
import json
from pathlib import Path
import sys

REPOSITORY = Path('/tmp/lark-full-shape-models-20261112')
sys.path.insert(0, str(REPOSITORY))
from reproduction.local_models import full_shape_run as run

ROOT = Path(__file__).resolve().parent
PREPARED = Path('/tmp/lark-full-shape-model-preflight-v2-20261112')
server = json.loads((ROOT / 'server-ready.json').read_text())
url, model = server['endpoint'], server['model']
run.client.check_health(url, model)
assert server['revision'] == run.MODELS[model] and server['image'] == run.IMAGE
content = run.client.call(url, model, [
    {'role': 'system', 'content': 'Reply with exactly LARK_READY and nothing else.'},
    {'role': 'user', 'content': 'LARK_READY'},
], ROOT / 'warmup', seed=0, temperature=0, max_tokens=256,
   timeout=1800, reasoning_effort='low', thinking_token_budget=64)
assert content.strip() == 'LARK_READY', 'Warmup did not return the exact marker'
receipt = json.loads((ROOT / 'warmup/receipt.json').read_text())
run.write(ROOT / 'warmup-summary.json', {
    'status': 'warmup-passed', 'content': content.strip(), 'usage': receipt['usage'],
    'actual_generation_requests': 1, 'model_proof_attempts': 0,
    'external_api_spend_usd': 0, 'scope': 'Protocol warmup only; excluded from proof experiments.'})
sources = run.verify_preparation(PREPARED)
context = ROOT / 'context'
context.mkdir(exist_ok=False)
remaining = {'model_requests': 16, 'proof_checks': 3, 'library_reads': 8}
feedback = 'No candidate yet. Inspect generic libraries as needed and prove all four fixed goals.'
cases = []
for name, *_ in run.full_shape.benchmark.CASES:
    folder = context / name
    folder.mkdir()
    request = json.loads((PREPARED / 'cases' / name / 'request.json').read_text())
    _, catalogue = run.library_context(name, sources)
    messages = run.messages(request, catalogue, [], feedback, '', remaining)
    count, limit = run.tokenize(url, model, messages, folder)
    assert count + run.PROTOCOL['max_tokens'] + run.PROTOCOL['context_margin'] <= min(
        limit, server['max_model_len'], run.PROTOCOL['context_limit'])
    cases.append({'case': name, 'input_tokens': count, 'reported_context': limit,
                  'messages_sha256': hashlib.sha256(run.encoded(messages)).hexdigest()})
run.write(ROOT / 'context-results.json', {
    'schema': 1, 'status': 'all-seventeen-full-size-initial-contexts-fit', 'cases': cases,
    'max_initial_prompt_tokens': max(x['input_tokens'] for x in cases),
    'context_limit': run.PROTOCOL['context_limit'], 'model_calls': 0, 'gpu_trials': 0,
    'preparation_manifest_sha256': run.PREPARATION_SHA256,
    'runner_sha256': run.sha(Path(run.__file__)),
    'driver_sha256': run.sha(Path(__file__)), 'original_paper_fully_reproduced': False})
print(json.dumps({'status': 'warmup-and-context-preflight-passed', 'context_cases': len(cases),
                  'max_initial_prompt_tokens': max(x['input_tokens'] for x in cases),
                  'warmup_usage': receipt['usage']}))
