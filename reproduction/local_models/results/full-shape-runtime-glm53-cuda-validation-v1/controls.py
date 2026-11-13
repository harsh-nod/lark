"""Check actual GLM CUDA runtime and two fully rehashed semantic mutations."""
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HELPER = Path('/tmp/lark-package-glm-cuda-runtime-20261113.py')
RUNTIME = Path('/tmp/lark-full-shape-glm53-cuda-runtime-20261113')
OUT = Path('/tmp/lark-glm-cuda-runtime-archive-controls-20261113')


def read(path):
    return json.loads(path.read_text())


def write(path, value):
    path.write_text(json.dumps(value, indent=2) + '\n')


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check(name, runtime, expected_error=None):
    packet = OUT / (name + '-packet')
    proc = subprocess.run([sys.executable, str(HELPER), '--runtime', str(runtime),
                           '--output', str(packet), '--check-only'],
                          capture_output=True, text=True, timeout=60)
    (OUT / (name + '.log')).write_text(proc.stdout + proc.stderr)
    assert not packet.exists()
    if expected_error:
        assert proc.returncode != 0 and expected_error in proc.stderr
    else:
        assert proc.returncode == 0 and 'GLM-CUDA-runtime-packet-preflight-passed' in proc.stdout
    return {'name': name, 'refused': proc.returncode != 0,
            'packet_not_created': True, 'exit_code': proc.returncode}


def main():
    assert sha(HELPER) == '5618b8fc0772bf8f9b72f87e56c16c5eb6fa0bf499d5edc3813a556d4d310f6d'
    OUT.mkdir(exist_ok=False)
    check('positive-actual', RUNTIME)
    context = OUT / 'mutated-context'
    shutil.copytree(RUNTIME, context)
    request = context / 'context/relu/request.json'
    data = read(request)
    data['messages'][0]['content'] += '\nUnrecorded extra instruction.'
    write(request, data)
    receipt = context / 'context/relu/receipt.json'
    data_receipt = read(receipt)
    data_receipt['request_sha256'] = sha(request)
    write(receipt, data_receipt)
    report = context / 'context-results.json'
    summary = read(report)
    # Match the producer's canonical JSON encoding for the altered messages.
    message_bytes = (json.dumps(data['messages'], sort_keys=True, separators=(',', ':')) + '\n').encode()
    # The encoding is imported from the source-checked producer to avoid ambiguity.
    sys.path.insert(0, '/tmp/lark-full-shape-cuda-models-20261113')
    from reproduction.local_models.full_shape_run import encoded
    message_bytes = encoded(data['messages'])
    next(row for row in summary['cases'] if row['case'] == 'relu')['messages_sha256'] = hashlib.sha256(message_bytes).hexdigest()
    write(report, summary)
    controls = [check('fully-rehashed-context-prompt', context, 'Context prompt does not regenerate: relu')]
    warmup = OUT / 'mutated-warmup'
    shutil.copytree(RUNTIME, warmup)
    for name in ('warmup-summary.json', 'warmup/response.json', 'warmup/receipt.json'):
        path = warmup / name
        changed = read(path)
        changed['usage']['total_tokens'] += 1
        write(path, changed)
    receipt = warmup / 'warmup/receipt.json'
    data = read(receipt)
    data['response_sha256'] = sha(warmup / 'warmup/response.json')
    write(receipt, data)
    controls.append(check('fully-rehashed-warmup-usage', warmup, 'Recorded non-proof warmup differs'))
    result = {'schema': 1, 'status': 'runtime-archive-semantic-rehash-controls-passed',
              'helper_sha256': sha(HELPER), 'control_driver_sha256': sha(Path(__file__)),
              'positive_actual_runtime_preflight_passed': True, 'controls': controls,
              'model_calls': 0, 'GPU_actions': 0, 'fresh_lean_checks': 0,
              'scope': 'Original recorded runtime passes; two fully rehashed prompt/warmup metadata mutations are refused at the named fixed-protocol gates before packet creation. Actual source/runtime remains unchanged.'}
    write(OUT / 'results.json', result)
    print(json.dumps(result))


if __name__ == '__main__':
    main()
