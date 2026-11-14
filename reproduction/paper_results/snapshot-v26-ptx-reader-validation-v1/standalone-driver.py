"""Authored reader validation; captured packet code remains data."""
import importlib.util
import json
from pathlib import Path
import sys
import time

here = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location('trusted_recording_reader', here / 'ptx_extended_evidence.py')
module = importlib.util.module_from_spec(spec)
spec.loader.exec_module(module)
root = here / 'corpus'
assert not any((p / '.git').exists() for p in (root, *root.parents))
config = {'evidence_groups': {}}
for kind, protocol in module.PROTOCOLS.items():
    config[module.CONFIG_KEYS[kind]] = {k: protocol[k] for k in (
        'prefix', 'publication_prefix', 'ci_prefix', 'main_prefix')}
    config['evidence_groups'][kind] = [p.relative_to(root).as_posix()
        for key in ('prefix', 'publication_prefix', 'ci_prefix', 'main_prefix')
        for p in (root / protocol[key]).iterdir() if p.is_file()]
reports = {}
for kind in module.PROTOCOLS:
    started = time.monotonic()
    reports[kind] = module.check_ptx_extended_evidence(config, kind=kind, root=root)
    reports[kind]['reader_seconds'] = time.monotonic() - started
assert not any(n == 'lark_kernels' or n.startswith('lark_kernels.') for n in sys.modules)
assert sys.flags.isolated and all(not p.startswith(str(Path('/tmp/lark-paper-v26-20261113')))
                                 for p in sys.path)
(here / 'standalone-reader-results.json').write_text(json.dumps(reports, indent=2) + '\n')
print(json.dumps({'status': 'isolated-no-Git-no-SDK-complete-readers-passed',
                  'archives': sum(v['archives_checked'] for v in reports.values()),
                  'archive_members': sum(v['archive_members_checked'] for v in reports.values()),
                  'fresh_Lean_GPU_model_checks': 0}), flush=True)
