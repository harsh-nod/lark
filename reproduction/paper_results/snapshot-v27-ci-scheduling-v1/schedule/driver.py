"""Redistribute existing checks without removing commands or changing any job cap."""
from collections import Counter
import hashlib
import json
from pathlib import Path
import re
import yaml

ROOT=Path('/tmp/lark-paper-v27-20261113')
OUT=Path('/tmp/lark-v27-ci-scheduling-v1-20261113')
OUT.mkdir(exist_ok=False)
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
path=ROOT/'.github/workflows/ci.yml'
before=path.read_text(); (OUT/'before.yml').write_text(before)
text=before

def remove_step(name):
 global text
 marker='      - name: '+name+'\n'
 assert text.count(marker)==1
 start=text.index(marker)
 match=re.search(r'^      - |^  [a-z][a-z-]*:',text[start+len(marker):],re.M)
 end=start+len(marker)+match.start() if match else len(text)
 block=text[start:end]
 text=text[:start]+text[end:]
 return block

packet_names=[
 'Audit frozen elaborated-reference numerical evidence without GPU or model calls',
 'Reject altered numerical evidence and fully rehashed scope claims',
 'Audit all seventeen benchmark reference families and complete score tensors',
 'Reject altered benchmark scope, samples, controls and score oracles']
packets=''.join(remove_step(n) for n in packet_names)
marker='      - name: Require six model cohorts and six complete-source PTX development proofs\n'
assert text.count(marker)==1;text=text.replace(marker,packets+marker)
fused_names=['Rebuild native in-place fused RMSNorm whole seeded-inout launch outside Git',
             'Check whole-launch report stage guards']
fused=''.join(remove_step(n) for n in fused_names)
assert text.count('  ptx-matrix:\n')==1;text=text.replace('  ptx-matrix:\n',fused+'  ptx-matrix:\n')
start=text.index('  proof-tests:\n')
section=text[start:]
checkout='      - uses: actions/checkout@11d5960a326750d5838078e36cf38b85af677262 # v4\n'
assert section.count(checkout)==1
section=section.replace(checkout,checkout+'        with:\n          fetch-depth: 0\n          filter: blob:none\n',1)
smoke='''      - name: Check all3792 preserved evidence paths before Lean work
        run: python -m unittest discover -s tests -p test_prepare_ptx_rotary_snapshot.py -v
'''
marker='      - name: Check machine model\n';assert section.count(marker)==1
section=section.replace(marker,smoke+marker)
text=text[:start]+section
old=yaml.safe_load(before)['jobs'];new=yaml.safe_load(text)['jobs']
assert set(old)==set(new) and len(old)==24
assert {k:v['timeout-minutes'] for k,v in old.items()}=={k:v['timeout-minutes'] for k,v in new.items()}
def commands(jobs):
 return Counter((s.get('name'),s.get('run'),s.get('working-directory')) for j in jobs.values() for s in j['steps'] if 'run' in s)
original=commands(old);revised=commands(new)
assert not (original-revised), 'No old named command can be lost or changed'
added=revised-original
assert sum(added.values())==1 and next(iter(added))[0]=='Check all3792 preserved evidence paths before Lean work'
assert new['proof-tests']['steps'][0]['with']=={'fetch-depth':0,'filter':'blob:none'}
for name in packet_names:
 assert any(s.get('name')==name for s in new['paper-ledger']['steps'])
for name in fused_names:
 assert any(s.get('name')==name for s in new['fused-real']['steps'])
assert any(s.get('name')=='Run tests, including Lean integration and mutants' and s['run']=='python -m unittest discover -s tests -v' for s in new['proof-tests']['steps'])
path.write_text(text);(OUT/'after.yml').write_text(text)
record={'status':'all-original-named-commands-and-all24-job-caps-preserved','jobs':24,
 'original_named_run_commands':sum(original.values()),'revised_named_run_commands':sum(revised.values()),
 'added_check':'early complete3792-evidence preservation unit gate',
 'moved_to_paper_ledger':packet_names,'moved_to_fused_real':fused_names,
 'proof_tests_checkout':{'fetch-depth':0,'filter':'blob:none'},
 'pinned_checkout_input_source':'https://raw.githubusercontent.com/actions/checkout/11d5960a326750d5838078e36cf38b85af677262/action.yml',
 'whole_98_suite_seconds':300,'per_replay_seconds':120,'max_independent_replayers':2,
 'source_CI_not_executed_by_this_check':True,'original_paper_fully_reproduced':False}
(OUT/'results.json').write_text(json.dumps(record,indent=2)+'\n')
(OUT/'manifest.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(OUT.iterdir()) if p.is_file()},indent=2)+'\n')
print(json.dumps(record),flush=True)
