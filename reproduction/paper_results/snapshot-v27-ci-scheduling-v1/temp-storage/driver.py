"""Select existing adequate RAM storage, preserving the original full-suite command."""
from collections import Counter
import hashlib,json
from pathlib import Path
import yaml

ROOT=Path('/tmp/lark-paper-v27-20261113')
OUT=Path('/tmp/lark-v27-ci-temp-storage-v1-20261113');OUT.mkdir(exist_ok=False)
(OUT/'driver.py').write_bytes(Path(__file__).read_bytes())
p=ROOT/'.github/workflows/ci.yml';before=p.read_text();(OUT/'before.yml').write_text(before)
marker='      - name: Replay the frozen ledger and all rehashed controls without Git\n'
step='''      - name: Select complete-replay temporary storage and record resources
        run: |
          python3 - <<'PYCODE'
          import json
          import os
          from pathlib import Path
          import shutil
          import tempfile
          ram = Path('/dev/shm')
          ram_free = shutil.disk_usage(ram).free if ram.is_dir() else 0
          memory = dict(line.split(':', 1) for line in Path('/proc/meminfo').read_text().splitlines())
          memory_available = int(memory['MemAvailable'].split()[0]) * 1024
          use_ram = ram_free >= 4 * 1024**3 and memory_available >= 6 * 1024**3 and os.access(ram, os.W_OK)
          selected = str(ram) if use_ram else tempfile.gettempdir()
          with open(os.environ['GITHUB_ENV'], 'a') as output:
              output.write('TMPDIR=' + selected + '\\n')
          print(json.dumps({'temporary_directory': selected, 'RAM_filesystem_free_bytes': ram_free,
                            'memory_available_bytes': memory_available,
                            'complete_payload_required': True, 'aggregate_seconds': 300,
                            'per_replay_seconds': 120, 'max_independent_replayers': 2}))
          PYCODE
'''
assert before.count(marker)==1;text=before.replace(marker,step+marker)
old_call='          result = subprocess.run(command)\n'
new_call="          result = subprocess.run(['/usr/bin/time', '-v', *command])\n"
assert text.count(old_call)==1;text=text.replace(old_call,new_call)
old=yaml.safe_load(before)['jobs'];new=yaml.safe_load(text)['jobs']
assert set(old)==set(new) and len(new)==24
assert {k:v['timeout-minutes'] for k,v in old.items()}=={k:v['timeout-minutes'] for k,v in new.items()}
for job in old:
 for old_step in old[job]['steps']:
  if old_step.get('name')=='Replay the frozen ledger and all rehashed controls without Git':
   found=next(s for s in new[job]['steps'] if s.get('name')==old_step['name'])
   assert found['run']==old_step['run'].replace("result = subprocess.run(command)","result = subprocess.run(['/usr/bin/time', '-v', *command])")
   assert "'300s'" in found['run'] and "record['positive_replays'] == 9" in found['run'] and "record['negative_controls'] == 89" in found['run']
  else:
   assert old_step in new[job]['steps'],old_step.get('name')
p.write_text(text);(OUT/'after.yml').write_text(text)
record={'status':'same-complete-suite-and24-job-caps-storage-and-timing-only',
 'change':'Selectexisting/dev/shm onlywith4GiBspaceand6GiBmemoryavailable;otherwiseexistingtemporarydirectory.',
 'original_full98_command_unchanged_inside_GNU_time':True,'no_input_work_moved_outside300second_window':True,
 'resource_limit_changes':False,'checks_removed':0,'jobs':24,
 'runner_specification_source':'https://docs.github.com/en/actions/reference/runners/github-hosted-runners',
 'source_CI_execution_not_claimed':True,'original_paper_fully_reproduced':False}
(OUT/'results.json').write_text(json.dumps(record,indent=2)+'\n')
(OUT/'manifest.json').write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in OUT.iterdir() if p.is_file()},indent=2)+'\n')
print(json.dumps(record))
