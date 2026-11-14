"""Seed exact expected Git blobs; the independent anonymous20 downloads still run."""
import hashlib,json,subprocess
from pathlib import Path
BASE=Path('/tmp/lark-paper-v27-publication-observer-v1-20261113')
VIEW=Path('/tmp/lark-paper-v27-publication-git-view-v1-20261113')
SOURCE=Path('/tmp/lark-paper-v27-controls-mi350-v4-20261113/source')
assert not (BASE/'expected-object-cache.json').exists()
assert not (BASE/'results.json').exists()
assert (Path('/proc')/'1174064'/'cmdline').exists()
descriptor=json.loads((BASE/'descriptor.json').read_text())
commit=descriptor['source_commit']
rows=[]
for bound in descriptor['files']:
 p=SOURCE/bound['path']
 assert p.is_file() and not p.is_symlink() and p.resolve().is_relative_to(SOURCE)
 assert p.stat().st_size==bound['bytes']
 digest=hashlib.sha256()
 with p.open('rb') as source:
  while data:=source.read(1024*1024):digest.update(data)
 assert digest.hexdigest()==bound['sha256']
 expected=subprocess.check_output(['git','-C',str(VIEW),'rev-parse',commit+':'+bound['path']],text=True).strip()
 with p.open('rb') as source:
  actual=subprocess.check_output(['git','-C',str(VIEW),'-c','core.compression=0','hash-object','-w','--stdin'],stdin=source,text=True).strip()
 assert actual==expected
 rows.append({'path':bound['path'],'Git_blob':actual,'bytes':bound['bytes'],'sha256':bound['sha256']})
record={'status':'all20-expected-Git-blobs-bound-to-actual-source-commit','source_commit':commit,'files':rows,
 'source':'already-verified-complete-MI350-v4-inputs','no_downloaded_program_or_snapshot_changed':True,
 'anonymous_public_URL_downloads_not_replaced':True,'publication_process_not_restarted':True,
 'replays_by_cache_preparation':0,'scope':'Expected-input Git object preparation only; every actual publication URL download and all98 replays still required.'}
(BASE/'expected-object-cache.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({'status':record['status'],'files':len(rows),'bytes':sum(r['bytes'] for r in rows)}),flush=True)
