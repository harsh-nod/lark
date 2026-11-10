"""Resume pinned public weights with bounded HTTPS ranges and SHA-256 validation."""
from concurrent.futures import ThreadPoolExecutor, as_completed
import fcntl,hashlib,json,os,time,urllib.request,urllib.error
from pathlib import Path
from huggingface_hub import HfApi
MODEL='deepseek-ai/DeepSeek-V4.1-Flash-1017'
REV='1bae0e1088993b9b82de08f59de5be5a34e42170'
CACHE=Path('/dev/shm/lark-models-20261109/hub')
BASE=CACHE/'models--deepseek-ai--DeepSeek-V4.1-Flash-1017'
RECORD=Path('/tmp/lark-local-models-20261109/deepseek-download-forward-v2.json')
CHUNK=64*1024**2
WORKERS=16

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(16*1024**2),b''):h.update(b)
 return h.hexdigest()

(BASE/"blobs").mkdir(parents=True,exist_ok=True)
(BASE/"snapshots"/REV).mkdir(parents=True,exist_ok=True)
(CACHE/".locks/models--deepseek-ai--DeepSeek-V4.1-Flash-1017").mkdir(parents=True,exist_ok=True)

info=HfApi().model_info(MODEL,revision=REV,files_metadata=True)
if info.sha!=REV or info.gated:raise RuntimeError('Unexpected public revision')
record={'model':MODEL,'revision':REV,'transport':'HTTPS 64MiB checked ranges','workers':WORKERS,'model_calls':0,'files':[],'status':'downloading','runner_sha256':sha(Path(__file__))}
RECORD.write_text(json.dumps(record,indent=2)+'\n')
for f in info.siblings:
 if not f.rfilename.endswith('.safetensors'):continue
 digest=f.lfs.sha256
 dest=BASE/'blobs'/digest
 if dest.exists():continue
 lockpath=CACHE/'.locks/models--deepseek-ai--DeepSeek-V4.1-Flash-1017'/(digest+'.lock')
 with lockpath.open('a') as lock:
  try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
  except BlockingIOError:continue
  if dest.exists():continue
  url='https://huggingface.co/'+MODEL+'/resolve/'+REV+'/'+f.rfilename
  temp=dest.with_name(digest+'.ranges.incomplete')
  if temp.exists():raise RuntimeError('Fresh ranged destination required')
  begin=time.monotonic()
  fd=os.open(temp,os.O_WRONLY|os.O_CREAT|os.O_EXCL,0o600)
  os.ftruncate(fd,f.size)
  print(json.dumps({'file':f.rfilename,'stage':'start','bytes':f.size}),flush=True)
  def chunk(start):
   end=min(start+CHUNK,f.size)-1
   for attempt in range(6):
    try:
     req=urllib.request.Request(url,headers={'Range':f'bytes={start}-{end}'})
     with urllib.request.urlopen(req,timeout=45) as r:
      if r.status!=206 or r.headers.get('Content-Range')!=f'bytes {start}-{end}/{f.size}':
       raise RuntimeError('Unexpected range response')
      data=r.read(end-start+2)
     if len(data)!=end-start+1:raise RuntimeError('Incomplete range')
     written=os.pwrite(fd,data,start)
     if written!=len(data):raise RuntimeError('Incomplete local write')
     return len(data)
    except Exception as e:
     if attempt==5:raise RuntimeError('Range failed after retries: '+type(e).__name__) from None
     time.sleep(min(2**attempt,8))
  try:
   completed=0
   with ThreadPoolExecutor(max_workers=WORKERS) as pool:
    jobs=[pool.submit(chunk,start) for start in range(0,f.size,CHUNK)]
    for j in as_completed(jobs):
     completed+=j.result()
   os.close(fd);fd=None
   if temp.stat().st_size!=f.size or sha(temp)!=digest:raise RuntimeError('Full weight SHA-256 mismatch')
   os.replace(temp,dest)
   snapshot=BASE/'snapshots'/REV/f.rfilename
   if not snapshot.exists():snapshot.symlink_to('../../blobs/'+digest)
   row={'file':f.rfilename,'bytes':f.size,'sha256':digest,'seconds':time.monotonic()-begin}
   record['files'].append(row)
   RECORD.write_text(json.dumps(record,indent=2)+'\n')
   print(json.dumps(row),flush=True)
  finally:
   if fd is not None:os.close(fd)
record['status']='finished'
RECORD.write_text(json.dumps(record,indent=2)+'\n')
