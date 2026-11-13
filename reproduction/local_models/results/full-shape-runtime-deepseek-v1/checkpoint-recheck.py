import concurrent.futures,hashlib,json,pathlib,time
from datetime import datetime,timezone
EXPECTED=json.loads(pathlib.Path(__file__).with_name("expected-checkpoint.json").read_text())
assert EXPECTED["model"]=="deepseek-ai/DeepSeek-V4.1-Flash-1017"
assert EXPECTED["revision"]=="1bae0e1088993b9b82de08f59de5be5a34e42170"
root=pathlib.Path(EXPECTED["path"])
allowed=pathlib.Path("/dev/shm/lark-models-20261109/hub")
def check(item):
 p=root/item["file"]
 resolved=p.resolve(strict=True)
 assert resolved.is_relative_to(allowed), "Unexpected checkpoint target"
 assert p.stat().st_size==item["bytes"], "Checkpoint size differs: "+item["file"]
 h=hashlib.sha256()
 with p.open("rb") as f:
  for b in iter(lambda:f.read(8*1024*1024),b""): h.update(b)
 assert h.hexdigest()==item["sha256"], "Checkpoint digest differs: "+item["file"]
 return item
start=time.monotonic()
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:
 list(pool.map(check,EXPECTED["weights"]+EXPECTED["supporting_files"]))
r=dict(EXPECTED)
r.update(status="verified-download",local_only=True,fresh_validation_only=True,
 model_calls=0,gpu_trials=0,downloaded_weight_bytes=0,
 revalidated_at_utc=datetime.now(timezone.utc).isoformat(),validation_seconds=time.monotonic()-start,
 validation_scope="Every existing checkpoint weight/support file rehashed against the previously published pinned revision record; no new download or inference.")
pathlib.Path(__file__).with_name("checkpoint.json").write_text(json.dumps(r,indent=2)+"\n")
print(json.dumps({"status":r["status"],"weights":len(r["weights"]),"supporting_files":len(r["supporting_files"]),"validation_seconds":r["validation_seconds"]}))
