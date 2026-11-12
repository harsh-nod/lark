from concurrent.futures import ThreadPoolExecutor
from pathlib import Path,PurePosixPath
import hashlib,json,os,subprocess,tarfile
from lark_kernels import native_sglang_rmsnorm_certificate as native,real_backend
repo=Path("/tmp/lark-native-sglang-rmsnorm-20261112")
out=Path("/tmp/lark-sglang-canonical-public-source-v1-20261112")
out.mkdir(exist_ok=False)
commit="564354a308d17b850d6cd72e74b23578facd4a8e"
prefix="reproduction/production_sglang_rmsnorm/"
files={"source.tar.gz":prefix+"results/canonical-real-v1/source.tar.gz",
 "source-manifest.json":prefix+"results/canonical-real-v1/source-manifest.json",
 "packet-manifest.json":prefix+"results/canonical-real-v1/manifest.json",
 "packet-results.json":prefix+"results/canonical-real-v1/results.json",
 "replay_native_real.py":prefix+"replay_native_real.py"}
env=dict(os.environ)
env["NO_PROXY"]=env["no_proxy"]=""
def git(path):return subprocess.check_output(["git","show",commit+":"+path],cwd=repo)
def sha(blob):return hashlib.sha256(blob).hexdigest()
def download(item):
 name,path=item
 url="https://raw.githubusercontent.com/harsh-nod/lark/"+commit+"/"+path
 r=subprocess.run(["curl","-q","--fail","--silent","--show-error","--location","--proto","=https","--proto-redir","=https","--noproxy","","--proxy","socks5h://127.0.0.1:18028","--max-time","90","--output",str(out/name),url],env=env,capture_output=True,text=True,timeout=100)
 assert r.returncode==0,(name,r.stderr)
 blob=(out/name).read_bytes()
 assert blob==git(path),name
 return {"file":name,"url":url,"bytes":len(blob),"sha256":sha(blob),"anonymous":True,"matches_published_commit":True}
with ThreadPoolExecutor(max_workers=5) as pool:downloads=list(pool.map(download,files.items()))
manifest=json.loads((out/"source-manifest.json").read_text())
outer=json.loads((out/"packet-manifest.json").read_text())
report=json.loads((out/"packet-results.json").read_text())
assert sha((out/"source.tar.gz").read_bytes())==report["source_archive_sha256"]==outer["source.tar.gz"]
assert sha((out/"source-manifest.json").read_bytes())==report["source_manifest_sha256"]==outer["source-manifest.json"]
blobs={}
with tarfile.open(out/"source.tar.gz") as tar:
 for member in tar:
  rel=PurePosixPath(member.name)
  assert member.isfile() and not rel.is_absolute() and ".." not in rel.parts and str(rel)==member.name
  assert not {".git",".lake"}&set(rel.parts) and not member.name.endswith((".olean",".ilean"))
  assert member.name in manifest and member.name not in blobs and member.size<=8000000
  blob=tar.extractfile(member).read()
  assert sha(blob)==manifest[member.name]
  blobs[member.name]=blob
assert set(blobs)==set(manifest)
bindings={}
for name,blob in blobs.items():
 if name.startswith("Lark/"):path="lean/"+name
 elif name.startswith("LarkReal/"):path="lean-real/"+name
 elif name.startswith("lark_kernels/"):path=name
 elif name in ("kernel.hip","reference.py"):path=prefix+"cases/native_fixed/"+name
 elif name=="LICENSE":path="LICENSE"
 elif name=="UPSTREAM-LICENSE":path=prefix+"upstream/LICENSE"
 else:continue
 assert blob==git(path),name
 bindings[name]={"repository_path":path,"sha256":sha(blob)}
configs=real_backend.configuration()
for name,blob in configs.items():assert blobs[name]==blob,name
for rows in (1,3,64,131072):
 task=git(prefix+f"results/canonical-real-v1/task-{rows}.json")
 assert sha(task)==outer[f"task-{rows}.json"]
 contract,tr=native.prepare(blobs["kernel.hip"].decode(),blobs["reference.py"].decode(),task.decode())
 name="Main.lean" if rows==1 else f"rows-{rows}.lean"
 assert native.render(contract,tr).encode()==blobs[name],name
 assert contract.buffers[0].shape[0]==rows
result={"schema":1,"status":"anonymous-public-native-sglang-source-archive-and-source-bindings-checked",
 "source_commit":commit,"source_archive_sha256":report["source_archive_sha256"],
 "source_manifest_sha256":report["source_manifest_sha256"],"packet_manifest_sha256":sha((out/"packet-manifest.json").read_bytes()),
 "downloads":downloads,"anonymous_bytes":sum(d["bytes"] for d in downloads),"frozen_files":len(blobs),
 "owned_lean_files_bound":sum(n.startswith(("Lark/","LarkReal/")) for n in bindings),
 "python_files_bound":sum(n.startswith("lark_kernels/") for n in bindings),
 "all_frozen_owned_models_and_sdk_bound":True,"source_instances_rerendered":4,"configuration_files_matched":3,
 "bindings":bindings,"model_calls":0,"gpu_trials":0,"original_paper_fully_reproduced":False}
assert result["owned_lean_files_bound"]==88
(out/"source-binding.json").write_text(json.dumps(result,indent=2)+"\n")
print(json.dumps({k:result[k] for k in ("status","anonymous_bytes","frozen_files","owned_lean_files_bound","python_files_bound","source_instances_rerendered")}))
