"""Check the public release against frozen asset hashes without authentication."""
import argparse,hashlib,json,shutil,subprocess,tempfile
from pathlib import Path
from urllib.request import Request,urlopen
p=argparse.ArgumentParser(description=__doc__)
p.add_argument("--expected",type=Path,required=True);p.add_argument("--output",type=Path,required=True)
p.add_argument("--socks-proxy");a=p.parse_args()
expected=json.loads(a.expected.read_text());out=a.output.resolve();out.mkdir(parents=True,exist_ok=False)
base="https://api.github.com/repos/harsh-nod/lark"
def api(suffix):
 request=Request(base+suffix,headers={"Accept":"application/vnd.github+json","X-GitHub-Api-Version":"2022-11-28","User-Agent":"lark-reproduction-publication-audit"})
 with urlopen(request,timeout=30) as response:
  assert response.status==200
  data=response.read()
 return data,json.loads(data)
raw,release=api("/releases/tags/native-softmax-evidence-20261111")
(out/"release-api.json").write_bytes(raw)
assert release["id"]==441474754 and release["draft"] is False and release["prerelease"] is True
assert {x["name"] for x in release["assets"]}==set(expected)
raw,commit=api("/commits/native-softmax-evidence-20261111")
assert commit["sha"]=="96b75ee3e06dfd3b298af404767762e377a358e4"
(out/"tag-commit-api.json").write_bytes(raw)
checks=[]
for asset in sorted(release["assets"],key=lambda x:x["name"]):
 e=expected[asset["name"]]
 assert asset["state"]=="uploaded" and asset["size"]==e["bytes"]
 assert asset["digest"]=="sha256:"+e["sha256"]
 with tempfile.NamedTemporaryFile() as headers:
  command=["curl","--silent","--show-error","--head","--location","--max-redirs","5","--connect-timeout","20","--max-time","60","--dump-header",headers.name,"--output","/dev/null","--write-out","%{http_code}"]
  if a.socks_proxy:command.extend(["--socks5-hostname",a.socks_proxy])
  command.append(asset["browser_download_url"])
  result=subprocess.run(command,capture_output=True,text=True,timeout=70)
  assert result.returncode==0,result.stderr
  assert result.stdout.strip()=="200",result.stdout
  blocks=Path(headers.name).read_text().strip().split("\n\n")
  final=blocks[-1]
  values={line.split(":",1)[0].lower():line.split(":",1)[1].strip() for line in final.splitlines()[1:] if ":" in line}
  size=int(values["content-length"]) if "content-length" in values else None
  assert size is None or size==e["bytes"]
 checks.append({"filename":asset["name"],"bytes":asset["size"],"sha256":e["sha256"],"server_digest":asset["digest"],"public_url":asset["browser_download_url"],"anonymous_head_status":200,"head_content_length":size})
 print(json.dumps(checks[-1]),flush=True)
asset=next(x for x in release["assets"] if x["name"]=="native-softmax-sampled-output.bin.gz")
with tempfile.NamedTemporaryFile() as body:
 command=["curl","--silent","--show-error","--location","--max-redirs","5","--connect-timeout","20","--max-time","180","--output",body.name]
 if a.socks_proxy:command.extend(["--socks5-hostname",a.socks_proxy])
 command.append(asset["browser_download_url"])
 result=subprocess.run(command,capture_output=True,text=True,timeout=190)
 assert result.returncode==0,result.stderr
 h=hashlib.sha256(Path(body.name).read_bytes()).hexdigest()
 assert h==expected[asset["name"]]["sha256"]
report={"schema":1,"status":"four-public-release-assets-checked-against-frozen-packets","release_id":release["id"],"release_url":release["html_url"],"tag_commit":commit["sha"],"authenticated_requests_used":False,"server_sha256_matches_frozen_packets":True,"anonymous_public_head_checks":checks,"anonymous_sample_output_download_sha256":h,"scope":"All four API sizes/server digests are checked against frozen input/output packets. Anonymous public HEAD requests return200; available Content-Length values are checked. The complete sampled-output asset is also anonymously downloaded and hashed. The other three public bodies are not redownloaded by this audit.","source_certificates":0,"whole_softmax_execution_proved":False,"original_paper_fully_reproduced":False}
(out/"results.json").write_text(json.dumps(report,indent=2)+"\n")
shutil.copyfile(a.expected,out/"expected-assets.json");shutil.copyfile(__file__,out/"checker.py")
(out/"manifest.json").write_text(json.dumps({p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(out.iterdir()) if p.is_file()},indent=2)+"\n")
print(json.dumps({"status":report["status"],"assets":len(checks)}))
