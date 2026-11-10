from pathlib import Path
import subprocess
b=Path("/tmp/lark-local-models-20261109")
server=b/"deepseek-server-v2.json"
subprocess.run(["python3",str(b/"scripts/serve-deepseek-v2.py"),"--checkpoint",str(b/"deepseek-checkpoint-verified.json"),"--cache","/dev/shm/lark-models-20261109/hub","--runtime-cache","/dev/shm/lark-deepseek-vllm-cache-20261109-v2","--output",str(server),"--name","lark-deepseek-v41-flash-20261109-v2","--port","19083","--launch"],check=True)
subprocess.run(["python3",str(b/"scripts/ready.py"),"--server",str(server),"--timeout","3600"],check=True)
