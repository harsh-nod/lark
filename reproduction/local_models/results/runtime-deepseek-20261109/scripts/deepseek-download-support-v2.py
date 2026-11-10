from huggingface_hub import snapshot_download
import json
p=snapshot_download('deepseek-ai/DeepSeek-V4.1-Flash-1017',revision='1bae0e1088993b9b82de08f59de5be5a34e42170',cache_dir='/dev/shm/lark-models-20261109/hub',allow_patterns=['*.json','*.model','*.txt','*.jinja','*.py','*.md','LICENSE*'],max_workers=4)
print(json.dumps({'support_snapshot':p}),flush=True)
