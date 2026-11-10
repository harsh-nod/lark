from huggingface_hub import snapshot_download
p=snapshot_download('zai-org/GLM-5.3',revision='ba32f8c19c8738e2c57c71798c601d477a7bf844',cache_dir='/dev/shm/lark-models-20261109/hub',allow_patterns=['*.json','*.model','*.txt','*.jinja','*.py','*.md','LICENSE*'],max_workers=4)
print(p)
