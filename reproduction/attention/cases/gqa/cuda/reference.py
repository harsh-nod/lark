import torch


def reference(q, k, v):
    return (((q.float() @ k.float().repeat_interleave(4,dim=0).transpose(-1,-2)) / 8.0).softmax(dim=-1) @ v.float().repeat_interleave(4,dim=0)).half()
