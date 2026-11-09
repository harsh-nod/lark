import torch

def reference(q, key, value):
    return (((q.float() @ key.float().repeat_interleave(2,dim=0).transpose(1,2)) / 1.0).softmax(dim=2) @ value.float().repeat_interleave(2,dim=0)).half()
