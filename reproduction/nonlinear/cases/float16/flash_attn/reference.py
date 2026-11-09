import torch

def reference(q, key, value):
    return (((q.float() @ key.float().transpose(0,1)) / 2.0).softmax(dim=1) @ value.float()).half()
