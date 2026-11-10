import torch


def reference(q, k, v):
    return (((q.float() @ k.float().transpose(-1,-2)) / 16.0).softmax(dim=-1) @ v.float()).half()
