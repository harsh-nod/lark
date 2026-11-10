import torch

def reference(a, b, c):
    return torch.matmul(a.float(), b.float())
