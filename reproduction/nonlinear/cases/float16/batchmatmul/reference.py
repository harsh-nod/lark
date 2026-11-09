import torch

def reference(a, b):
    return (torch.bmm(a.float(), b.float())).half()
