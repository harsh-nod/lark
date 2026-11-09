import torch

def reference(x):
    return x.reshape(2, 2).sum(dim=1)
