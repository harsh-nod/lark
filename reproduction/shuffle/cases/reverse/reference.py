import torch

def reference(x):
    return torch.flip(x, [0])
