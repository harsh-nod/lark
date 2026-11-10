import torch

def reference(x):
    pairs = x.reshape(32, 2)
    return torch.stack((pairs.select(1, 1), pairs.select(1, 0)), dim=1).reshape(64)
