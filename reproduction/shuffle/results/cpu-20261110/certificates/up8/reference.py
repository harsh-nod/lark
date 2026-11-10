import torch

def reference(x):
    rows = x.reshape(8, 8)
    return torch.stack((rows.select(1, 0), rows.select(1, 0), rows.select(1, 1), rows.select(1, 2), rows.select(1, 3), rows.select(1, 4), rows.select(1, 5), rows.select(1, 6)), dim=1).reshape(64)
