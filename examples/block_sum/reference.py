import torch

def reference(x):
    rows = x.reshape(2, 2)
    return rows.sum(dim=1)
