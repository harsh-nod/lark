import torch

def reference(x):
    return torch.nn.functional.silu(x)
