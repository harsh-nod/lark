import torch

def reference(x):
    return torch.nn.functional.gelu(x, approximate="tanh")
