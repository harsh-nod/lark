import torch

def reference(x, y):
    return torch.relu(x + y) * y
