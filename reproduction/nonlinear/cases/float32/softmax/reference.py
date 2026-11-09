import torch

def reference(x):
    return torch.softmax(x, dim=0)
