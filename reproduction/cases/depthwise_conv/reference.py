import torch

def reference(x, w):
    return torch.conv2d(x, w, groups=2)
