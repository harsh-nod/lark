import torch

def reference(x):
    return (torch.relu(x.float())).half()
