import torch

def reference(x):
    return (torch.softmax(x.float(), dim=0)).half()
