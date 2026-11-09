import torch

def reference(x):
    return (torch.nn.functional.gelu(x.float(), approximate="tanh")).half()
