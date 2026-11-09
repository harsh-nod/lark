import torch

def reference(x):
    return x.float().relu().half()
