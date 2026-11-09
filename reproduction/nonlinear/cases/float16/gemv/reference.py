import torch

def reference(a, x):
    return (a.float() @ x.float()).half()
