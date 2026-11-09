import torch

def reference(x, w, bias):
    return (x.float() @ w.float() + bias.float()).half()
