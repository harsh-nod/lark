import torch

def reference(x, w, bias):
    return x @ w + bias
