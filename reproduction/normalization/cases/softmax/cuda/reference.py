import torch


def reference(x):
    return x.float().softmax(dim=0).half()
