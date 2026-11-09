import torch

def reference(x, w1, down):
    return (((x.float() @ w1.float()).relu().half().float() @ down.float())).half()
