import torch

def reference(x, w1, up, down):
    return (((torch.nn.functional.silu(x.float() @ w1.float()) * (x.float() @ up.float())).half().float() @ down.float())).half()
