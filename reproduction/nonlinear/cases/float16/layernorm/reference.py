import torch

def reference(x):
    return (torch.nn.functional.layer_norm(x.float(), (4,), eps=1e-5)).half()
