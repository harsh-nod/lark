import torch


def reference(x):
    return ((x.float()-x.float().mean())*torch.rsqrt(((x.float()-x.float().mean())*(x.float()-x.float().mean())).mean()+1e-5)).half()
