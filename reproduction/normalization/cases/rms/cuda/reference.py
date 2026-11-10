import torch


def reference(x):
    return (x.float()*torch.rsqrt((x.float()*x.float()).mean()+1e-5)).half()
