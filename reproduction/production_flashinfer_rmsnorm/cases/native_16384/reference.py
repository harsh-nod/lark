import torch


def reference(input, weight):
    x = input.float()
    return (x * torch.rsqrt((x * x).mean(dim=1, keepdim=True) + 1e-5) * (0.0 + weight.float())).half()
