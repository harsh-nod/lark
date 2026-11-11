import torch


def reference(input, residual, weight):
    x = input.float() + residual.float()
    output = (x * torch.rsqrt((x * x).mean(dim=1, keepdim=True) + 1e-5) * (0.0 + weight.float())).half()
    return output, x.half()
