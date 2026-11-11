import torch


def normalize(values, weight):
    x = values.float()
    scale = torch.rsqrt((x * x).mean(dim=-1, keepdim=True) + 1e-5)
    return x * (scale * weight.float())


def rotate(values, cache):
    x = values[..., 0::2]
    y = values[..., 1::2]
    c = cache[:, None, :64].float()
    s = cache[:, None, 64:].float()
    ox = x * c - y * s
    oy = x * s + y * c
    return torch.stack((ox, oy), dim=-1).flatten(-2).half()


def reference(qkv, q_weight, k_weight, cache):
    q = rotate(normalize(qkv[:, :32, :], q_weight), cache)
    k = rotate(normalize(qkv[:, 32:40, :], k_weight), cache)
    return torch.cat((q, k), dim=1)
