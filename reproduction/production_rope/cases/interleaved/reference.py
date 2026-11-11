import torch


def rotate(values, cache):
    x = values[..., 0::2].float()
    y = values[..., 1::2].float()
    c = cache[:, None, :64].float()
    s = cache[:, None, 64:].float()
    ox = (x * c - y * s).half()
    oy = (y * c + x * s).half()
    return torch.stack((ox, oy), dim=-1).flatten(-2)


def reference(query, key, cache):
    return rotate(query, cache), rotate(key, cache)
