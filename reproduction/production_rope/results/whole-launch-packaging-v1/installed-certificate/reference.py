import torch


def rotate(values, cache):
    x = values[..., :64].float()
    y = values[..., 64:].float()
    c = cache[:, None, :64].float()
    s = cache[:, None, 64:].float()
    ox = (x * c - y * s).half()
    oy = (y * c + x * s).half()
    return torch.cat((ox, oy), dim=-1)


def reference(query, key, cache):
    return rotate(query, cache), rotate(key, cache)
