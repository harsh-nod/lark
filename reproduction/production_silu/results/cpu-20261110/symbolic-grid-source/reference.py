import torch


def reference(input):
    packed = input.reshape(1073741823, 2, 1)
    gate = packed.select(1, 0).float()
    up = packed.select(1, 1).float()
    activated = (gate / (1.0 + torch.exp((0.0 - gate) * 1.0))).half()
    return (activated.float() * (up + 0.0)).half()
