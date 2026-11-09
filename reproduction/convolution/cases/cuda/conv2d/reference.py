import torch


def reference(x, w):
    return torch.conv2d(x.float(),w.float(),groups=1).half()
