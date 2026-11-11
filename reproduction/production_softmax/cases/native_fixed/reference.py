import torch


def reference(inp):
    return torch.softmax(inp.float(), dim=1).half()
