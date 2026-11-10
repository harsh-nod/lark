import torch
def reference(input):
    return input.sum(dim=0, keepdim=True).repeat_interleave(64, dim=0)
