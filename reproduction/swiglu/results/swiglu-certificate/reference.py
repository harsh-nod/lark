import torch


def reference(x, wgate, wup, down):
    return ((torch.nn.functional.silu(x.float() @ wgate.float()) * (x.float() @ wup.float())).half().float() @ down.float()).half()
