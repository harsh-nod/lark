import torch


def reference(a, b):
    return (a.float() @ b.float()).half()
