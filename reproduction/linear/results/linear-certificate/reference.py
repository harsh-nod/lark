import torch


def reference(a, b, bias):
    return (a.float() @ b.float() + bias.float()).half()
