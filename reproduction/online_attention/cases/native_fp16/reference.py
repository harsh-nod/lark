import torch


def reference(query, key, value):
    return (((query.float() @ key.float().transpose(1, 2)) / 16.0).softmax(dim=2) @ value.float()).half()
