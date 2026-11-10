def reference(x):
    rows = x.reshape(8, 8)
    return rows.select(1, 1).repeat_interleave(8, dim=0)
