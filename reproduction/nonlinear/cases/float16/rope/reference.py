import torch

def reference(x, cosine, sine):
    return (torch.stack((x.float().reshape(2,2,2).select(2,0)*cosine.float()-x.float().reshape(2,2,2).select(2,1)*sine.float(), x.float().reshape(2,2,2).select(2,0)*sine.float()+x.float().reshape(2,2,2).select(2,1)*cosine.float()), dim=-1).reshape(2,4)).half()
