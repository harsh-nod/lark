"""Independent contracts at the dimensions in paper Table 9; not original kernels."""

NAMES = (
    "relu",
    "silu",
    "gelu",
    "softmax",
    "layernorm",
    "rmsnorm",
    "gemv",
    "gemm",
    "batchmatmul",
    "linear",
    "conv2d",
    "depthwise_conv",
    "rope",
    "ffn",
    "swiglu",
    "flash_attn",
    "gqa",
)
PAPER_HIP_US = (1.73, 1.75, 1.77, 5.25, 5.05, 4.02, 3.83, 2.14, 11.13, 3.36, 2.65, 4.13)
SHAPES = {
    **{n: ([(16384,)], (16384,)) for n in NAMES[:6]},
    "gemv": ([(512, 1024), (1024, 1)], (512, 1)),
    "gemm": ([(64, 256), (256, 512)], (64, 512)),
    "batchmatmul": ([(32, 64, 256), (32, 256, 512)], (32, 64, 512)),
    "linear": ([(64, 256), (256, 512), (512,)], (64, 512)),
    "conv2d": ([(1, 32, 8, 8), (8, 32, 3, 3)], (1, 8, 6, 6)),
    "depthwise_conv": ([(1, 32, 16, 16), (32, 1, 5, 5)], (1, 32, 12, 12)),
    "rope": ([(256, 128), (256, 64), (256, 64)], (256, 128)),
    "ffn": ([(64, 256), (256, 1024), (1024, 256)], (64, 256)),
    "swiglu": ([(64, 256), (256, 1024), (256, 1024), (1024, 256)], (64, 256)),
    "flash_attn": ([(1, 128, 256)] * 3, (1, 128, 256)),
    "gqa": ([(8, 128, 64), (2, 128, 64), (2, 128, 64)], (8, 128, 64)),
}
CONTRACTS = {
    "relu": "max(x,0)",
    "silu": "x/(1+exp(-x))",
    "gelu": "tanh approximation, cubic coefficient 0.044715",
    "softmax": "one row of length 16384, stable maximum subtraction",
    "layernorm": "one row, population variance, eps=1e-5, no affine parameters",
    "rmsnorm": "one row, eps=1e-5, no affine parameters",
    "gemv": "FP32 accumulation, FP16 input/output",
    "gemm": "FP32 accumulation, FP16 input/output",
    "batchmatmul": "32 independent products, FP32 accumulation, FP16 storage",
    "linear": "x@weight + bias; weight stored [in,out]",
    "conv2d": "NCHW, batch=1, stride=1, padding=0, no bias",
    "depthwise_conv": "NCHW, batch=1, stride=1, padding=0, groups=32, no bias",
    "rope": "adjacent pairs; already supplied FP16 cos/sin tables",
    "ffn": "ReLU(x@W1), FP16 intermediate, then @W2; two kernel launches",
    "swiglu": "SiLU(x@Wgate)*(x@Wup), FP16 intermediate, then @Wdown; two launches",
    "flash_attn": "dense scaled dot-product attention, noncausal, no dropout; not FlashAttention algorithm",
    "gqa": "8 query/2 KV heads, dimension=64, noncausal, no dropout, head-major contiguous storage",
}


def reference(name, args):
    import torch
    import torch.nn.functional as F

    a = [x.float() for x in args]
    x = a[0]
    if name == "relu":
        y = x.relu()
    elif name == "silu":
        y = F.silu(x)
    elif name == "gelu":
        y = F.gelu(x, approximate="tanh")
    elif name == "softmax":
        y = x.softmax(-1)
    elif name == "layernorm":
        y = F.layer_norm(x, (x.numel(),), eps=1e-5)
    elif name == "rmsnorm":
        y = x * (x.square().mean() + 1e-5).rsqrt()
    elif name in {"gemv", "gemm", "batchmatmul"}:
        y = x @ a[1]
    elif name == "linear":
        y = x @ a[1] + a[2]
    elif name in {"conv2d", "depthwise_conv"}:
        y = F.conv2d(x, a[1], groups=32 if name == "depthwise_conv" else 1)
    elif name == "rope":
        pairs = x.reshape(256, 64, 2)
        y = torch.stack(
            (
                pairs[..., 0] * a[1] - pairs[..., 1] * a[2],
                pairs[..., 0] * a[2] + pairs[..., 1] * a[1],
            ),
            -1,
        ).reshape_as(x)
    elif name == "ffn":
        y = (x @ a[1]).relu().half().float() @ a[2]
    elif name == "swiglu":
        y = (F.silu(x @ a[1]) * (x @ a[2])).half().float() @ a[3]
    elif name in {"flash_attn", "gqa"}:
        k, v = a[1:]
        if name == "gqa":
            k = k.repeat_interleave(4, dim=0)
            v = v.repeat_interleave(4, dim=0)
        y = ((x @ k.transpose(-1, -2)) / x.shape[-1] ** 0.5).softmax(-1) @ v
    else:
        raise ValueError(name)
    return y.half()
