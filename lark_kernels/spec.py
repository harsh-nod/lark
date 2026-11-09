"""Independent, closed PyTorch AST formalization for fixed contiguous tensor shapes."""

from __future__ import annotations

import ast
from dataclasses import dataclass
import itertools
import math

from .ir import Node, Refusal, Task, literal, node


@dataclass(frozen=True)
class Tensor:
    shape: tuple[int, ...]
    values: tuple[Node, ...]
    tensor: bool = True
    dtype: str = "float32"

    def require_float(self):
        if self.dtype != "float32":
            raise Refusal("spec-dtype", "half arithmetic requires an explicit .float() conversion")

    def unary(self, op):
        self.require_float()
        return Tensor(self.shape, tuple(node("un", op, v) for v in self.values), self.tensor)

    def cast(self, dtype):
        if self.dtype == dtype:
            return self
        op = "fromHalf" if dtype == "float32" else "toHalf"
        return Tensor(self.shape, tuple(node("un", op, v) for v in self.values), self.tensor, dtype)

    def binary(self, op: str, other: Tensor):
        self.require_float()
        other.require_float()
        if self.shape == other.shape:
            pairs = zip(self.values, other.values)
            shape = self.shape
        elif not other.shape:
            pairs = ((a, other.values[0]) for a in self.values)
            shape = self.shape
        elif not self.shape:
            pairs = ((self.values[0], b) for b in other.values)
            shape = other.shape
        else:
            rank = max(len(self.shape), len(other.shape))
            left = (1,) * (rank - len(self.shape)) + self.shape
            right = (1,) * (rank - len(other.shape)) + other.shape
            if any(a != b and a != 1 and b != 1 for a, b in zip(left, right)):
                raise Refusal("spec-shape", "incompatible broadcast shapes")
            shape = tuple(max(a, b) for a, b in zip(left, right))

            def offset(coords, dims):
                result = 0
                for i, n in zip(coords, dims):
                    result = result * n + (0 if n == 1 else i)
                return result

            pairs = (
                (self.values[offset(c, left)], other.values[offset(c, right)])
                for c in itertools.product(*(range(n) for n in shape))
            )
        return Tensor(
            shape, tuple(node("bin", op, a, b) for a, b in pairs), self.tensor or other.tensor
        )

    def reshape(self, shape):
        if any(type(x) is not int or x <= 0 for x in shape) or math.prod(shape) != len(self.values):
            raise Refusal(
                "spec-shape", "reshape must preserve size and use positive literal dimensions"
            )
        return Tensor(tuple(shape), self.values, self.tensor, self.dtype)

    def sum(self, dim=None):
        self.require_float()
        if dim is None:
            value = literal(0)
            for v in self.values:
                value = node("bin", "add", value, v)
            return Tensor((), (value,))
        if type(dim) is not int or not 0 <= dim < len(self.shape):
            raise Refusal("spec-shape", "sum dimension is out of range")
        shape = self.shape[:dim] + self.shape[dim + 1 :]
        output = []
        for coords in itertools.product(*(range(n) for n in shape)):
            value = literal(0)
            for k in range(self.shape[dim]):
                full = coords[:dim] + (k,) + coords[dim:]
                flat = 0
                for i, n in zip(full, self.shape):
                    flat = flat * n + i
                value = node("bin", "add", value, self.values[flat])
            output.append(value)
        return Tensor(shape, tuple(output))

    def matmul(self, other):
        self.require_float()
        other.require_float()
        if len(self.shape) == len(other.shape) == 3:
            if self.shape[0] != other.shape[0] or self.shape[2] != other.shape[1]:
                raise Refusal("spec-shape", "bmm requires matching batches and inner dimensions")
            batch, m, k = self.shape
            _, _, n = other.shape
            result = []
            for b in range(batch):
                a = Tensor((m, k), self.values[b * m * k : (b + 1) * m * k])
                rhs = Tensor((k, n), other.values[b * k * n : (b + 1) * k * n])
                result.extend(a.matmul(rhs).values)
            return Tensor((batch, m, n), tuple(result))
        if len(self.shape) != 2 or len(other.shape) != 2 or self.shape[1] != other.shape[0]:
            raise Refusal("spec-shape", "matmul requires two compatible rank-2 tensors")
        m, k = self.shape
        _, n = other.shape
        values = []
        for i in range(m):
            for j in range(n):
                value = literal(0)
                for p in range(k):
                    product = node("bin", "mul", self.values[i * k + p], other.values[p * n + j])
                    value = node("bin", "add", value, product)
                values.append(value)
        return Tensor((m, n), tuple(values))

    def conv2d(self, weight, groups=1):
        self.require_float()
        weight.require_float()
        if len(self.shape) != 4 or len(weight.shape) != 4 or type(groups) is not int or groups <= 0:
            raise Refusal(
                "spec-shape", "conv2d requires NCHW inputs, OIHW weights, positive groups"
            )
        batch, cin, h, w = self.shape
        cout, cg, kh, kw = weight.shape
        if cin % groups or cout % groups or cg != cin // groups or h < kh or w < kw:
            raise Refusal("spec-shape", "invalid convolution shapes or groups")
        values = []
        for b, oc, y, x in itertools.product(
            range(batch), range(cout), range(h - kh + 1), range(w - kw + 1)
        ):
            acc = literal(0)
            group = oc // (cout // groups)
            for c, ky, kx in itertools.product(range(cg), range(kh), range(kw)):
                lhs = self.values[((b * cin + group * cg + c) * h + y + ky) * w + x + kx]
                rhs = weight.values[((oc * cg + c) * kh + ky) * kw + kx]
                acc = node("bin", "add", acc, node("bin", "mul", lhs, rhs))
            values.append(acc)
        return Tensor((batch, cout, h - kh + 1, w - kw + 1), tuple(values))

    def axis(self, dim):
        if type(dim) is not int or not -len(self.shape) <= dim < len(self.shape):
            raise Refusal("spec-shape", "dimension is out of range")
        return dim % len(self.shape)

    def reduce(self, kind, dim=None, keepdim=False):
        self.require_float()
        if type(keepdim) is not bool:
            raise Refusal("spec-shape", "keepdim must be a literal boolean")
        if dim is None:
            values = self.values
            acc = literal(0) if kind == "add" else values[0]
            for v in values if kind == "add" else values[1:]:
                acc = node("bin", kind, acc, v)
            return Tensor((1,) * len(self.shape) if keepdim else (), (acc,))
        dim = self.axis(dim)
        shape = self.shape[:dim] + self.shape[dim + 1 :]
        output = []
        for coords in itertools.product(*(range(n) for n in shape)):
            values = []
            for k in range(self.shape[dim]):
                full = coords[:dim] + (k,) + coords[dim:]
                values.append(self.values[flat_index(full, self.shape)])
            acc = literal(0) if kind == "add" else values[0]
            for value in values if kind == "add" else values[1:]:
                acc = node("bin", kind, acc, value)
            output.append(acc)
        if keepdim:
            shape = self.shape[:dim] + (1,) + self.shape[dim + 1 :]
        return Tensor(shape, tuple(output))

    def mean(self, dim=None, keepdim=False):
        n = len(self.values) if dim is None else self.shape[self.axis(dim)]
        return self.reduce("add", dim, keepdim).binary("div", scalar(n))

    def softmax(self, dim):
        dim = self.axis(dim)
        shifted = self.binary("sub", self.reduce("max", dim, True)).unary("exp")
        return shifted.binary("div", shifted.reduce("add", dim, True))

    def silu(self):
        denominator = scalar(1).binary("add", scalar(0).binary("sub", self).unary("exp"))
        return self.binary("mul", scalar(1).binary("div", denominator))

    def gelu(self):
        cubic = scalar("0.044715").binary("mul", self).binary("mul", self).binary("mul", self)
        arg = scalar("0.7978845608028654").binary("mul", self.binary("add", cubic))
        return (
            scalar("0.5")
            .binary("mul", self)
            .binary("mul", scalar(1).binary("add", arg.unary("tanh")))
        )

    def norm(self, normalized_shape, eps, centered):
        if tuple(normalized_shape) != self.shape[-1:]:
            raise Refusal("spec-shape", "norm supports one trailing normalized dimension")
        if type(eps) not in {int, float} or not math.isfinite(eps) or eps <= 0:
            raise Refusal("specification", "norm requires an explicit positive finite epsilon")
        value = self.binary("sub", self.mean(-1, True)) if centered else self
        variance = value.binary("mul", value).mean(-1, True)
        return value.binary("mul", variance.binary("add", scalar(str(eps))).unary("rsqrt"))

    def transpose(self, d0, d1):
        d0, d1 = self.axis(d0), self.axis(d1)
        shape = list(self.shape)
        shape[d0], shape[d1] = shape[d1], shape[d0]
        values = []
        for coords in itertools.product(*(range(n) for n in shape)):
            src = list(coords)
            src[d0], src[d1] = src[d1], src[d0]
            values.append(self.values[flat_index(src, self.shape)])
        return Tensor(tuple(shape), tuple(values), self.tensor, self.dtype)

    def select(self, dim, index):
        dim = self.axis(dim)
        if type(index) is not int or not -self.shape[dim] <= index < self.shape[dim]:
            raise Refusal("spec-shape", "select index is out of range")
        index %= self.shape[dim]
        shape = self.shape[:dim] + self.shape[dim + 1 :]
        values = tuple(
            self.values[flat_index(c[:dim] + (index,) + c[dim:], self.shape)]
            for c in itertools.product(*(range(n) for n in shape))
        )
        return Tensor(shape, values, self.tensor, self.dtype)

    def repeat_interleave(self, repeats, dim):
        dim = self.axis(dim)
        if type(repeats) is not int or not 1 <= repeats <= 64:
            raise Refusal("spec-shape", "repeat_interleave requires a positive bounded literal")
        shape = list(self.shape)
        shape[dim] *= repeats
        values = []
        for coords in itertools.product(*(range(n) for n in shape)):
            src = list(coords)
            src[dim] //= repeats
            values.append(self.values[flat_index(src, self.shape)])
        return Tensor(tuple(shape), tuple(values), self.tensor, self.dtype)


def scalar(value):
    return Tensor((), (literal(value),), False)


def flat_index(coords, shape):
    result = 0
    for c, n in zip(coords, shape):
        result = result * n + c
    return result


def stack(tensors, dim):
    if not tensors or any(
        (t.shape, t.dtype) != (tensors[0].shape, tensors[0].dtype) for t in tensors
    ):
        raise Refusal("spec-shape", "stack requires equally shaped and typed tensors")
    t = tensors[0]
    if type(dim) is not int or not -len(t.shape) - 1 <= dim <= len(t.shape):
        raise Refusal("spec-shape", "stack dimension out of range")
    dim %= len(t.shape) + 1
    shape = t.shape[:dim] + (len(tensors),) + t.shape[dim:]
    values = tuple(
        tensors[c[dim]].values[flat_index(c[:dim] + c[dim + 1 :], t.shape)]
        for c in itertools.product(*(range(n) for n in shape))
    )
    return Tensor(shape, values, True, t.dtype)


class SpecReader:
    def __init__(self, source: str, task: Task):
        self.source, self.task = source, task
        self.env: dict[str, Tensor] = {}

    def constant(self, x):
        try:
            return ast.literal_eval(x)
        except (ValueError, TypeError):
            raise Refusal("specification", "expected literal shape or dimension") from None

    def expr(self, x):
        if isinstance(x, ast.Name) and x.id in self.env:
            return self.env[x.id]
        if isinstance(x, ast.Constant) and type(x.value) in {int, float}:
            return Tensor((), (literal(ast.get_source_segment(self.source, x)),), False)
        if isinstance(x, ast.UnaryOp) and isinstance(x.op, ast.USub):
            return Tensor((), (literal(0),), False).binary("sub", self.expr(x.operand))
        if isinstance(x, ast.BinOp):
            a, b = self.expr(x.left), self.expr(x.right)
            if isinstance(x.op, ast.MatMult):
                return a.matmul(b)
            op = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul", ast.Div: "div"}.get(type(x.op))
            if op:
                return a.binary(op, b)
        if isinstance(x, ast.Call) and isinstance(x.func, ast.Attribute):
            f = x.func

            def qualified(n):
                if isinstance(n, ast.Name):
                    return n.id
                if isinstance(n, ast.Attribute):
                    return qualified(n.value) + "." + n.attr
                return ""

            owner = qualified(f.value)
            if owner == "torch.nn.functional" and f.attr not in {
                "relu",
                "silu",
                "gelu",
                "layer_norm",
                "rms_norm",
                "softmax",
            }:
                raise Refusal("specification", "unsupported torch.nn.functional call")
            is_torch = owner in {"torch", "torch.nn.functional"}
            args = list(x.args)
            if owner == "torch" and f.attr == "stack":
                if len(args) != 1 or not isinstance(args[0], (ast.Tuple, ast.List)):
                    raise Refusal("specification", "stack requires a literal sequence of tensors")
                kw = {k.arg: self.constant(k.value) for k in x.keywords}
                if len(kw) != len(x.keywords) or set(kw) - {"dim"}:
                    raise Refusal("specification", "invalid stack options")
                return stack([self.expr(v) for v in args[0].elts], kw.get("dim", 0))
            if is_torch:
                if not args:
                    raise Refusal("specification", "torch calls require a tensor")
                obj = self.expr(args.pop(0))
            else:
                obj = self.expr(f.value)
            if not obj.tensor:
                raise Refusal("specification", "tensor operation applied to a Python scalar")
            kw = {k.arg: self.constant(k.value) for k in x.keywords}
            if len(kw) != len(x.keywords):
                raise Refusal("specification", "duplicate keywords")
            if f.attr in {"float", "half"} and not args and not kw and not is_torch:
                return obj.cast("float32" if f.attr == "float" else "float16")
            if f.attr in {"exp", "tanh", "rsqrt"} and not args and not kw:
                return obj.unary(f.attr)
            if f.attr == "square" and not args and not kw:
                return obj.binary("mul", obj)
            if f.attr == "sigmoid" and not args and not kw:
                return scalar(1).binary(
                    "div", scalar(1).binary("add", scalar(0).binary("sub", obj).unary("exp"))
                )
            if f.attr == "silu" and owner == "torch.nn.functional" and not args and not kw:
                return obj.silu()
            if (
                f.attr == "gelu"
                and owner == "torch.nn.functional"
                and not args
                and kw == {"approximate": "tanh"}
            ):
                return obj.gelu()
            if f.attr in {"layer_norm", "rms_norm"} and is_torch:
                if len(args) == 1 and set(kw) == {"eps"}:
                    shape = self.constant(args[0])
                    if isinstance(shape, (list, tuple)):
                        return obj.norm(shape, kw["eps"], f.attr == "layer_norm")
            if f.attr in {"mean", "amax", "softmax"}:
                if len(args) <= 1 and set(kw) <= {"dim", "keepdim"}:
                    if args and "dim" in kw:
                        raise Refusal("specification", "duplicate dimension")
                    dim = self.constant(args[0]) if args else kw.get("dim")
                    if f.attr == "softmax" and dim is not None and "keepdim" not in kw:
                        return obj.softmax(dim)
                    if f.attr == "mean":
                        return obj.mean(dim, kw.get("keepdim", False))
                    if f.attr == "amax":
                        return obj.reduce("max", dim, kw.get("keepdim", False))
            if f.attr in {"transpose", "select"} and len(args) == 2 and not kw:
                return getattr(obj, f.attr)(self.constant(args[0]), self.constant(args[1]))
            if f.attr == "repeat_interleave" and len(args) == 1 and set(kw) == {"dim"}:
                return obj.repeat_interleave(self.constant(args[0]), kw["dim"])
            if f.attr == "relu" and not args and not kw:
                return obj.binary("max", Tensor((), (literal(0),)))
            if f.attr == "maximum" and len(args) == 1 and not kw and is_torch:
                return obj.binary("max", self.expr(args[0]))
            if f.attr in {"reshape", "view"} and not kw:
                if is_torch and (
                    f.attr == "view"
                    or len(args) != 1
                    or not isinstance(self.constant(args[0]), (list, tuple))
                ):
                    raise Refusal(
                        "specification",
                        "torch.reshape requires one shape tuple; view is a tensor method",
                    )
                shape = [self.constant(a) for a in args]
                if len(shape) == 1 and isinstance(shape[0], (list, tuple)):
                    shape = shape[0]
                return obj.reshape(shape)
            if f.attr == "sum" and not args and set(kw) <= {"dim", "keepdim"}:
                return obj.reduce("add", kw.get("dim"), kw.get("keepdim", False))
            if f.attr in {"matmul", "bmm"} and len(args) == 1 and not kw:
                rhs = self.expr(args[0])
                if f.attr == "bmm" and (len(obj.shape) != 3 or len(rhs.shape) != 3):
                    raise Refusal("spec-shape", "bmm requires two rank-3 tensors")
                return obj.matmul(rhs)
            if f.attr == "conv2d" and is_torch and len(args) == 1 and set(kw) <= {"groups"}:
                return obj.conv2d(self.expr(args[0]), kw.get("groups", 1))
            if f.attr == "flip" and not kw and len(args) == 1:
                dims = self.constant(args[0])
                if dims != [0] and dims != (0,):
                    raise Refusal("specification", "flip currently supports dims=[0]")
                if len(obj.shape) != 1:
                    raise Refusal("spec-shape", "flip currently requires rank 1")
                return Tensor(obj.shape, obj.values[::-1], obj.tensor, obj.dtype)
        raise Refusal(
            "specification",
            f"unsupported reference construct: {ast.dump(x, include_attributes=False)}",
        )

    def read(self):
        tree = ast.parse(self.source)
        funcs = [s for s in tree.body if isinstance(s, ast.FunctionDef)]
        if len(funcs) != 1 or any(
            not isinstance(s, (ast.FunctionDef, ast.Import)) for s in tree.body
        ):
            raise Refusal("specification", "reference must have imports and exactly one function")
        for s in tree.body:
            if isinstance(s, ast.Import) and any(a.name != "torch" or a.asname for a in s.names):
                raise Refusal("specification", "only 'import torch' is supported")
        f = funcs[0]
        if (
            f.decorator_list
            or f.args.defaults
            or f.args.kw_defaults
            or f.args.kwonlyargs
            or f.args.posonlyargs
            or f.args.vararg
            or f.args.kwarg
        ):
            raise Refusal(
                "specification", "decorators, defaults, and variadic arguments are unsupported"
            )
        inputs = [(id, b) for id, b in enumerate(self.task.buffers) if b.role == "input"]
        if [a.arg for a in f.args.args] != [b.name for _, b in inputs]:
            raise Refusal(
                "spec-signature", "reference arguments must match input buffers in task order"
            )
        for id, b in inputs:
            if b.name == "torch":
                raise Refusal("specification", "input cannot shadow the torch namespace")
            self.env[b.name] = Tensor(
                b.shape, tuple(node("input", id, i) for i in range(b.size)), True, b.dtype
            )
        returned = None
        for s in f.body:
            if returned is not None:
                raise Refusal("specification", "statements after return are unsupported")
            if (
                isinstance(s, ast.Assign)
                and len(s.targets) == 1
                and isinstance(s.targets[0], ast.Name)
            ):
                if s.targets[0].id == "torch":
                    raise Refusal("specification", "assignment cannot shadow the torch namespace")
                self.env[s.targets[0].id] = self.expr(s.value)
            elif isinstance(s, ast.Return):
                returned = (
                    [self.expr(v) for v in s.value.elts]
                    if isinstance(s.value, ast.Tuple)
                    else [self.expr(s.value)]
                )
            else:
                raise Refusal(
                    "specification", "reference bodies support tensor assignments and a return"
                )
        outputs = [b for b in self.task.buffers if b.role == "output"]
        if returned is None or len(returned) != len(outputs):
            raise Refusal("spec-signature", "reference must return one tensor per output buffer")
        for value, b in zip(returned, outputs):
            if value.dtype != b.dtype:
                raise Refusal(
                    "spec-dtype", "output dtype differs from task; explicit conversion required"
                )
            if not value.tensor:
                raise Refusal(
                    "specification", "outputs must be tensors, not Python scalar constants"
                )
            # A scalar return may occupy a task buffer with shape [1].
            if value.shape != b.shape and not (value.shape == () and b.shape == (1,)):
                raise Refusal(
                    "spec-shape", f"output {b.name}: expected {b.shape}, got {value.shape}"
                )
        return [v for t in returned for v in t.values]


def read_spec(source: str, task: Task):
    return SpecReader(source, task).read()
