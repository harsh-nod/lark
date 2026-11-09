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

    def binary(self, op: str, other: Tensor):
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
            raise Refusal("spec-shape", "only scalar broadcasting is implemented")
        return Tensor(
            shape, tuple(node("bin", op, a, b) for a, b in pairs), self.tensor or other.tensor
        )

    def reshape(self, shape):
        if any(type(x) is not int or x <= 0 for x in shape) or math.prod(shape) != len(self.values):
            raise Refusal(
                "spec-shape", "reshape must preserve size and use positive literal dimensions"
            )
        return Tensor(tuple(shape), self.values)

    def sum(self, dim=None):
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
            op = {ast.Add: "add", ast.Sub: "sub", ast.Mult: "mul"}.get(type(x.op))
            if op:
                return a.binary(op, b)
        if isinstance(x, ast.Call) and isinstance(x.func, ast.Attribute):
            f = x.func
            is_torch = isinstance(f.value, ast.Name) and f.value.id == "torch"
            args = list(x.args)
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
            if f.attr == "sum" and not args and set(kw) <= {"dim"}:
                return obj.sum(kw.get("dim"))
            if f.attr == "matmul" and len(args) == 1 and not kw:
                return obj.matmul(self.expr(args[0]))
            if f.attr == "flip" and not kw and len(args) == 1:
                dims = self.constant(args[0])
                if dims != [0] and dims != (0,):
                    raise Refusal("specification", "flip currently supports dims=[0]")
                if len(obj.shape) != 1:
                    raise Refusal("spec-shape", "flip currently requires rank 1")
                return Tensor(obj.shape, obj.values[::-1])
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
            self.env[b.name] = Tensor(b.shape, tuple(node("input", id, i) for i in range(b.size)))
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
