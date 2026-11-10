import LarkReal.Ops
open LarkReal

example : nonassociativeOps.add (nonassociativeOps.add 1 2) 3 =
    nonassociativeOps.add 1 (nonassociativeOps.add 2 3) := by decide
