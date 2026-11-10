# Same-source dot-product ablation

This compares the existing concrete-execution checker with counted-loop induction
on the same FP16 GEMV sources. It is an independent scaling experiment, not the
paper's original agent segmentation/flat ablation. [Results](RESULTS.md).

```bash
python3 reproduction/dot_ablation/run.py --output /tmp/dot-ablation \
  --lean /path/to/lean-4.19.0/bin/lean --flat-timeout 30
```

All successful flat and inductive certificates are independently rechecked.
The eight pairs use K=1,2,4,8,16,32,64,128 and two output rows. Failed bounded
proofs, timeout flags, source hashes and the exact standalone projects remain
in the output. Archives contain the source snapshot actually loaded by the run.

`summarize.py` reconstructs every archived statement from its source/reference/task
and renders the table/figure with Matplotlib (recorded version in validation.json).
Proof checking itself has no Matplotlib dependency. Largest full-size/symbolic
GEMV certificates remain in the separate [reduction study](../reduction/RESULTS.md).
