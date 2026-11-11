"""Exact-real bridge for the fully bound repaired source and grid."""

EXTRA = r'''import Main
import LarkReal.NativeSoftmaxCanonical
open LarkNonlinear LarkNativeSoftmax LarkReal.NativeSoftmax
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem source_canonical_correct (p : Shape) (seed : ℝ) :
    LarkPartitionCollective.Correct (softmaxOps seed) (sourceLayout p) (sourceGeometry p)
      sourceFuel sourceFixed (canonicalSpec p) := by
  rewrite [←source_spec_canonical p seed]
  exact source_fixed_grid_correct p (softmaxOps seed)

theorem source_canonical_extract (p : Shape) (seed : ℝ) (input : Nat → Nat → ℝ)
    (outside : Location → Option ℝ) :
    extract (sourceLayout p) (sourceFixedGrid p (softmaxOps seed) input outside)=some (canonicalSpec p input) := by
  rewrite [source_fixed_grid_extract,source_spec_canonical]
  rfl

theorem source_canonical_output (p : Shape) (seed : ℝ) (input : Nat → Nat → ℝ)
    (outside : Location → Option ℝ) (offset : Nat) (ho : offset<p.rows*50257) :
    (sourceFixedGrid p (softmaxOps seed) input outside).memory (globalCell 0 offset)=
      some (canonicalOutput input (offset/50257) (offset%50257)) := by
  rewrite [source_fixed_grid_output p (softmaxOps seed) input outside offset ho]
  unfold sourceOutputValue
  rewrite [source_output_canonical seed input (offset/50257) (offset%50257) (Nat.mod_lt _ (by decide))]
  rfl

theorem sum_real_ones (xs : List ι) :
    (xs.map fun _ => (1 : ℝ)).sum=(xs.length : ℝ) := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one,ih]
    exact add_comm _ _

theorem canonical_uniform (row col : Nat) :
    canonicalOutput (fun _ _ => (0 : ℝ)) row col=1/50257 := by
  unfold canonicalOutput
  simp only [Real.exp_zero]
  rewrite [sum_real_ones,List.length_range]
  rfl

theorem source_uniform_output (p : Shape) (seed : ℝ) (outside : Location → Option ℝ)
    (offset : Nat) (ho : offset<p.rows*50257) :
    (sourceFixedGrid p (softmaxOps seed) (fun _ _ => 0) outside).memory (globalCell 0 offset)=some (1/50257) := by
  rewrite [source_canonical_output p seed (fun _ _ => 0) outside offset ho,canonical_uniform]
  rfl

#print axioms source_canonical_correct
#print axioms source_canonical_extract
#print axioms source_canonical_output
#print axioms sum_real_ones
#print axioms canonical_uniform
#print axioms source_uniform_output
'''
