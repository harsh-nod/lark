import LarkReal.NativeSoftmaxReduction

/-! Exact enumeration of the 7x8 components of each of the 1024 source
threads. Inactive columns contribute zero, so the actual reduction equals
the sum of precisely the 50257 real exponentials in one row. -/
namespace LarkReal.NativeSoftmax
open LarkNonlinear LarkNativeSoftmax
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem real_sum_comm (xs : List ι) (ys : List κ) (f : ι → κ → ℝ) :
    (xs.map fun x => (ys.map (f x)).sum).sum=
      (ys.map fun y => (xs.map fun x => f x y).sum).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    rewrite [List.sum_map_add,←ih]
    rfl

noncomputable def clippedExp (input : Nat → Nat → ℝ) (row : Nat) (shift : ℝ) (col : Nat) : ℝ :=
  if col<50257 then expTerm input row shift col else 0

theorem round_sum_columns (input : Nat → Nat → ℝ) (row tid iteration : Nat) (shift : ℝ) :
    roundTerm input row tid iteration shift=
      ((List.range' (0+iteration*8) 8).map fun k => clippedExp input row shift (tid+k*1024)).sum := by
  simp only [roundTerm,List.range'_eq_map_range,List.map_map,Function.comp_def,
    Nat.one_mul,Nat.zero_add]
  apply congrArg List.sum
  apply List.map_congr_left
  intro component hc
  rfl

theorem thread_sum_columns (seed : ℝ) (input : Nat → Nat → ℝ) (row tid : Nat) :
    threadExpSum (softmaxOps seed) input row tid=
      ((List.range 56).map fun k => clippedExp input row
        (rowMaximum (softmaxOps seed) input row) (tid+k*1024)).sum := by
  rewrite [thread_sum_real]
  have hr : (List.range 7).map (fun it => roundTerm input row tid it
      (rowMaximum (softmaxOps seed) input row))=
    (List.range 7).map (fun it => ((List.range' (0+it*8) 8).map fun k =>
      clippedExp input row (rowMaximum (softmaxOps seed) input row) (tid+k*1024)).sum) := by
    apply List.map_congr_left
    intro it hi
    exact round_sum_columns input row tid it _
  rewrite [hr,real_sum_blocks,←List.range_eq_range']
  rfl

theorem real_sum_truncate (f : Nat → ℝ) (m n : Nat) (hmn : m≤n) :
    ((List.range n).map fun col => if col<m then f col else 0).sum=
      ((List.range m).map f).sum := by
  let extra := n-m
  have hn : n=m+extra := by dsimp [extra]; omega
  rewrite [hn]
  induction extra with
  | zero =>
    simp only [Nat.add_zero]
    apply congrArg List.sum
    apply List.map_congr_left
    intro col hc
    exact if_pos (List.mem_range.mp hc)
  | succ extra ih =>
    rewrite [show m+(extra+1)=(m+extra)+1 by omega,List.range_succ,List.map_append,List.sum_append,ih]
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rewrite [if_neg (by omega : ¬m+extra<m),add_zero]
    rfl

theorem row_sum_exponentials (seed : ℝ) (input : Nat → Nat → ℝ) (row : Nat) :
    rowExpSum (softmaxOps seed) input row=
      ((List.range 50257).map (expTerm input row (rowMaximum (softmaxOps seed) input row))).sum := by
  rewrite [row_sum_threads_real]
  have ht : (List.range 1024).map (threadExpSum (softmaxOps seed) input row)=
      (List.range 1024).map (fun tid => ((List.range 56).map fun k =>
        clippedExp input row (rowMaximum (softmaxOps seed) input row) (tid+k*1024)).sum) := by
    apply List.map_congr_left
    intro tid ht
    exact thread_sum_columns seed input row tid
  rewrite [ht,real_sum_comm]
  have hb : (List.range 56).map (fun k => ((List.range 1024).map fun tid =>
      clippedExp input row (rowMaximum (softmaxOps seed) input row) (tid+k*1024)).sum)=
      (List.range 56).map (fun k => ((List.range' (0+k*1024) 1024).map
        (clippedExp input row (rowMaximum (softmaxOps seed) input row))).sum) := by
    apply List.map_congr_left
    intro k hk
    simp only [List.range'_eq_map_range,List.map_map,Function.comp_def,Nat.one_mul,Nat.zero_add]
    apply congrArg List.sum
    apply List.map_congr_left
    intro tid ht
    rewrite [Nat.add_comm tid]
    rfl
  rewrite [hb,real_sum_blocks,←List.range_eq_range']
  exact real_sum_truncate (expTerm input row (rowMaximum (softmaxOps seed) input row)) 50257 (56*1024) (by decide)

#print axioms real_sum_comm
#print axioms round_sum_columns
#print axioms thread_sum_columns
#print axioms real_sum_truncate
#print axioms row_sum_exponentials
end LarkReal.NativeSoftmax
