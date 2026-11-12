import LarkReal.NativeSglangRmsNormTree

/-! The source's paired-square accumulation and two logical32 reductions
cover every dense row input exactly once in the exact-real interpretation.
-/
namespace LarkReal.NativeSglangRmsNorm
open LarkNativeSglangRmsNorm
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def rowSquare (input : Nat → Nat → ℝ) (row col : Nat) : ℝ :=
  let x := input 1 (row*16384+col)
  x*x

theorem pair_square_sum (input : Nat → Nat → ℝ) (row tid iteration pair : Nat) :
    pairSquare ops input row tid iteration pair=
      ((List.range' (pair*2) 2).map (fun component => rowSquare input row (column tid iteration component))).sum := by
  simp [pairSquare,pairLoaded,ops,rowSquare,address,List.range'_succ]

theorem pair_fold_sum (input : Nat → Nat → ℝ) (row tid iteration pair remaining : Nat) (acc : ℝ) :
    pairFold ops input row tid iteration pair remaining acc=
      acc+((List.range' (pair*2) (remaining*2)).map (fun component => rowSquare input row (column tid iteration component))).sum := by
  induction remaining generalizing pair acc with
  | zero => simp [pairFold]
  | succ remaining ih =>
      rw [pairFold,ih]
      change (acc+pairSquare ops input row tid iteration pair)+_=_
      have ranges : List.range' (pair*2) 2 ++ List.range' ((pair+1)*2) (remaining*2)=
          List.range' (pair*2) ((remaining+1)*2) := by
        have h := List.range'_append (s := pair*2) (m := 2) (n := remaining*2) (step := 1)
        simpa only [Nat.one_mul,Nat.mul_one,show pair*2+2=(pair+1)*2 by omega,
          show 2+remaining*2=(remaining+1)*2 by omega] using h
      rw [pair_square_sum,← ranges,List.map_append,List.sum_append]
      exact add_assoc _ _ _

theorem thread_sum (input : Nat → Nat → ℝ) (row tid : Nat) :
    threadSum ops input row tid=
      ((List.range' (tid*8) 8).map (rowSquare input row)).sum+
      ((List.range' (8192+tid*8) 8).map (rowSquare input row)).sum := by
  unfold threadSum
  rw [pair_fold_sum,pair_fold_sum]
  simp [ops,List.range'_eq_map_range,List.map_map,Function.comp_def,column,
    Nat.add_mul,Nat.add_comm,Nat.add_left_comm]

theorem sum_blocks (values : Nat → ℝ) (n width start : Nat) :
    ((List.range n).map (fun block => ((List.range' (start+block*width) width).map values).sum)).sum=
      ((List.range' start (n*width)).map values).sum := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ,List.map_append,List.sum_append]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,ih]
      rw [← List.sum_append,← List.map_append]
      have he := List.range'_append (s := start) (m := n*width) (n := width) (step := 1)
      simpa only [Nat.one_mul,Nat.add_mul,Nat.one_mul] using
        congrArg (fun xs : List Nat => (xs.map values).sum) he

theorem partials_sum (input : Nat → Nat → ℝ) (row : Nat) :
    ((List.range 32).map (blockPartialValue ops input row)).sum=
      ((List.range 1024).map (threadSum ops input row)).sum := by
  have hparts : ((List.range 32).map (blockPartialValue ops input row)).sum=
      ((List.range 32).map (fun warp =>
        ((List.range' (0+warp*32) 32).map (threadSum ops input row)).sum)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro warp hw
    simpa only [Nat.zero_add] using partial_sum input row warp
  rw [hparts,sum_blocks]
  change ((List.range' 0 1024).map (threadSum ops input row)).sum=_
  rw [← List.range_eq_range']

theorem block_sum (input : Nat → Nat → ℝ) (row : Nat) :
    ((List.range 32).map (blockPartialValue ops input row)).sum=
      ((List.range 16384).map (rowSquare input row)).sum := by
  rw [partials_sum]
  have hthreads : ((List.range 1024).map (threadSum ops input row)).sum=
      ((List.range 1024).map (fun tid =>
        ((List.range' (0+tid*8) 8).map (rowSquare input row)).sum+
        ((List.range' (8192+tid*8) 8).map (rowSquare input row)).sum)).sum := by
    apply congrArg List.sum
    apply List.map_congr_left
    intro tid ht
    simpa only [Nat.zero_add] using thread_sum input row tid
  rw [hthreads,List.sum_map_add,sum_blocks,sum_blocks,← List.sum_append,← List.map_append]
  have he := List.range'_append (s := 0) (m := 8192) (n := 8192) (step := 1)
  simpa only [Nat.zero_add,Nat.one_mul,← List.range_eq_range'] using
    congrArg (fun xs : List Nat => (xs.map (rowSquare input row)).sum) he

theorem total_from_lane (input : Nat → Nat → ℝ) (row lane : Nat) (hl : lane<32) :
    reductionValues ops (blockPartialValue ops input row) 5 lane=
      ((List.range 16384).map (rowSquare input row)).sum := by
  rw [reduction_sum32 _ lane hl,block_sum]

#print axioms pair_square_sum
#print axioms pair_fold_sum
#print axioms thread_sum
#print axioms sum_blocks
#print axioms partials_sum
#print axioms block_sum
#print axioms total_from_lane
end LarkReal.NativeSglangRmsNorm
