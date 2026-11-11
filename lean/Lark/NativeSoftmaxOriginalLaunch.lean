import Lark.NativeSoftmaxOriginalRace

/-! The supported single-row original launch completes with a racy actual
trace. Consequently it cannot satisfy the machine's Correct relation for any
reference specification. The repaired launch remains universally correct. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem original_grid_halt_of_pc (p : Shape) (s : State α)
    (hp : ∀ t, t<p.rows*1024 → s.pc t=normPc false 115) :
    LarkCollective.converged (program false) (List.range (p.rows*1024)) s=some .halt := by
  have hpos : 0<p.rows*1024 := by have h := p.positive; omega
  have hp0 := hp 0 hpos
  have ha : (List.range (p.rows*1024)).all (fun t => s.pc t == s.pc 0)=true := by
    apply List.all_eq_true.mpr
    intro t ht
    simp [hp t (List.mem_range.mp ht),hp0]
  unfold LarkCollective.converged
  rewrite [List.head?_range,if_neg (by omega : p.rows*1024 ≠ 0)]
  simp only [bind,pure,Option.bind,ha,↓reduceIte]
  unfold LarkCollective.parked
  rewrite [hp0,(norm_round_end_codes false).2.2]
  rfl

theorem original_single_row_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (hrows : p.rows=1) :
    LarkCollective.converged (program false) (List.range ((geometry p).grid*(geometry p).block))
      (wholeBlock p false ops input 0 (initial (layout p) input outside))=some .halt := by
  apply original_grid_halt_of_pc p
  intro t ht
  have hb : t<1024 := by rewrite [hrows] at ht; omega
  simpa only [Nat.zero_mul,Nat.zero_add] using whole_block_pc p false ops input 0 t (initial (layout p) input outside) hb

theorem original_single_row_grid_fold (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (hrows : p.rows=1) :
    (List.range (geometry p).grid).foldlM
      (fun s row => LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program false) row fuel.block s)
      (initial (layout p) input outside)=some (wholeBlock p false ops input 0 (initial (layout p) input outside)) := by
  have hg : (geometry p).grid=1 := hrows
  rewrite [hg,show List.range 1=[0] by rfl,List.foldlM_cons,
    initial_whole_block p false ops input outside 0 p.positive]
  rfl

theorem original_single_row_launch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (hrows : p.rows=1) :
    LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel (program false) (initial (layout p) input outside)=
      some (wholeBlock p false ops input 0 (initial (layout p) input outside)) := by
  have hv : ¬ ((geometry p).grid=0 ∨ (geometry p).block=0 ∨ (geometry p).warp ≠ 64 ∨ (geometry p).block%64 ≠ 0) := by
    simp [geometry,hrows]
  rewrite [LarkPartitionCollective.runLaunch,if_neg hv]
  change LarkPartitionCollective.runGrid ops (layout p) (geometry p) fuel (program false) (0+1) _=_
  rewrite [LarkPartitionCollective.runGrid,original_single_row_grid_fold p ops input outside hrows]
  simp only [bind,pure,Option.some_bind,original_single_row_cut p ops input outside hrows,reduceCtorEq,↓reduceIte]

theorem original_single_row_not_correct (p : Shape) (ops : Ops α) (spec : (Nat → Nat → α) → List α)
    (hrows : p.rows=1) :
    ¬ LarkPartitionCollective.Correct ops (layout p) (geometry p) fuel (program false) spec := by
  intro correct
  let input : Nat → Nat → α := fun _ _ => ops.literal 0 1
  let outside : Location → Option α := fun _ => none
  obtain ⟨final,hrun,hrf,_⟩ := correct input outside
  have heq := Option.some.inj (hrun.symm.trans (original_single_row_launch p ops input outside hrows))
  subst final
  rewrite [initial_original_block_race_free_false p ops input outside 0] at hrf
  cases hrf

#print axioms original_grid_halt_of_pc
#print axioms original_single_row_cut
#print axioms original_single_row_grid_fold
#print axioms original_single_row_launch
#print axioms original_single_row_not_correct
end LarkNativeSoftmax
