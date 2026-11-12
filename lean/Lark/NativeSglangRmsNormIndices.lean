import Lark.NativeSglangRmsNormFrame

/-! Native lane/warp identifiers survive all preload and paired-square loops. -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] inputCacheComponents weightCacheComponents pairs

def NativeIndices (t : Nat) (s : State α) : Prop :=
  s.indices t 0 = some ((t / 1024 : Nat) : Int) ∧
  s.indices t 1 = some ((t % 1024 : Nat) : Int) ∧
  s.indices t 2 = some (((t % 1024) % 32 : Nat) : Int) ∧
  s.indices t 3 = some (((t % 1024) / 32 : Nat) : Int)

theorem input_after_low (input : Nat → Nat → α) (row tid iteration component t q : Nat)
    (s : State α) (hq : q < 4) :
    (inputCacheAfter input row tid iteration component t s).indices t q = s.indices t q := by
  have h5 : q ≠ 5 := by omega
  have h6 : q ≠ 6 := by omega
  have h7 : q ≠ 7 := by omega
  have h8 : q ≠ 8 := by omega
  simp [inputCacheAfter,setIndex,cacheWritten,record,advance,h5,h6,h7,h8]

theorem input_components_low (input : Nat → Nat → α)
    (row tid iteration t component remaining q : Nat) (s : State α) (hq : q < 4) :
    (inputCacheComponents input row tid iteration t component remaining s).indices t q = s.indices t q := by
  induction remaining generalizing component s with
  | zero => simp only [inputCacheComponents]
  | succ remaining ih => simp only [inputCacheComponents,ih,input_after_low input row tid iteration component t q s hq]

theorem input_round_low (input : Nat → Nat → α) (row tid iteration t q : Nat)
    (s : State α) (hq : q < 4) :
    (inputCacheRound input row tid iteration t s).indices t q = s.indices t q := by
  have h4 : q ≠ 4 := by omega
  have h5 : q ≠ 5 := by omega
  have h := input_components_low input row tid iteration t 0 8 q (inputCacheEntry t s) hq
  simpa [inputCacheRound,inputCacheExit,inputCacheEntry,setIndex,advance,h4,h5] using h

theorem input_preloads_low (input : Nat → Nat → α) (t q : Nat) (s : State α) (hq : q < 4) :
    (inputPreloads input t s).indices t q = (initialized t s).indices t q := by
  let s0 := initialized t s
  let s1 := inputCacheRound input (t / 1024) (t % 1024) 0 t s0
  exact (input_round_low input (t / 1024) (t % 1024) 1 t q s1 hq).trans
    (input_round_low input (t / 1024) (t % 1024) 0 t q s0 hq)

theorem weight_after_low (input : Nat → Nat → α) (tid iteration component t q : Nat)
    (s : State α) (hq : q < 4) :
    (weightCacheAfter input tid iteration component t s).indices t q = s.indices t q := by
  have h10 : q ≠ 10 := by omega
  have h11 : q ≠ 11 := by omega
  have h12 : q ≠ 12 := by omega
  simp [weightCacheAfter,setIndex,cacheWritten,record,advance,h10,h11,h12]

theorem weight_components_low (input : Nat → Nat → α)
    (row tid iteration t component remaining q : Nat) (s : State α) (hq : q < 4) :
    (weightCacheComponents input row tid iteration t component remaining s).indices t q = s.indices t q := by
  induction remaining generalizing component s with
  | zero => simp only [weightCacheComponents]
  | succ remaining ih => simp only [weightCacheComponents,ih,weight_after_low input tid iteration component t q s hq]

theorem weight_round_low (input : Nat → Nat → α) (row tid iteration t q : Nat)
    (s : State α) (hq : q < 4) :
    (weightCacheRound input row tid iteration t s).indices t q = s.indices t q := by
  have h9 : q ≠ 9 := by omega
  have h10 : q ≠ 10 := by omega
  have h := weight_components_low input row tid iteration t 0 8 q (weightCacheEntry t s) hq
  simpa [weightCacheRound,weightCacheExit,weightCacheEntry,setIndex,advance,h9,h10] using h

theorem preloads_low (input : Nat → Nat → α) (t q : Nat) (s : State α) (hq : q < 4) :
    (preloads input t s).indices t q = (initialized t s).indices t q := by
  let si := inputPreloads input t s
  let s0 := setIndex si t 9 0 17
  let s1 := weightCacheRound input (t / 1024) (t % 1024) 0 t s0
  have h9 : q ≠ 9 := by omega
  have h0 : s0.indices t q = si.indices t q := by simp [s0,setIndex,advance,h9]
  exact (weight_round_low input (t / 1024) (t % 1024) 1 t q s1 hq).trans
    ((weight_round_low input (t / 1024) (t % 1024) 0 t q s0 hq).trans
      (h0.trans (input_preloads_low input t q s hq)))

theorem pair_after_low (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t q : Nat) (acc : α) (s : State α) (hq : q < 4) :
    (pairAfter ops input row tid iteration pair t acc s).indices t q = s.indices t q := by
  have h13 : q ≠ 13 := by omega
  have h14 : q ≠ 14 := by omega
  have h15 : q ≠ 15 := by omega
  simp [pairAfter,setIndex,setReg,record,advance,h13,h14,h15]

theorem pairs_low (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining q : Nat) (acc : α) (s : State α) (hq : q < 4) :
    (pairs ops input row tid iteration t pair remaining acc s).indices t q = s.indices t q := by
  induction remaining generalizing pair acc s with
  | zero => simp only [pairs]
  | succ remaining ih => simp only [pairs,ih,pair_after_low ops input row tid iteration pair t q acc s hq]

theorem round_low (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t q : Nat) (acc : α) (s : State α) (hq : q < 4) :
    (roundAfter ops input row tid iteration t acc s).indices t q = s.indices t q := by
  have h13 : q ≠ 13 := by omega
  have h14 : q ≠ 14 := by omega
  have h := pairs_low ops input row tid iteration t 0 4 q acc (beginRound t s) hq
  simpa [roundAfter,endRound,beginRound,setIndex,advance,h13,h14] using h

theorem prefix_low_indices (ops : Ops α) (input : Nat → Nat → α)
    (t q : Nat) (s : State α) (hq : q < 4) :
    (prefixState ops input t s).indices t q = (initialized t s).indices t q := by
  let zero := ops.literal 0 1
  let s0 := sumStarted ops t (preloads input t s)
  let s1 := roundAfter ops input (t / 1024) (t % 1024) 0 t zero s0
  have h13 : q ≠ 13 := by omega
  have h0 : s0.indices t q = (preloads input t s).indices t q := by
    simp [s0,sumStarted,setIndex,setReg,advance,h13]
  exact (round_low ops input (t / 1024) (t % 1024) 1 t q
    (pairFold ops input (t / 1024) (t % 1024) 0 0 4 zero) s1 hq).trans
    ((round_low ops input (t / 1024) (t % 1024) 0 t q zero s0 hq).trans
      (h0.trans (preloads_low input t q s hq)))

theorem prefix_native_indices (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    NativeIndices t (prefixState ops input t s) := by
  obtain ⟨_,h0,h1,h2,h3,_⟩ := initialized_fields t s
  exact ⟨(prefix_low_indices ops input t 0 s (by decide)).trans h0,
    (prefix_low_indices ops input t 1 s (by decide)).trans h1,
    (prefix_low_indices ops input t 2 s (by decide)).trans h2,
    (prefix_low_indices ops input t 3 s (by decide)).trans h3⟩

theorem prefix_native_other (ops : Ops α) (input : Nat → Nat → α)
    (t u : Nat) (s : State α) (hu : u ≠ t) (indices : NativeIndices u s) :
    NativeIndices u (prefixState ops input t s) := by
  simpa only [NativeIndices,(prefix_frame ops input t s).indices u hu] using indices

#print axioms prefix_low_indices
#print axioms prefix_native_indices
#print axioms prefix_native_other
end LarkNativeSglangRmsNorm
