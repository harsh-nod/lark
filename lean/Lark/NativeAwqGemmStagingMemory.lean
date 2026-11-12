import Lark.NativeAwqGemmStagingBlock

/-! Unique shared writers preserve every earlier lane's staged values while
the actual scheduler visits later lanes. Outside memory remains unchanged. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] aLoopState aRoundState aBodyState bChunksState bChunkState bChunkBody bLoopState bRoundState bBodyState stagingState

theorem a_writer_cells_distinct (t u e q : Nat) (different : t≠u) (he : e<8) (hq : q<8) : aCell t e≠aCell u q := by
  intro same
  have writers := congrArg aWriter same
  rw [a_cell_writer t e he,a_cell_writer u q hq] at writers
  exact different writers

theorem b_writer_cells_distinct (p : Shape) (t u chunk otherChunk e q : Nat)
    (different : t≠u) (he : e<8) (hq : q<8) : bCell p t chunk e≠bCell p u otherChunk q := by
  intro same
  have keys := congrArg (bKey p) same
  rw [b_cell_key p t chunk e he,b_cell_key p u otherChunk q hq] at keys
  exact different (congrArg Prod.fst keys)

theorem ab_cells_distinct (p : Shape) (t u e chunk q : Nat) : aCell t e≠bCell p u chunk q := by
  intro same
  have impossible := congrArg Location.buffer same
  cases impossible

theorem staging_other_a_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t u e : Nat) (s : State α) (different : u≠t) (he : e<8) :
    (stagingState p ops input tile t s).memory (aCell u e)=s.memory (aCell u e) :=
  staging_memory_outside p ops input tile t s (aCell u e)
    (fun q hq => a_writer_cells_distinct u t e q different he hq)
    (fun chunk hc q hq => ab_cells_distinct p u t e chunk q)

theorem staging_other_b_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t u chunk e : Nat) (s : State α) (different : u≠t) (he : e<8) :
    (stagingState p ops input tile t s).memory (bCell p u chunk e)=s.memory (bCell p u chunk e) :=
  staging_memory_outside p ops input tile t s (bCell p u chunk e)
    (fun q hq => Ne.symm (ab_cells_distinct p t u q chunk e))
    (fun c hc q hq => b_writer_cells_distinct p u t chunk c e q different he hq)

theorem staging_fold_other_a_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile u e : Nat) (ts : List Nat) (s : State α) (hu : u∉ts) (he : e<8) :
    (stagingFold p ops input tile ts s).memory (aCell u e)=s.memory (aCell u e) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    have different : u≠t := by intro same; exact hu (List.mem_cons.mpr (Or.inl same))
    have tail : u∉ts := by intro member; exact hu (List.mem_cons_of_mem t member)
    exact (ih (stagingState p ops input tile t s) tail).trans (staging_other_a_memory p ops input tile t u e s different he)

theorem staging_fold_other_b_memory (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile u chunk e : Nat) (ts : List Nat) (s : State α) (hu : u∉ts) (he : e<8) :
    (stagingFold p ops input tile ts s).memory (bCell p u chunk e)=s.memory (bCell p u chunk e) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    have different : u≠t := by intro same; exact hu (List.mem_cons.mpr (Or.inl same))
    have tail : u∉ts := by intro member; exact hu (List.mem_cons_of_mem t member)
    exact (ih (stagingState p ops input tile t s) tail).trans (staging_other_b_memory p ops input tile t u chunk e s different he)

theorem staging_fold_a_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile u e : Nat) (ts : List Nat) (s : State α) (hd : ts.Nodup) (hu : u∈ts) (he : e<8) :
    (stagingFold p ops input tile ts s).memory (aCell u e)=
      some (if inputRow p u<p.m then input 0 (aSourceOffset p tile u e) else ops.toHalf (ops.literal 0 1)) := by
  induction ts generalizing s with
  | nil => simp at hu
  | cons t ts ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    rcases List.mem_cons.mp hu with same | member
    · subst u
      exact (staging_fold_other_a_memory p ops input tile t e ts (stagingState p ops input tile t s) disjoint he).trans
        (staging_a_value p ops input tile t e s he)
    · exact ih (stagingState p ops input tile t s) tail member

theorem staging_fold_b_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile u chunk e : Nat) (ts : List Nat) (s : State α) (hd : ts.Nodup) (hu : u∈ts)
    (hc : chunk<banks p) (he : e<8) :
    (stagingFold p ops input tile ts s).memory (bCell p u chunk e)=some (input 1 (bSourceOffset p tile u chunk e)) := by
  induction ts generalizing s with
  | nil => simp at hu
  | cons t ts ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    rcases List.mem_cons.mp hu with same | member
    · subst u
      exact (staging_fold_other_b_memory p ops input tile t chunk e ts (stagingState p ops input tile t s) disjoint he).trans
        (staging_b_value p ops input tile t chunk e s hc he)
    · exact ih (stagingState p ops input tile t s) tail member

theorem staging_fold_memory_outside (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile : Nat) (ts : List Nat) (s : State α) (loc : Location)
    (ha : ∀ t∈ts, ∀ e, e<8 → loc≠aCell t e)
    (hb : ∀ t∈ts, ∀ chunk, chunk<banks p → ∀ e, e<8 → loc≠bCell p t chunk e) :
    (stagingFold p ops input tile ts s).memory loc=s.memory loc := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    have rest := ih (stagingState p ops input tile t s)
      (by intro u hu; exact ha u (List.mem_cons_of_mem t hu))
      (by intro u hu; exact hb u (List.mem_cons_of_mem t hu))
    exact rest.trans (staging_memory_outside p ops input tile t s loc (ha t (by simp)) (hb t (by simp)))

theorem after_middle_a_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t e : Nat) (s : State α) (ht : t∈blockThreads (geometry p) b) (he : e<8) :
    (afterMiddleBarrier p ops input tile b s).memory (aCell t e)=
      some (if inputRow p t<p.m then input 0 (aSourceOffset p tile t e) else ops.toHalf (ops.literal 0 1)) :=
  staging_fold_a_value p ops input tile t e (blockThreads (geometry p) b) s (block_threads_nodup p b) ht he

theorem after_middle_b_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t chunk e : Nat) (s : State α) (ht : t∈blockThreads (geometry p) b) (hc : chunk<banks p) (he : e<8) :
    (afterMiddleBarrier p ops input tile b s).memory (bCell p t chunk e)=some (input 1 (bSourceOffset p tile t chunk e)) :=
  staging_fold_b_value p ops input tile t chunk e (blockThreads (geometry p) b) s (block_threads_nodup p b) ht hc he

theorem after_middle_memory_outside (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (s : State α) (loc : Location)
    (ha : ∀ t∈blockThreads (geometry p) b, ∀ e, e<8 → loc≠aCell t e)
    (hb : ∀ t∈blockThreads (geometry p) b, ∀ chunk, chunk<banks p → ∀ e, e<8 → loc≠bCell p t chunk e) :
    (afterMiddleBarrier p ops input tile b s).memory loc=s.memory loc :=
  staging_fold_memory_outside p ops input tile (blockThreads (geometry p) b) s loc ha hb

#print axioms a_writer_cells_distinct
#print axioms b_writer_cells_distinct
#print axioms ab_cells_distinct
#print axioms staging_other_a_memory
#print axioms staging_other_b_memory
#print axioms staging_fold_other_a_memory
#print axioms staging_fold_other_b_memory
#print axioms staging_fold_a_value
#print axioms staging_fold_b_value
#print axioms staging_fold_memory_outside
#print axioms after_middle_a_value
#print axioms after_middle_b_value
#print axioms after_middle_memory_outside
end LarkNativeAwqGemm
