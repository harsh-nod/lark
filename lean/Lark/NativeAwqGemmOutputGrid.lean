import Lark.NativeAwqGemmOutputCoverage

/-! Every cell in the final dense output buffer contains its complete
source-order accumulator value after every original block has executed. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] wholeBlock gridFold wholeGrid

theorem grid_fold_other_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (t q : Nat) (s : State α) (hq : q<4*banks p)
    (outside : ∀ b∈bs, t∉blockThreads (geometry p) b) :
    (gridFold p ops input bs s).memory (outCell p t q)=s.memory (outCell p t q) := by
  induction bs generalizing s with
  | nil => simp only [gridFold,List.foldl_nil]
  | cons b bs ih =>
    simpa only [gridFold,List.foldl_cons] using
      (ih (wholeBlock p ops input b s) (fun c hc => outside c (List.mem_cons_of_mem b hc))).trans
        (whole_block_other_output p ops input b t q s (outside b (by simp)) hq)

theorem grid_fold_output_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (b t q : Nat) (s : State α) (hd : bs.Nodup) (hb : b∈bs)
    (ht : t∈blockThreads (geometry p) b) (hq : q<4*banks p) (guard : globalOutputRow p t (q%4)<p.m) :
    (gridFold p ops input bs s).memory (outCell p t q)=
      some (ops.toHalf (kAccum p ops input b (p.k/32) (q/4) t (q%4))) := by
  induction bs generalizing s with
  | nil => simp at hb
  | cons c bs ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    rcases List.mem_cons.mp hb with same | member
    · subst b
      have frame := grid_fold_other_output p ops input bs t q (wholeBlock p ops input c s) hq
        (fun d hd => different_block_threads p c d t (by intro same; subst d; exact disjoint hd) ht)
      simpa only [gridFold,List.foldl_cons] using frame.trans (whole_block_output_value p ops input c t q s ht hq guard)
    · simpa only [gridFold,List.foldl_cons] using ih (wholeBlock p ops input c s) tail member

def sourceOutput (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (offset : Nat) : α :=
  ops.toHalf (kAccum p ops input (blockId (writer p offset)) (p.k/32)
    (outputSlot p offset/4) (writer p offset) (outputSlot p offset%4))

def sourceSpec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (p.m*p.n)).map (sourceOutput p ops input)

theorem whole_grid_output_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (s : State α) (offset : Nat) (hi : offset<p.m*p.n) :
    (wholeGrid p ops input s).memory (globalCell 2 offset)=some (sourceOutput p ops input offset) := by
  have value := grid_fold_output_value p ops input (List.range (geometry p).grid)
    (blockId (writer p offset)) (writer p offset) (outputSlot p offset) s List.nodup_range
    (List.mem_range.mpr (writer_block_bound p offset hi)) (thread_in_own_block p (writer p offset))
    (output_slot_bound p offset) (writer_output_guard p offset hi)
  have cell : outCell p (writer p offset) (outputSlot p offset)=globalCell 2 offset := by
    unfold outCell
    rw [writer_output_offset]
  rw [cell] at value
  simpa only [wholeGrid,sourceOutput] using value

theorem output_mapM_some (xs : List Nat) (f : Nat → Option α) (v : Nat → α)
    (values : ∀ i∈xs, f i=some (v i)) : xs.mapM f=some (xs.map v) := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.mapM_cons,values i (by simp),Option.some_bind,
      ih (fun j hj => values j (List.mem_cons_of_mem i hj)),List.map_cons]
    rfl

theorem output_mapM_map (xs : List Nat) (f : Nat → Nat × Nat) (g : Nat × Nat → Option α) :
    (xs.map f).mapM g=xs.mapM (fun i => g (f i)) := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp only [List.map_cons,List.mapM_cons,ih]

theorem extract_source_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (values : ∀ offset, offset<p.m*p.n → s.memory (globalCell 2 offset)=some (sourceOutput p ops input offset)) :
    extract (layout p) s=some (sourceSpec p ops input) := by
  simp only [extract,layout,List.zipIdx_cons,List.zipIdx_nil,List.flatMap_cons,List.flatMap_nil]
  simp only [List.map_cons,List.map_nil,show Role.input≠Role.output by decide,
    ↓reduceIte,List.nil_append,List.append_nil]
  change (((List.range (p.m*p.n)).map (fun i => (2,i))).mapM
    (fun bi => s.memory ⟨.global,0,bi.1,bi.2⟩) : Option (List α))=_
  rw [output_mapM_map]
  exact output_mapM_some (List.range (p.m*p.n)) (fun i => s.memory (globalCell 2 i))
    (sourceOutput p ops input) (fun i hi => values i (List.mem_range.mp hi))

theorem whole_grid_extract (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) :
    extract (layout p) (wholeGrid p ops input s)=some (sourceSpec p ops input) :=
  extract_source_values p ops input _ (whole_grid_output_value p ops input s)

theorem whole_launch_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    LarkMFMA.runLaunch ops (layout p) (geometry p) (fuel p) (program p) (initial (layout p) input outside)=
      some (wholeGrid p ops input (initial (layout p) input outside)) := by
  rw [LarkMFMA.runLaunch_of ops (layout p) (geometry p) (fuel p) (program p) _
    (by have h := Nat.mul_pos (row_tiles_positive p) (column_tiles_positive p); change rowTiles p*columnTiles p≠0; omega)
    (by change (64 : Nat)≠0; decide) rfl (by change (64%64 : Nat)=0; decide)]
  exact initialized_whole_grid_run p ops input outside

#print axioms grid_fold_other_output
#print axioms grid_fold_output_value
#print axioms whole_grid_output_value
#print axioms output_mapM_some
#print axioms output_mapM_map
#print axioms extract_source_values
#print axioms whole_grid_extract
#print axioms whole_launch_run
end LarkNativeAwqGemm
