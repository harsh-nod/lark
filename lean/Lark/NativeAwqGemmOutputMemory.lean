import Lark.NativeAwqGemmGrid

/-! Exact final output values and memory frames across all actual lane
tails. Distinct source output writers prevent later lanes overwriting them. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] outputStored outputRound outputLoop outputLane tailLane tailFold

theorem tail_lane_other_memory (p : Shape) (ops : Ops α) (tile t : Nat) (values : Nat → α)
    (s : State α) (loc : Location) (outside : ∀ q, q<4*banks p → loc≠outCell p t q) :
    (tailLane p ops tile t values s).memory loc=s.memory loc := by
  unfold tailLane
  split
  · rfl
  · unfold outputLane
    exact output_loop_other_memory p ops t 0 (4*banks p) values _ loc
      (fun q _ hq => outside q (by omega))

theorem tail_lane_value (p : Shape) (ops : Ops α) (tile t q : Nat) (values : Nat → α)
    (s : State α) (last : ¬tile+1<p.k/32) (hq : q<4*banks p) (guard : globalOutputRow p t (q%4)<p.m) :
    (tailLane p ops tile t values s).memory (outCell p t q)=some (ops.toHalf (values q)) := by
  rw [tailLane,if_neg last]
  unfold outputLane
  exact output_loop_value p ops t 0 (4*banks p) q values _ (by omega) (by omega) (by omega) guard

theorem tail_fold_other_memory (p : Shape) (ops : Ops α) (tile : Nat) (values : Nat → Nat → α)
    (ts : List Nat) (s : State α) (loc : Location)
    (outside : ∀ t∈ts, ∀ q, q<4*banks p → loc≠outCell p t q) :
    (tailFold p ops tile values ts s).memory loc=s.memory loc := by
  induction ts generalizing s with
  | nil => simp only [tailFold,List.foldl_nil]
  | cons t ts ih =>
    simpa only [tailFold,List.foldl_cons] using (ih (tailLane p ops tile t (values t) s)
      (fun u hu => outside u (List.mem_cons_of_mem t hu))).trans
      (tail_lane_other_memory p ops tile t (values t) s loc (outside t (by simp)))

theorem tail_fold_value (p : Shape) (ops : Ops α) (tile t q : Nat) (values : Nat → Nat → α)
    (ts : List Nat) (s : State α) (last : ¬tile+1<p.k/32) (hd : ts.Nodup) (ht : t∈ts)
    (hq : q<4*banks p) (guard : globalOutputRow p t (q%4)<p.m) :
    (tailFold p ops tile values ts s).memory (outCell p t q)=some (ops.toHalf (values t q)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    rcases List.mem_cons.mp ht with same | member
    · subst t
      have frame := tail_fold_other_memory p ops tile values ts (tailLane p ops tile u (values u) s) (outCell p u q)
        (fun v hv j hj => out_cell_different_threads p u v q j hq hj
          (by intro same; subst v; exact disjoint hv))
      simpa only [tailFold,List.foldl_cons] using frame.trans (tail_lane_value p ops tile u q (values u) s last hq guard)
    · simpa only [tailFold,List.foldl_cons] using ih (tailLane p ops tile u (values u) s) tail member

theorem tail_fold_more_memory (p : Shape) (ops : Ops α) (tile : Nat) (values : Nat → Nat → α)
    (ts : List Nat) (s : State α) (more : tile+1<p.k/32) :
    (tailFold p ops tile values ts s).memory=s.memory ∧ (tailFold p ops tile values ts s).trace=s.trace := by
  induction ts generalizing s with
  | nil => simp only [tailFold,List.foldl_nil,and_self]
  | cons t ts ih =>
    have one : (tailLane p ops tile t (values t) s).memory=s.memory ∧
        (tailLane p ops tile t (values t) s).trace=s.trace := by
      rw [tailLane,if_pos more]
      exact ⟨rfl,rfl⟩
    have rest := ih (tailLane p ops tile t (values t) s)
    simpa only [tailFold,List.foldl_cons] using And.intro (rest.1.trans one.1) (rest.2.trans one.2)

theorem block_tail_value (p : Shape) (ops : Ops α) (tile b t q : Nat) (values : Nat → Nat → α)
    (s : State α) (last : ¬tile+1<p.k/32) (ht : t∈blockThreads (geometry p) b)
    (hq : q<4*banks p) (guard : globalOutputRow p t (q%4)<p.m) :
    (blockTail p ops tile b values s).memory (outCell p t q)=some (ops.toHalf (values t q)) :=
  tail_fold_value p ops tile t q values _ s last (block_threads_nodup p b) ht hq guard

#print axioms tail_lane_other_memory
#print axioms tail_lane_value
#print axioms tail_fold_other_memory
#print axioms tail_fold_value
#print axioms tail_fold_more_memory
#print axioms block_tail_value
end LarkNativeAwqGemm
