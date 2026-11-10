import Lark.NativeAttentionFirstFrame

/-! Actual lane folds for the first native block phase. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def firstFold (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => firstLane ops input t s) s

theorem first_fold_epochs (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (firstFold ops input ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih => exact (ih (firstLane ops input t s)).trans (first_lane_fields ops input t s).2

theorem first_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hr : Reads p input s) : Reads p input (firstFold ops input ts s) := by
  induction ts generalizing s with
  | nil => exact hr
  | cons t ts ih => exact ih _ (first_lane_reads p ops input t s hr)

theorem first_fold_other (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (u : Nat) (s : State α) (hu : u ∉ ts) :
    (firstFold ops input ts s).pc u = s.pc u ∧ (firstFold ops input ts s).indices u = s.indices u ∧
    (firstFold ops input ts s).regs u = s.regs u := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons t ts ih =>
      have h := ih (firstLane ops input t s) (by intro hm; exact hu (by simp [hm]))
      have h1 := first_lane_other ops input t u s (by intro he; exact hu (by simp [he]))
      exact ⟨h.1.trans h1.1, h.2.1.trans h1.2.1, h.2.2.trans h1.2.2⟩

theorem first_fold_member (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (t : Nat) (s : State α) (hn : ts.Nodup) (ht : t ∈ ts) :
    (firstFold ops input ts s).pc t = 20 ∧ NativeIndices t (firstFold ops input ts s) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have hf := first_fold_other ops input ts u (firstLane ops input u s) hnot
        refine ⟨hf.1.trans (first_lane_fields ops input u s).1, ?_⟩
        change NativeIndices u (firstFold ops input ts (firstLane ops input u s))
        simpa only [NativeIndices, hf.2.1] using (first_lane_native ops input u s)
      · exact ih (firstLane ops input u s) hnodup hm

theorem first_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (ht : ∀ t ∈ ts, t < p.groups * 32)
    (hr : Reads p input s) (hp : ∀ t ∈ ts, s.pc t = 0) :
    ts.foldlM (fun s t => runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (firstFold ops input ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      have hpc : ∀ u ∈ ts, (firstLane ops input t s).pc u = 0 := by
        intro u hu
        have hne : u ≠ t := by intro he; subst u; exact hnot hu
        exact (first_lane_other ops input t u s hne).1.trans (hp u (by simp [hu]))
      rw [List.foldlM_cons, first_lane_run p ops input t s (ht t (by simp)) hr (hp t (by simp))]
      simp only [bind, Option.some_bind]
      exact ih _ hnodup (by intro u hu; exact ht u (by simp [hu]))
        (first_lane_reads p ops input t s hr) hpc

theorem first_fold_good (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α)
    (he : ∀ t ∈ ts, (s.epochs t).block % 2 = 0) (hg : TraceGood s) : TraceGood (firstFold ops input ts s) := by
  induction ts generalizing s with
  | nil => exact hg
  | cons t ts ih =>
      apply ih (firstLane ops input t s)
      · intro u hu
        rw [(first_lane_fields ops input t s).2]
        exact he u (by simp [hu])
      · exact first_lane_good ops input t s (he t (by simp)) hg

theorem first_fold_output_other (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (offset : Nat) (s : State α) (ho : writer offset ∉ ts) :
    (firstFold ops input ts s).memory (globalCell 0 offset) = s.memory (globalCell 0 offset) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      have h := ih (firstLane ops input t s) (by intro hm; exact ho (by simp [hm]))
      exact h.trans (first_lane_output_other ops input t offset s (by intro he; exact ho (by simp [he])))

theorem first_fold_output (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (t tile col : Nat) (s : State α) (hn : ts.Nodup) (ht : t ∈ ts)
    (hi : tile < 4) (hc : col < 256) :
    (firstFold ops input ts s).memory (globalCell 0 (globalAddress t tile col)) = some (zeroValue ops) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have hf := first_fold_output_other ops input ts (globalAddress u tile col) (firstLane ops input u s)
          (by simpa only [global_address_owner u tile col hi hc] using hnot)
        exact hf.trans (first_lane_output ops input u tile col s hi hc)
      · exact ih (firstLane ops input u s) hnodup hm

theorem first_fold_tile_other (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (u b col : Nat) (s : State α) (hu : u ∉ ts) (hc : col < 256) :
    (firstFold ops input ts s).memory (sharedCell u b (sharedAddress u col)) =
      s.memory (sharedCell u b (sharedAddress u col)) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      have h := ih (firstLane ops input t s) (by intro hm; exact hu (by simp [hm]))
      exact h.trans (first_lane_tile_other ops input t u b col s (by intro he; exact hu (by simp [he])) hc)

theorem first_fold_tile (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (t b col : Nat) (s : State α) (hn : ts.Nodup) (ht : t ∈ ts)
    (hb : b = 1 ∨ b = 2) (hc : col < 256) :
    (firstFold ops input ts s).memory (sharedCell t b (sharedAddress t col)) =
      some (ops.fromHalf (input (b + 1) (globalAddress t 0 col))) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot, hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (first_fold_tile_other ops input ts u b col (firstLane ops input u s) hnot hc).trans
          (first_lane_tile ops input u b col s hb hc)
      · exact ih (firstLane ops input u s) hnodup hm

#print axioms first_fold_run
#print axioms first_fold_member
#print axioms first_fold_output
#print axioms first_fold_tile
#print axioms first_fold_good
end LarkNativeAttention
