import Lark.NativeAttentionNextLoad

/-! Native lane folds for the subsequent K/V copy phases. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

structure CopyLaneReady (p : Shape) (t key : Nat) (s : State α) : Prop where
  bound : t < p.groups * 32
  native : NativeIndices t s
  keyIndex : s.indices t 5 = some (key : Int)
  pc : s.pc t = 88

def nextFold (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => nextLoad ops input t key s) s

theorem next_fold_epochs (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (ts : List Nat) (s : State α) :
    (nextFold ops input key ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih => exact (ih (nextLoad ops input t key s)).trans (next_load_fields ops input t key s).2.2

theorem next_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (ts : List Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (nextFold ops input key ts s) := by
  induction ts generalizing s with
  | nil => exact hr
  | cons t ts ih => exact ih _ (next_load_reads p ops input t key s hr)

theorem next_fold_other (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (ts : List Nat)
    (u : Nat) (s : State α) (hu : u ∉ ts) :
    (nextFold ops input key ts s).pc u = s.pc u ∧ (nextFold ops input key ts s).indices u = s.indices u ∧
    (nextFold ops input key ts s).regs u = s.regs u := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons t ts ih =>
      have hf := ih (nextLoad ops input t key s) (by intro hm; exact hu (by simp [hm]))
      have he := next_load_other ops input t key u s (by intro he; exact hu (by simp [he]))
      exact ⟨hf.1.trans he.1, hf.2.1.trans he.2.1, hf.2.2.trans he.2.2⟩

theorem next_fold_member (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (ts : List Nat)
    (t : Nat) (s : State α) (hn : ts.Nodup) (ht : t ∈ ts)
    (native : ∀ u ∈ ts, NativeIndices u s) :
    (nextFold ops input key ts s).pc t = 20 ∧ NativeIndices t (nextFold ops input key ts s) ∧
    (nextFold ops input key ts s).indices t 5 = some ((key + 1 : Nat) : Int) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have hf := next_fold_other ops input key ts u (nextLoad ops input u key s) (List.nodup_cons.mp hn).1
        have hl := next_load_fields ops input u key s
        refine ⟨hf.1.trans hl.1, ?_, (congrArg (fun indices => indices 5) hf.2.1).trans hl.2.1⟩
        change NativeIndices u (nextFold ops input key ts (nextLoad ops input u key s))
        simpa only [NativeIndices, hf.2.1] using next_load_native ops input u key s (native u (by simp))
      · apply ih (nextLoad ops input u key s) (List.nodup_cons.mp hn).2 hm
        intro v hv
        have he := (next_load_other ops input u key v s
          (by intro he; subst v; exact (List.nodup_cons.mp hn).1 hv)).2.1
        simpa only [NativeIndices, he] using native v (by simp [hv])

theorem next_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (ts : List Nat)
    (s : State α) (hk : key + 1 < 4) (hn : ts.Nodup) (hr : Reads p input s)
    (ready : ∀ t ∈ ts, CopyLaneReady p t key s) :
    ts.foldlM (fun s t => runLane ops (layout p) (geometry p) program t fuel.lane s) s = some (nextFold ops input key ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      have ht := ready t (by simp)
      rw [List.foldlM_cons, next_load_run p ops input t key s ht.bound hk hr ht.native ht.keyIndex ht.pc]
      simp only [bind, Option.some_bind]
      apply ih _ (List.nodup_cons.mp hn).2 (next_load_reads p ops input t key s hr)
      intro u hu
      have hf := next_load_other ops input t key u s (by intro he; subst u; exact (List.nodup_cons.mp hn).1 hu)
      have hr := ready u (by simp [hu])
      refine ⟨hr.bound, ?_, (congrArg (fun indices => indices 5) hf.2.1).trans hr.keyIndex, hf.1.trans hr.pc⟩
      simpa only [NativeIndices, hf.2.1] using hr.native

theorem next_fold_memory_other (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (ts : List Nat)
    (s : State α) (l : Location)
    (hl : ∀ t ∈ ts, ∀ c, c < 256 → l ≠ sharedCell t 1 (sharedAddress t c) ∧ l ≠ sharedCell t 2 (sharedAddress t c)) :
    (nextFold ops input key ts s).memory l = s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (nextLoad ops input t key s) (by intro u hu; exact hl u (by simp [hu]))).trans
        (next_load_memory_other ops input t key s l (hl t (by simp)))

theorem next_fold_tile_other (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (ts : List Nat)
    (u buffer col : Nat) (s : State α) (hu : u ∉ ts) (hc : col < 256) :
    (nextFold ops input key ts s).memory (sharedCell u buffer (sharedAddress u col)) =
      s.memory (sharedCell u buffer (sharedAddress u col)) := by
  apply next_fold_memory_other
  intro t ht c hb
  have hne : u ≠ t := by intro he; exact hu (he ▸ ht)
  exact ⟨shared_thread_ne t u buffer 1 col c hne hc hb, shared_thread_ne t u buffer 2 col c hne hc hb⟩

theorem next_fold_tile (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (ts : List Nat)
    (t buffer col : Nat) (s : State α) (hn : ts.Nodup) (ht : t ∈ ts) (hb : buffer = 1 ∨ buffer = 2) (hc : col < 256) :
    (nextFold ops input key ts s).memory (sharedCell t buffer (sharedAddress t col)) =
      some (ops.fromHalf (input (buffer + 1) (globalAddress t (key + 1) col))) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (next_fold_tile_other ops input key ts u buffer col (nextLoad ops input u key s) (List.nodup_cons.mp hn).1 hc).trans
          (next_load_value ops input u key buffer col s hb hc)
      · exact ih (nextLoad ops input u key s) (List.nodup_cons.mp hn).2 hm

theorem next_fold_good (ops : Ops α) (input : Nat → Nat → α) (key : Nat) (ts : List Nat)
    (s : State α) (he : ∀ t ∈ ts, (s.epochs t).block % 2 = 0) (hg : TraceGood s) : TraceGood (nextFold ops input key ts s) := by
  induction ts generalizing s with
  | nil => exact hg
  | cons t ts ih =>
      exact ih _ (by intro u hu; rw [(next_load_fields ops input t key s).2.2]; exact he u (by simp [hu]))
        (next_load_good ops input t key s (he t (by simp)) hg)

#print axioms next_fold_run
#print axioms next_fold_member
#print axioms next_fold_tile
#print axioms next_fold_memory_other
#print axioms next_fold_good
end LarkNativeAttention
