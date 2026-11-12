import Lark.NativeFlashInferRmsNormOutputStored

/-! The actual source-ordered output lane fold, with retained operands,
controls, epochs, actual access classification and unique native writers.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def outputFold (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => outputLane ops input row (t % 1024) t (blockSum ops input row) s) s

theorem native_thread_eq (row t : Nat) (hr : t / 1024 = row) : t = row * 1024 + t % 1024 := by omega

theorem output_fold_epochs (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (ts : List Nat) (s : State α) :
    (outputFold ops input row ts s).epochs = s.epochs := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (outputLane ops input row (t % 1024) t (blockSum ops input row) s)).trans
        (output_lane_epochs ops input row (t % 1024) t (blockSum ops input row) s)

theorem output_fold_reads (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (reads : OutputReads ops input row s) :
    OutputReads ops input row (outputFold ops input row ts s) := by
  induction ts generalizing s with
  | nil => exact reads
  | cons t ts ih => exact ih _ (output_lane_reads ops input row (t % 1024) t (blockSum ops input row) s reads)

theorem output_fold_indices (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (u : Nat) (s : State α) (hi : NativeIndices u s) :
    NativeIndices u (outputFold ops input row ts s) := by
  induction ts generalizing s with
  | nil => exact hi
  | cons t ts ih => exact ih _ (output_lane_native_indices ops input row (t % 1024) t u (blockSum ops input row) s hi)

theorem output_fold_other (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (u : Nat) (s : State α) (hu : u ∉ ts) :
    (outputFold ops input row ts s).pc u = s.pc u ∧
    (outputFold ops input row ts s).indices u = s.indices u ∧
    (outputFold ops input row ts s).regs u = s.regs u := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons t ts ih =>
      have hn : u ∉ ts := by intro h; exact hu (by simp [h])
      have he : u ≠ t := by intro h; subst u; simp at hu
      have h := ih (outputLane ops input row (t % 1024) t (blockSum ops input row) s) hn
      have h1 := output_lane_other ops input row (t % 1024) t u (blockSum ops input row) s he
      exact ⟨h.1.trans h1.1,h.2.1.trans h1.2.1,h.2.2.trans h1.2.2⟩

theorem output_fold_memory_frame (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (l : Location)
    (hl : ∀ t ∈ ts, ¬ OutputWrites row (t % 1024) l) :
    (outputFold ops input row ts s).memory l = s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      exact (ih (outputLane ops input row (t % 1024) t (blockSum ops input row) s)
        (by intro u hu; exact hl u (by simp [hu]))).trans
        (output_lane_frame ops input row (t % 1024) t (blockSum ops input row) s l (hl t (by simp)))

theorem output_fold_shared (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (owner buffer offset : Nat) :
    (outputFold ops input row ts s).memory ⟨.shared,owner,buffer,offset⟩ = s.memory ⟨.shared,owner,buffer,offset⟩ :=
  output_fold_memory_frame ops input row ts s _ (by intro t ht; rintro ⟨j,hj,he⟩; cases he)

theorem output_fold_pc (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t ∈ ts) :
    (outputFold ops input row ts s).pc t = 67 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot,hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (output_fold_other ops input row ts u (outputLane ops input row (u % 1024) u (blockSum ops input row) s) hnot).1.trans
          (output_lane_pc ops input row (u % 1024) u (blockSum ops input row) s)
      · exact ih _ hnodup hm

structure OutputFoldEntry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) : Prop where
  valid : row < p.rows
  reads : OutputReads ops input row s
  indices : ∀ t ∈ ts, NativeIndices t s
  total : s.memory (partialSlot row 0) = some (blockSum ops input row)
  pc : ∀ t ∈ ts, s.pc t = 47
  epoch : ∀ t ∈ ts, (s.epochs t).block = 2
  good : ∀ a ∈ s.trace, Good a

theorem output_fold_entry_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (ts : List Nat) (s : State α) (hr : t / 1024 = row) (hn : t ∉ ts)
    (entry : OutputFoldEntry p ops input row (t :: ts) s) :
    OutputFoldEntry p ops input row ts (outputLane ops input row (t % 1024) t (blockSum ops input row) s) := by
  exact {
    valid := entry.valid
    reads := output_lane_reads ops input row (t % 1024) t (blockSum ops input row) s entry.reads
    indices := by
      intro u hu
      exact output_lane_native_indices ops input row (t % 1024) t u (blockSum ops input row) s (entry.indices u (by simp [hu]))
    total := (output_lane_shared ops input row (t % 1024) t row 0 0 (blockSum ops input row) s).trans entry.total
    pc := by
      intro u hu
      exact (output_lane_other ops input row (t % 1024) t u (blockSum ops input row) s
        (by intro he; subst u; exact hn hu)).1.trans (entry.pc u (by simp [hu]))
    epoch := by
      intro u hu
      exact (congrArg (fun epochs => (epochs u).block) (output_lane_epochs ops input row (t % 1024) t (blockSum ops input row) s)).trans
        (entry.epoch u (by simp [hu]))
    good := output_lane_good p ops input row (t % 1024) t (blockSum ops input row) s (Nat.mod_lt _ (by decide))
      (native_thread_eq row t hr) (entry.epoch t (by simp)) entry.good }

theorem output_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (ho : ∀ t ∈ ts, t / 1024 = row) (entry : OutputFoldEntry p ops input row ts s) :
    ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s) s =
      some (outputFold ops input row ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot,hnodup⟩
      have hit := entry.indices t (by simp)
      have hrow := ho t (by simp)
      have hi0 : s.indices t 0 = some (row : Int) := by simpa only [hrow] using hit.1
      rewrite [List.foldlM_cons, output_lane_run p ops input row (t % 1024) t (blockSum ops input row) s
        entry.valid (Nat.mod_lt _ (by decide)) (native_thread_eq row t hrow) (entry.pc t (by simp)) hi0 hit.2.1
        entry.total entry.reads (entry.epoch t (by simp)) entry.good]
      simp only [bind, Option.some_bind]
      exact ih _ hnodup (by intro u hu; exact ho u (by simp [hu]))
        (output_fold_entry_tail p ops input row t ts s hrow hnot entry)

theorem output_fold_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (ho : ∀ t ∈ ts, t / 1024 = row) (entry : OutputFoldEntry p ops input row ts s) :
    ∀ a ∈ (outputFold ops input row ts s).trace, Good a := by
  induction ts generalizing s with
  | nil => exact entry.good
  | cons t ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot,hnodup⟩
      exact ih _ hnodup (by intro u hu; exact ho u (by simp [hu]))
        (output_fold_entry_tail p ops input row t ts s (ho t (by simp)) hnot entry)

theorem output_fold_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (ho : ∀ t ∈ ts, t / 1024 = row)
    (t : Nat) (ht : t ∈ ts) (l : Location) (value : α) (hl : OutputWrites row (t % 1024) l)
    (hv : ∀ u : State α, (outputLane ops input row (t % 1024) t (blockSum ops input row) u).memory l = some value) :
    (outputFold ops input row ts s).memory l = some value := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot,hnodup⟩
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        apply (output_fold_memory_frame ops input row ts (outputLane ops input row (u % 1024) u (blockSum ops input row) s) l ?_).trans (hv s)
        intro t ht hwrite
        have h1 := (output_writes_writer p row (u % 1024) u l (Nat.mod_lt _ (by decide))
          (native_thread_eq row u (ho u (by simp))) hl).2.2
        have h2 := (output_writes_writer p row (t % 1024) t l (Nat.mod_lt _ (by decide))
          (native_thread_eq row t (ho t (by simp [ht]))) hwrite).2.2
        have heq : u = t := h1.symm.trans h2
        exact hnot (heq.symm ▸ ht)
      · exact ih _ hnodup (by intro t ht; exact ho t (by simp [ht])) hm

theorem output_fold_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) :
    (outputFold ops input row ts s).trace.length = s.trace.length + 49 * ts.length := by
  induction ts generalizing s with
  | nil => simp [outputFold]
  | cons t ts ih =>
      change (outputFold ops input row ts (outputLane ops input row (t % 1024) t (blockSum ops input row) s)).trace.length = _
      rewrite [ih, output_lane_trace_length]
      simp only [List.length_cons]
      omega

#print axioms native_thread_eq
#print axioms output_fold_epochs
#print axioms output_fold_reads
#print axioms output_fold_indices
#print axioms output_fold_other
#print axioms output_fold_memory_frame
#print axioms output_fold_shared
#print axioms output_fold_pc
#print axioms output_fold_entry_tail
#print axioms output_fold_run
#print axioms output_fold_good
#print axioms output_fold_value
#print axioms output_fold_trace_length
end LarkNativeFlashInferRmsNorm
