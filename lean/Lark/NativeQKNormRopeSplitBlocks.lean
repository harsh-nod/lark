import Lark.NativeQKNormRopeSplitBlock

/-! Actual grid block fold, retaining the shared memory state and every
previous block's output. No per-block memory initialization is introduced. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def splitBlocks (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (s : State α) : State α :=
  bs.foldl (fun s block => splitBlockState p ops input block s) s

theorem split_native_block_bound (p : Shape) (block t : Nat) (hb : block < p.rows * 5)
    (ht : t ∈ blockThreads (geometry p) block) : t < p.rows * 1280 := by
  have ho := (native_block_mem p block t).mp ht
  unfold physicalBlock at ho
  omega

theorem split_blocks_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (s : State α) (hr : Reads p input s) : Reads p input (splitBlocks p ops input bs s) := by
  induction bs generalizing s with
  | nil => exact hr
  | cons b bs ih => exact ih (splitBlockState p ops input b s) (split_block_reads p ops input b s hr)


theorem split_blocks_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (t : Nat) (s : State α) (ht : physicalBlock t ∉ bs) :
    (splitBlocks p ops input bs s).pc t = s.pc t ∧
    (splitBlocks p ops input bs s).indices t = s.indices t ∧
    (splitBlocks p ops input bs s).regs t = s.regs t := by
  induction bs generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons b bs ih =>
      have hn : physicalBlock t ∉ bs := by intro hm; exact ht (by simp [hm])
      have hb : t ∉ blockThreads (geometry p) b := by
        intro hm
        exact ht (by simp [(native_block_mem p b t).mp hm])
      have later := ih (splitBlockState p ops input b s) hn
      have first := split_block_other p ops input b t s hb
      exact ⟨later.1.trans first.1, later.2.1.trans first.2.1, later.2.2.trans first.2.2⟩

theorem split_blocks_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (s : State α) (loc : Location)
    (hn : loc.buffer ≠ 0 ∨ physicalBlock (loc.offset / 4) ∉ bs) :
    (splitBlocks p ops input bs s).memory loc = s.memory loc := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
      have htail : loc.buffer ≠ 0 ∨ physicalBlock (loc.offset / 4) ∉ bs := by
        rcases hn with hb | ho
        · exact Or.inl hb
        · exact Or.inr (by intro hm; exact ho (by simp [hm]))
      have hfirst : loc.buffer ≠ 0 ∨ physicalBlock (loc.offset / 4) ≠ b := by
        rcases hn with hb | ho
        · exact Or.inl hb
        · exact Or.inr (by intro eq; exact ho (by simp [eq]))
      exact (ih (splitBlockState p ops input b s) htail).trans
        (split_block_memory_frame p ops input b s loc hfirst)

theorem split_blocks_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (s : State α) (hn : bs.Nodup) (hb : ∀ b ∈ bs, b < p.rows * 5)
    (hp : ∀ b ∈ bs, ∀ t ∈ blockThreads (geometry p) b, s.pc t = 0) (hr : Reads p input s) :
    bs.foldlM (fun s b => LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true)
      b fuel.block s) s = some (splitBlocks p ops input bs s) := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rw [List.foldlM_cons, native_split_block p ops input b s (hb b (by simp)) (hp b (by simp)) hr]
      simp only [bind, Option.some_bind]
      apply ih (splitBlockState p ops input b s) hnodup
      · intro c hc; exact hb c (by simp [hc])
      · intro c hc t ht
        have hne : c ≠ b := by intro eq; subst c; exact hnot hc
        have outside : t ∉ blockThreads (geometry p) b := by
          intro hm
          exact hne (((native_block_mem p c t).mp ht).symm.trans ((native_block_mem p b t).mp hm))
        exact (split_block_other p ops input b t s outside).1.trans (hp c (by simp [hc]) t ht)
      · exact split_block_reads p ops input b s hr

theorem split_blocks_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (s : State α) (hn : bs.Nodup) (b t : Nat) (hb : b ∈ bs)
    (ht : t ∈ blockThreads (geometry p) b) : (splitBlocks p ops input bs s).pc t = 106 := by
  induction bs generalizing s with
  | nil => simp at hb
  | cons c bs ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hb with eq | hb
      · subst b
        have outside : physicalBlock t ∉ bs := by simpa only [(native_block_mem p c t).mp ht] using hnot
        exact (split_blocks_other p ops input bs t (splitBlockState p ops input c s) outside).1.trans
          (split_block_pc p ops input c t s ht)
      · exact ih (splitBlockState p ops input c s) hnodup hb

theorem split_blocks_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (s : State α) (hn : bs.Nodup) (b t e : Nat) (hb : b ∈ bs)
    (ht : t ∈ blockThreads (geometry p) b) (he : e < 4) :
    (splitBlocks p ops input bs s).memory (globalCell 0 (outputAddress t e)) =
      some (splitSourceResult ops input t e) := by
  induction bs generalizing s with
  | nil => simp at hb
  | cons c bs ih =>
      obtain ⟨hnot, hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hb with eq | hb
      · subst b
        have outside : physicalBlock ((globalCell 0 (outputAddress t e)).offset / 4) ∉ bs := by
          simpa only [globalCell, output_owner t e he, (native_block_mem p c t).mp ht] using hnot
        exact (split_blocks_memory_frame p ops input bs (splitBlockState p ops input c s) _ (Or.inr outside)).trans
          (split_block_value p ops input c t e s ht he)
      · exact ih (splitBlockState p ops input c s) hnodup hb

theorem split_blocks_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (s : State α) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (splitBlocks p ops input bs s).trace, Good access := by
  induction bs generalizing s with
  | nil => exact good
  | cons b bs ih => exact ih (splitBlockState p ops input b s) (split_block_good p ops input b s good)

theorem split_blocks_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (s : State α) : (splitBlocks p ops input bs s).trace.length = s.trace.length + 5120 * bs.length := by
  induction bs generalizing s with
  | nil => simp [splitBlocks]
  | cons b bs ih =>
      change (splitBlocks p ops input bs (splitBlockState p ops input b s)).trace.length = _
      rw [ih, split_block_trace_length]
      simp only [List.length_cons]
      omega

#print axioms split_native_block_bound
#print axioms split_blocks_reads
#print axioms split_blocks_other
#print axioms split_blocks_memory_frame
#print axioms split_blocks_run
#print axioms split_blocks_pc
#print axioms split_blocks_value
#print axioms split_blocks_good
#print axioms split_blocks_trace_length
end LarkNativeQKNormRope
