import Lark.NativeAttentionForeignOutput

/-! Composition of complete native blocks, preserving prior block outputs. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000

structure GridBlockReady (p : Shape) (b : Nat) (s : State α) : Prop where
  bound : b < p.groups
  pc : ∀ t ∈ blockThreads (geometry p) b, s.pc t = 0
  even : ∀ t ∈ blockThreads (geometry p) b, (s.epochs t).block % 2 = 0

def fullBlocks (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (bs : List Nat) (s : State α) : State α :=
  bs.foldl (fun s b => finalBlock p ops input b s) s

theorem full_blocks_tail_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat)
    (bs : List Nat) (s : State α) (hn : (b :: bs).Nodup) (hr : Reads p input s) (hg : TraceGood s)
    (ready : ∀ c ∈ b :: bs, GridBlockReady p c s) :
    ∀ c ∈ bs, GridBlockReady p c (finalBlock p ops input b s) := by
  intro c hc
  have hb := ready b (by simp)
  have other := ready c (by simp [hc])
  have hne : c ≠ b := by intro he; subst c; exact (List.nodup_cons.mp hn).1 hc
  have hf := fun t ht => final_block_foreign p ops input b t s
    (block_not_member p b t (by rw [block_member_owner p c t ht]; exact hne)) hb.bound hr hb.even hg
  exact ⟨other.bound, (by intro t ht; exact (hf t ht).1.trans (other.pc t ht)),
    (by intro t ht; rw [(hf t ht).2]; exact other.even t ht)⟩

theorem full_blocks_reads_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (bs : List Nat)
    (s : State α) (hn : bs.Nodup) (hr : Reads p input s) (hg : TraceGood s)
    (ready : ∀ b ∈ bs, GridBlockReady p b s) : Reads p input (fullBlocks p ops input bs s) ∧ TraceGood (fullBlocks p ops input bs s) := by
  induction bs generalizing s with
  | nil => exact ⟨hr, hg⟩
  | cons b bs ih =>
      have hb := ready b (by simp)
      exact ih (finalBlock p ops input b s) (List.nodup_cons.mp hn).2
        (final_block_reads p ops input b s hb.bound hr hb.even hg) (final_block_good p ops input b s hb.bound hr hb.even hg)
        (full_blocks_tail_ready p ops input b bs s hn hr hg ready)

theorem full_blocks_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (bs : List Nat)
    (s : State α) (hn : bs.Nodup) (hr : Reads p input s) (hg : TraceGood s)
    (ready : ∀ b ∈ bs, GridBlockReady p b s) :
    bs.foldlM (fun s b => runBlock ops (layout p) (geometry p) fuel program b fuel.block s) s = some (fullBlocks p ops input bs s) := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
      have hb := ready b (by simp)
      rw [List.foldlM_cons, final_block_run p ops input b s hb.bound hr hb.pc hb.even hg]
      simp only [bind, Option.some_bind]
      exact ih _ (List.nodup_cons.mp hn).2 (final_block_reads p ops input b s hb.bound hr hb.even hg)
        (final_block_good p ops input b s hb.bound hr hb.even hg) (full_blocks_tail_ready p ops input b bs s hn hr hg ready)

theorem full_blocks_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (bs : List Nat) (u : Nat)
    (s : State α) (hn : bs.Nodup) (hr : Reads p input s) (hg : TraceGood s)
    (ready : ∀ b ∈ bs, GridBlockReady p b s) (hu : u / 32 ∉ bs) :
    (fullBlocks p ops input bs s).pc u = s.pc u ∧ (fullBlocks p ops input bs s).epochs u = s.epochs u := by
  induction bs generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons b bs ih =>
      have hb := ready b (by simp)
      have hne : u / 32 ≠ b := by intro he; exact hu (by simp [he])
      have hf := final_block_foreign p ops input b u s (block_not_member p b u hne) hb.bound hr hb.even hg
      have ht := ih (finalBlock p ops input b s) (List.nodup_cons.mp hn).2
        (final_block_reads p ops input b s hb.bound hr hb.even hg) (final_block_good p ops input b s hb.bound hr hb.even hg)
        (full_blocks_tail_ready p ops input b bs s hn hr hg ready) (by intro hm; exact hu (by simp [hm]))
      exact ⟨ht.1.trans hf.1, ht.2.trans hf.2⟩

theorem full_blocks_output_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (bs : List Nat)
    (offset : Nat) (s : State α) (ho : writer offset / 32 ∉ bs) :
    (fullBlocks p ops input bs s).memory (globalCell 0 offset) = s.memory (globalCell 0 offset) := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
      have hb : writer offset ∉ blockThreads (geometry p) b :=
        block_not_member p b (writer offset) (by intro he; exact ho (by simp [he]))
      exact (ih (finalBlock p ops input b s) (by intro hm; exact ho (by simp [hm]))).trans
        (final_block_output_foreign p ops input b offset s hb)

theorem full_blocks_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (bs : List Nat) (b t : Nat)
    (s : State α) (hn : bs.Nodup) (hr : Reads p input s) (hg : TraceGood s)
    (ready : ∀ c ∈ bs, GridBlockReady p c s) (hb : b ∈ bs) (ht : t ∈ blockThreads (geometry p) b) :
    (fullBlocks p ops input bs s).pc t = 90 := by
  induction bs generalizing s with
  | nil => simp at hb
  | cons c bs ih =>
      have hc := ready c (by simp)
      have reads := final_block_reads p ops input c s hc.bound hr hc.even hg
      have good := final_block_good p ops input c s hc.bound hr hc.even hg
      have tailReady := full_blocks_tail_ready p ops input c bs s hn hr hg ready
      rcases List.mem_cons.mp hb with he | hm
      · subst b
        exact (full_blocks_foreign p ops input bs t (finalBlock p ops input c s) (List.nodup_cons.mp hn).2 reads good tailReady
          (by simpa only [block_member_owner p c t ht] using (List.nodup_cons.mp hn).1)).1.trans (final_block_member p ops input c t s ht).1
      · exact ih (finalBlock p ops input c s) (List.nodup_cons.mp hn).2 reads good tailReady hm

theorem full_blocks_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (bs : List Nat) (b t qi col : Nat)
    (s : State α) (hn : bs.Nodup) (hr : Reads p input s) (hg : TraceGood s)
    (ready : ∀ c ∈ bs, GridBlockReady p c s) (hb : b ∈ bs) (ht : t ∈ blockThreads (geometry p) b) (hi : qi < 4) (hc : col < 256) :
    (fullBlocks p ops input bs s).memory (globalCell 0 (globalAddress t qi col)) = some ((onlineValues ops input 4 t qi).stored col) := by
  induction bs generalizing s with
  | nil => simp at hb
  | cons c bs ih =>
      have current := ready c (by simp)
      have reads := final_block_reads p ops input c s current.bound hr current.even hg
      have good := final_block_good p ops input c s current.bound hr current.even hg
      have tailReady := full_blocks_tail_ready p ops input c bs s hn hr hg ready
      rcases List.mem_cons.mp hb with he | hm
      · subst b
        exact (full_blocks_output_foreign p ops input bs (globalAddress t qi col) (finalBlock p ops input c s)
          (by simpa only [global_address_owner t qi col hi hc, block_member_owner p c t ht] using (List.nodup_cons.mp hn).1)).trans
          (final_block_values p ops input c t qi col s current.bound hr current.even hg ht hi hc)
      · exact ih (finalBlock p ops input c s) (List.nodup_cons.mp hn).2 reads good tailReady hm

#print axioms full_blocks_run
#print axioms full_blocks_reads_good
#print axioms full_blocks_pc
#print axioms full_blocks_value
end LarkNativeAttention
