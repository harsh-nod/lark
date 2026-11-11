import Lark.NativeAttentionForeignControl

/-! Output ownership preserves completed blocks while later blocks execute. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000

theorem first_resumed_output_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b offset : Nat)
    (s : State α) (ho : writer offset ∉ blockThreads (geometry p) b) :
    (firstResumed p ops input b s).memory (globalCell 0 offset) = s.memory (globalCell 0 offset) := by
  have hs := first_resumed_eq p ops input b s
  have hb : firstBlock p ops input b s = firstFold ops input (blockThreads (geometry p) b) s := rfl
  exact (congrArg (fun state : State α => state.memory (globalCell 0 offset)) hs).trans
    ((resume_memory_of _ .block _ _).trans
      ((congrArg (fun state : State α => state.memory (globalCell 0 offset)) hb).trans
        (first_fold_output_other ops input _ offset s ho)))

theorem query_resumed_output_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (key b offset : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) (ho : writer offset ∉ blockThreads (geometry p) b) :
    (queryResumed p ops input key b old s).memory (globalCell 0 offset) = s.memory (globalCell 0 offset) := by
  have hs := query_resumed_state p ops input key b old s
  have hb : queryBlock p ops input key b old s = queryFold ops input key old (blockThreads (geometry p) b) s := rfl
  exact (congrArg (fun state : State α => state.memory (globalCell 0 offset)) hs).trans
    ((resume_memory_of _ .block _ _).trans
      ((congrArg (fun state : State α => state.memory (globalCell 0 offset)) hb).trans
        (query_fold_output_other ops input key old _ offset s ho)))

theorem keys_completed_output_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b key offset : Nat)
    (s : State α) (ho : writer offset ∉ blockThreads (geometry p) b) :
    (keysCompleted p ops input b key s).memory (globalCell 0 offset) = s.memory (globalCell 0 offset) := by
  induction key with
  | zero =>
      exact (congrArg (fun state : State α => state.memory (globalCell 0 offset)) (keys_completed_zero p ops input b s)).trans
        (query_resumed_output_foreign p ops input 0 b offset (onlineValues ops input 0) s ho)
  | succ key ih =>
      have hq := query_resumed_output_foreign p ops input (key + 1) b offset (onlineValues ops input (key + 1))
        (nextResumed p ops input key b (keysCompleted p ops input b key s)) ho
      have hn := next_resumed_memory_other p ops input key b (keysCompleted p ops input b key s) (globalCell 0 offset) (by simp [globalCell])
      exact (congrArg (fun state : State α => state.memory (globalCell 0 offset)) (keys_completed_succ p ops input b key s)).trans
        (hq.trans (hn.trans ih))

theorem final_block_output_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b offset : Nat)
    (s : State α) (ho : writer offset ∉ blockThreads (geometry p) b) :
    (finalBlock p ops input b s).memory (globalCell 0 offset) = s.memory (globalCell 0 offset) :=
  (congrArg (fun memory => memory (globalCell 0 offset)) (final_block_frames p ops input b s).1).trans
    ((keys_completed_output_foreign p ops input b 3 offset (firstResumed p ops input b s) ho).trans
      (first_resumed_output_foreign p ops input b offset s ho))

theorem block_member_owner (p : Shape) (b t : Nat) (ht : t ∈ blockThreads (geometry p) b) : t / 32 = b := by
  obtain ⟨lane, hl, he⟩ := (block_mem p b t).mp ht
  omega

theorem block_not_member (p : Shape) (b t : Nat) (ht : t / 32 ≠ b) : t ∉ blockThreads (geometry p) b := by
  intro hm
  exact ht (block_member_owner p b t hm)

#print axioms keys_completed_output_foreign
#print axioms final_block_output_foreign
end LarkNativeAttention
