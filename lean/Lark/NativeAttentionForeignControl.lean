import Lark.NativeAttentionWholeBlock

/-! A block leaves the program counters and epochs of foreign threads intact. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000

theorem resume_foreign (ts : List Nat) (cut : Cut) (u : Nat) (s : State α) (hu : u ∉ ts) :
    (resume ts cut s).pc u = s.pc u ∧ (resume ts cut s).epochs u = s.epochs u := by
  have hc : ts.contains u = false := by
    cases hc : ts.contains u with
    | false => rfl
    | true => exact False.elim (hu (List.contains_iff_mem.mp hc))
  simp [resume, hc, hu]

theorem first_resumed_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b u : Nat)
    (s : State α) (hu : u ∉ blockThreads (geometry p) b) :
    (firstResumed p ops input b s).pc u = s.pc u ∧ (firstResumed p ops input b s).epochs u = s.epochs u := by
  have hs := first_resumed_eq p ops input b s
  have hb : firstBlock p ops input b s = firstFold ops input (blockThreads (geometry p) b) s := rfl
  have hr := resume_foreign _ .block u (firstBlock p ops input b s) hu
  have hf := first_fold_other ops input (blockThreads (geometry p) b) u s hu
  exact ⟨(congrArg (fun state : State α => state.pc u) hs).trans
      (hr.1.trans ((congrArg (fun state : State α => state.pc u) hb).trans hf.1)),
    (congrArg (fun state : State α => state.epochs u) hs).trans
      (hr.2.trans (congrArg (fun epochs => epochs u) (first_block_epochs p ops input b s)))⟩

theorem query_resumed_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b key u : Nat)
    (old : Nat → Nat → QueryValue α) (s : State α) (hu : u ∉ blockThreads (geometry p) b)
    (hr : Reads p input s) (ready : ∀ t ∈ blockThreads (geometry p) b, QueryLaneReady p ops input t key (old t) s) :
    (queryResumed p ops input key b old s).pc u = s.pc u ∧ (queryResumed p ops input key b old s).epochs u = s.epochs u := by
  have hs := query_resumed_state p ops input key b old s
  have hb : queryBlock p ops input key b old s = queryFold ops input key old (blockThreads (geometry p) b) s := rfl
  have hresume := resume_foreign _ .block u (queryBlock p ops input key b old s) hu
  have hf := query_fold_other p ops input key old (blockThreads (geometry p) b) u s (block_nodup p b) hr ready hu
  have he : (queryBlock p ops input key b old s).epochs = s.epochs :=
    (congrArg (fun state : State α => state.epochs) hb).trans (query_fold_epochs ops input key old _ s)
  exact ⟨(congrArg (fun state : State α => state.pc u) hs).trans
      (hresume.1.trans ((congrArg (fun state : State α => state.pc u) hb).trans hf.1)),
    (congrArg (fun state : State α => state.epochs u) hs).trans (hresume.2.trans (congrArg (fun epochs => epochs u) he))⟩

theorem next_resumed_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b key u : Nat)
    (s : State α) (hu : u ∉ blockThreads (geometry p) b) :
    (nextResumed p ops input key b s).pc u = s.pc u ∧ (nextResumed p ops input key b s).epochs u = s.epochs u := by
  have hs := next_resumed_state p ops input key b s
  have hb : nextBlock p ops input key b s = nextFold ops input key (blockThreads (geometry p) b) s := rfl
  have hr := resume_foreign _ .block u (nextBlock p ops input key b s) hu
  have hf := next_fold_other ops input key (blockThreads (geometry p) b) u s hu
  have he : (nextBlock p ops input key b s).epochs = s.epochs :=
    (congrArg (fun state : State α => state.epochs) hb).trans (next_fold_epochs ops input key _ s)
  exact ⟨(congrArg (fun state : State α => state.pc u) hs).trans
      (hr.1.trans ((congrArg (fun state : State α => state.pc u) hb).trans hf.1)),
    (congrArg (fun state : State α => state.epochs u) hs).trans (hr.2.trans (congrArg (fun epochs => epochs u) he))⟩

theorem keys_completed_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b key u : Nat)
    (s : State α) (hu : u ∉ blockThreads (geometry p) b) (start : QueryStart p ops input b 0 s) :
    (keysCompleted p ops input b key s).pc u = s.pc u ∧ (keysCompleted p ops input b key s).epochs u = s.epochs u := by
  induction key with
  | zero =>
      have hs := keys_completed_zero p ops input b s
      have hf := query_resumed_foreign p ops input b 0 u (onlineValues ops input 0) s hu start.reads start.ready
      exact ⟨(congrArg (fun state : State α => state.pc u) hs).trans hf.1,
        (congrArg (fun state : State α => state.epochs u) hs).trans hf.2⟩
  | succ key ih =>
      have done := keys_completed_spec p ops input b key s start
      have copied := copy_phase_start p ops input b key (keysCompleted p ops input b key s) done
      have hq := query_resumed_foreign p ops input b (key + 1) u (onlineValues ops input (key + 1))
        (nextResumed p ops input key b (keysCompleted p ops input b key s)) hu copied.reads copied.ready
      have hn := next_resumed_foreign p ops input b key u (keysCompleted p ops input b key s) hu
      have hs := keys_completed_succ p ops input b key s
      exact ⟨(congrArg (fun state : State α => state.pc u) hs).trans (hq.1.trans (hn.1.trans ih.1)),
        (congrArg (fun state : State α => state.epochs u) hs).trans (hq.2.trans (hn.2.trans ih.2))⟩

theorem final_block_foreign (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b u : Nat)
    (s : State α) (hu : u ∉ blockThreads (geometry p) b) (hb : b < p.groups) (hr : Reads p input s)
    (he : ∀ t ∈ blockThreads (geometry p) b, (s.epochs t).block % 2 = 0) (hg : TraceGood s) :
    (finalBlock p ops input b s).pc u = s.pc u ∧ (finalBlock p ops input b s).epochs u = s.epochs u := by
  have hf := first_resumed_foreign p ops input b u s hu
  have hk := keys_completed_foreign p ops input b 3 u (firstResumed p ops input b s) hu (initial_query_start p ops input b s hb hr he hg)
  have hh := halt_fold_other (blockThreads (geometry p) b) u (keysCompleted p ops input b 3 (firstResumed p ops input b s)) hu
  have hs := final_block_state p ops input b s
  exact ⟨(congrArg (fun state : State α => state.pc u) hs).trans (hh.1.trans (hk.1.trans hf.1)),
    (congrArg (fun epochs => epochs u) (final_block_frames p ops input b s).2.1).trans (hk.2.trans hf.2)⟩

#print axioms first_resumed_foreign
#print axioms query_resumed_foreign
#print axioms keys_completed_foreign
#print axioms final_block_foreign
end LarkNativeAttention
