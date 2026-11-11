import Lark.NativeAttentionFirstKey

/-! Generic scalar-machine frames for scheduling the remaining member lanes. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

structure EvalFrame (s next : State α) : Prop where
  pc : next.pc = s.pc
  indices : next.indices = s.indices
  regs : next.regs = s.regs
  memory : next.memory = s.memory
  epochs : next.epochs = s.epochs

theorem eval_frame_trans (s mid next : State α) (h1 : EvalFrame s mid) (h2 : EvalFrame mid next) : EvalFrame s next :=
  ⟨h2.pc.trans h1.pc, h2.indices.trans h1.indices, h2.regs.trans h1.regs,
    h2.memory.trans h1.memory, h2.epochs.trans h1.epochs⟩

theorem eval_expr_frame (ops : Ops α) (layout : Layout) (g : Geometry) (t : Nat) (e : Expr)
    (s : State α) (value : α) (next : State α) (he : evalExpr ops layout g t e s = some (value, next)) : EvalFrame s next := by
  induction e generalizing s value next with
  | lit n d =>
      by_cases hd : d = 0
      · simp [evalExpr, hd] at he
      · simp [evalExpr, hd] at he
        rcases he with ⟨rfl, rfl⟩
        exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | reg r =>
      cases hv : s.regs t r with
      | none => simp [evalExpr, hv] at he
      | some x =>
          simp [evalExpr, hv] at he
          rcases he with ⟨rfl, rfl⟩
          exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | load space buffer ix =>
      cases hi : evalIndex g t s ix with
      | none => simp [evalExpr, hi] at he
      | some index =>
          cases hl : location layout g t space buffer index false with
          | none => simp [evalExpr, hi, hl] at he
          | some loc =>
              cases hv : s.memory loc with
              | none => simp [evalExpr, hi, hl, hv] at he
              | some x =>
                  simp [evalExpr, hi, hl, hv] at he
                  rcases he with ⟨rfl, rfl⟩
                  exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | bin op a b iha ihb =>
      cases ha : evalExpr ops layout g t a s with
      | none => simp [evalExpr, ha] at he
      | some pair =>
          rcases pair with ⟨x, mid⟩
          cases hb : evalExpr ops layout g t b mid with
          | none => simp [evalExpr, ha, hb] at he
          | some pair =>
              rcases pair with ⟨y, final⟩
              simp [evalExpr, ha, hb] at he
              rcases he with ⟨rfl, rfl⟩
              exact eval_frame_trans s mid final (iha s x mid ha) (ihb mid y final hb)
  | un op a ih =>
      cases ha : evalExpr ops layout g t a s with
      | none => simp [evalExpr, ha] at he
      | some pair =>
          rcases pair with ⟨x, mid⟩
          simp [evalExpr, ha] at he
          rcases he with ⟨rfl, rfl⟩
          exact ih s x mid ha

theorem execute_lane_other (ops : Ops α) (layout : Layout) (g : Geometry) (t u : Nat) (i : Instr)
    (s next : State α) (hne : u ≠ t) (he : execute ops layout g t i s = some next) :
    next.pc u = s.pc u ∧ next.indices u = s.indices u ∧ next.regs u = s.regs u := by
  cases i with
  | index r ix =>
      cases hv : evalIndex g t s ix with
      | none => simp [execute, hv] at he
      | some x =>
          simp [execute, hv] at he
          subst next
          simp [advance, hne]
  | assign r e =>
      cases hv : evalExpr ops layout g t e s with
      | none => simp [execute, hv] at he
      | some pair =>
          rcases pair with ⟨x, mid⟩
          have hf := eval_expr_frame ops layout g t e s x mid hv
          simp [execute, hv] at he
          subst next
          simpa [advance, hne] using
            (show mid.pc u = s.pc u ∧ mid.indices u = s.indices u ∧ mid.regs u = s.regs u from
              ⟨congrArg (fun pc => pc u) hf.pc, congrArg (fun indices => indices u) hf.indices, congrArg (fun regs => regs u) hf.regs⟩)
  | store space buffer ix e =>
      cases hi : evalIndex g t s ix with
      | none => simp [execute, hi] at he
      | some index =>
          cases hl : location layout g t space buffer index true with
          | none => simp [execute, hi, hl] at he
          | some loc =>
              cases hv : evalExpr ops layout g t e s with
              | none => simp [execute, hi, hl, hv] at he
              | some pair =>
                  rcases pair with ⟨x, mid⟩
                  have hf := eval_expr_frame ops layout g t e s x mid hv
                  simp [execute, hi, hl, hv] at he
                  subst next
                  simpa [record, advance, hne] using
                    (show mid.pc u = s.pc u ∧ mid.indices u = s.indices u ∧ mid.regs u = s.regs u from
                      ⟨congrArg (fun pc => pc u) hf.pc, congrArg (fun indices => indices u) hf.indices, congrArg (fun regs => regs u) hf.regs⟩)
  | branch pred target =>
      cases hv : evalPredicate g t s pred with
      | none => simp [execute, hv] at he
      | some yes =>
          simp [execute, hv] at he
          subst next
          simp [advance, hne]
  | jump target =>
      simp [execute] at he
      subst next
      simp [advance, hne]
  | barrier cut => simp [execute] at he
  | halt => simp [execute] at he

theorem run_lane_other (ops : Ops α) (layout : Layout) (g : Geometry) (p : List Instr) (t u n : Nat)
    (s next : State α) (hne : u ≠ t) (he : runLane ops layout g p t n s = some next) :
    next.pc u = s.pc u ∧ next.indices u = s.indices u ∧ next.regs u = s.regs u := by
  induction n generalizing s with
  | zero => simp [runLane] at he
  | succ n ih =>
      cases hc : parked p s t with
      | some cut =>
          simp [runLane, hc] at he
          subst next
          exact ⟨rfl, rfl, rfl⟩
      | none =>
          cases hi : p[s.pc t]? with
          | none => simp [runLane, hc, hi] at he
          | some i =>
              cases hs : execute ops layout g t i s with
              | none => simp [runLane, hc, hi, hs] at he
              | some mid =>
                  simp [runLane, hc, hi, hs] at he
                  have h1 := execute_lane_other ops layout g t u i s mid hne hs
                  have h2 := ih mid he
                  exact ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

#print axioms eval_expr_frame
#print axioms execute_lane_other
#print axioms run_lane_other
end LarkNativeAttention
