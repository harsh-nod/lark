import Lark.NativeAwqGemmOperandLane

/-! Every native lane reaches the same MFMA site with its original A/B
register fragments. Later lanes preserve earlier lanes' operand snapshots. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] operandLoop operandLoaded operandLaneState

theorem operand_lane_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t u half bank : Nat) (s : State α) (hu : u≠t) :
    (operandLaneState p ops input tile t half bank s).pc u=s.pc u ∧
      (operandLaneState p ops input tile t half bank s).indices u=s.indices u ∧
        (operandLaneState p ops input tile t half bank s).regs u=s.regs u := by
  let beforeB := operandBeforeB p ops input tile t half bank s
  have aPC : beforeB.pc u=s.pc u := by
    unfold beforeB operandBeforeB
    split
    · exact operand_loop_other_pc p ops input tile t u half bank 0 4 true s hu
    · rfl
  have aRegs : beforeB.regs u=s.regs u := by
    funext r
    unfold beforeB operandBeforeB
    split
    · exact operand_loop_reg_outside p ops input tile t u half bank 0 4 r true s
        (by intro q hlo hhi same; exact hu same.1)
    · rfl
  have bPC := operand_loop_other_pc p ops input tile t u half bank 0 4 false beforeB hu
  have bRegs : (operandLaneState p ops input tile t half bank s).regs u=beforeB.regs u := by
    funext r
    unfold operandLaneState
    exact operand_loop_reg_outside p ops input tile t u half bank 0 4 r false beforeB
      (by intro q hlo hhi same; exact hu same.1)
  exact ⟨by unfold operandLaneState; exact bPC.trans aPC,
    congrFun (operand_lane_frames p ops input tile t half bank s).2.1 u,bRegs.trans aRegs⟩

structure OperandEntry (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile half bank t : Nat) (s : State α) : Prop where
  pc : s.pc t=operandLaneStart p half bank
  lane : s.indices t 0=some ((laneId t : Nat) : Int)
  a : bank≠0 → ∀ e, e<4 → s.regs t (leftBase p half+e)=some (aOperand p ops input tile t half e)

structure OperandReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile half bank t : Nat) (s : State α) : Prop where
  pc : s.pc t=matrixPC p half bank
  lane : s.indices t 0=some ((laneId t : Nat) : Int)
  a : ∀ e, e<4 → s.regs t (leftBase p half+e)=some (aOperand p ops input tile t half e)
  b : ∀ e, e<4 → s.regs t (rightBase p half bank+e)=some (bOperand p input tile t half bank e)

theorem operand_entry_of_thread (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile half bank t : Nat) (s next : State α) (h : OperandEntry p ops input tile half bank t s)
    (hp : next.pc t=s.pc t) (hi : next.indices t=s.indices t) (hr : next.regs t=s.regs t) :
    OperandEntry p ops input tile half bank t next := by
  exact {pc := hp.trans h.pc
         lane := by rw [hi]; exact h.lane
         a := by intro nonzero e he; rw [hr]; exact h.a nonzero e he}

theorem operand_ready_of_thread (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile half bank t : Nat) (s next : State α) (h : OperandReady p ops input tile half bank t s)
    (hp : next.pc t=s.pc t) (hi : next.indices t=s.indices t) (hr : next.regs t=s.regs t) :
    OperandReady p ops input tile half bank t next := by
  exact {pc := hp.trans h.pc
         lane := by rw [hi]; exact h.lane
         a := by intro e he; rw [hr]; exact h.a e he
         b := by intro e he; rw [hr]; exact h.b e he}

theorem operand_lane_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile half bank t : Nat) (s : State α) (h : OperandEntry p ops input tile half bank t s) :
    OperandReady p ops input tile half bank t (operandLaneState p ops input tile t half bank s) := by
  exact {pc := operand_lane_pc p ops input tile t half bank s h.pc
         lane := by rw [(operand_lane_frames p ops input tile t half bank s).2.1]; exact h.lane
         a := fun e he => operand_lane_a_value p ops input tile t half bank e s he h.a
         b := fun e he => operand_lane_b_value p ops input tile t half bank e s he}

def operandFold (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile half bank : Nat) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun state t => operandLaneState p ops input tile t half bank state) s

theorem operand_fold_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile half bank u : Nat) (ts : List Nat) (s : State α) (hu : u∉ts) :
    (operandFold p ops input tile half bank ts s).pc u=s.pc u ∧
      (operandFold p ops input tile half bank ts s).indices u=s.indices u ∧
        (operandFold p ops input tile half bank ts s).regs u=s.regs u := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons t ts ih =>
    have different : u≠t := by intro same; exact hu (List.mem_cons.mpr (Or.inl same))
    have tail : u∉ts := by intro member; exact hu (List.mem_cons_of_mem t member)
    have one := operand_lane_other p ops input tile t u half bank s different
    have rest := ih (operandLaneState p ops input tile t half bank s) tail
    exact ⟨rest.1.trans one.1,rest.2.1.trans one.2.1,rest.2.2.trans one.2.2⟩

theorem operand_fold_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile half bank : Nat) (ts : List Nat) (s : State α) :
    (operandFold p ops input tile half bank ts s).memory=s.memory ∧
      (operandFold p ops input tile half bank ts s).indices=s.indices ∧
        (operandFold p ops input tile half bank ts s).epochs=s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons t ts ih =>
    have one := operand_lane_frames p ops input tile t half bank s
    have rest := ih (operandLaneState p ops input tile t half bank s)
    exact ⟨rest.1.trans one.1,rest.2.1.trans one.2.1,rest.2.2.trans one.2.2⟩

theorem operand_fold_accumulator (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile half bank u r : Nat) (ts : List Nat) (s : State α) (hr : r<4*banks p) :
    (operandFold p ops input tile half bank ts s).regs u r=s.regs u r := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    exact (ih (operandLaneState p ops input tile t half bank s)).trans (operand_lane_accumulator p ops input tile t u half bank r s hr)

theorem operand_fold_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile half bank u : Nat) (ts : List Nat) (s : State α) (hd : ts.Nodup) (hu : u∈ts)
    (entries : ∀ t∈ts, OperandEntry p ops input tile half bank t s) :
    OperandReady p ops input tile half bank u (operandFold p ops input tile half bank ts s) := by
  induction ts generalizing s with
  | nil => simp at hu
  | cons t ts ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    rcases List.mem_cons.mp hu with same | member
    · subst u
      have frame := operand_fold_other p ops input tile half bank t ts (operandLaneState p ops input tile t half bank s) disjoint
      exact operand_ready_of_thread p ops input tile half bank t (operandLaneState p ops input tile t half bank s) _
        (operand_lane_ready p ops input tile half bank t s (entries t (by simp))) frame.1 frame.2.1 frame.2.2
    · apply ih (operandLaneState p ops input tile t half bank s) tail member
      intro v hv
      have different : v≠t := by intro same; subst v; exact disjoint hv
      have frame := operand_lane_other p ops input tile t v half bank s different
      exact operand_entry_of_thread p ops input tile half bank v s _ (entries v (List.mem_cons_of_mem t hv)) frame.1 frame.2.1 frame.2.2

theorem operand_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (ts : List Nat) (s : State α) (hh : half<2) (hbank : bank<banks p) (hd : ts.Nodup)
    (blocks : ∀ t∈ts, blockId t=b) (reads : TileReads p ops input tile b s)
    (entries : ∀ t∈ts, OperandEntry p ops input tile half bank t s) :
    ts.foldlM (fun state t => LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane state) s=
      some (operandFold p ops input tile half bank ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    have head := entries t (by simp)
    rw [List.foldlM_cons,operand_lane_run p ops input tile b t half bank s (blocks t (by simp)) hh hbank head.lane reads head.pc]
    change ts.foldlM (fun state t => LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane state)
      (operandLaneState p ops input tile t half bank s)=
        some (operandFold p ops input tile half bank ts (operandLaneState p ops input tile t half bank s))
    apply ih (operandLaneState p ops input tile t half bank s) tail
      (by intro u hu; exact blocks u (List.mem_cons_of_mem t hu))
      (tile_reads_of_memory p ops input tile b s _ reads (operand_lane_frames p ops input tile t half bank s).1)
    intro u hu
    have different : u≠t := by intro same; subst u; exact disjoint hu
    have frame := operand_lane_other p ops input tile t u half bank s different
    exact operand_entry_of_thread p ops input tile half bank u s _ (entries u (List.mem_cons_of_mem t hu)) frame.1 frame.2.1 frame.2.2

#print axioms operand_lane_other
#print axioms operand_entry_of_thread
#print axioms operand_ready_of_thread
#print axioms operand_lane_ready
#print axioms operand_fold_other
#print axioms operand_fold_frames
#print axioms operand_fold_accumulator
#print axioms operand_fold_ready
#print axioms operand_fold_run
end LarkNativeAwqGemm
