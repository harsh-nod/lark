import Lark.PtxFeedForwardUp

/- Exact full-size FFN up-stage ReLU/FP16-store epilogue and lane execution.
   Whole-launch extraction/race freedom and the second stage remain separate work. -/
namespace LarkPtxMatrix
open LarkNonlinear LarkPtxPointwise LarkPtxDot
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
namespace FfnUp

def outputCell (t : Nat) : Location := ⟨.global, 0, 2, t⟩
def exitGlobal (s : Machine α) : Machine α := setPointer s 44 ⟨2, 0, true⟩
def exitZero (ops : Ops α) (s : Machine α) : Machine α :=
  setFloat (exitGlobal s) 68 (ops.literal 0 1)
def exitRelu (ops : Ops α) (acc : α) (s : Machine α) : Machine α :=
  setFloat (exitZero ops s) 67 (ops.max acc (ops.literal 0 1))
def exitHalf (ops : Ops α) (acc : α) (s : Machine α) : Machine α :=
  setHalf (exitRelu ops acc s) 33 (ops.toHalf (ops.max acc (ops.literal 0 1)))
def exitWide (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) : Machine α :=
  setIndex64 (exitHalf ops acc s) 45 ((t*2 : Nat) : Int)
def exitAddress (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) : Machine α :=
  setPointer (exitWide ops t acc s) 46 ⟨2, ((t*2 : Nat) : Int), true⟩
def exitStored (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) : Machine α :=
  storedHalf (exitAddress ops t acc s) t (outputCell t) (ops.toHalf (ops.max acc (ops.literal 0 1)))
def exitReturned (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) : Machine α :=
  returned (exitStored ops t acc s)

theorem output_address (t : Nat) (ht : t < 65536) :
    address layout geometry t ⟨2, ((t*2 : Nat) : Int), true⟩ 0 true = some (outputCell t) := by
  have hs : signed64 ((t : Int)*2) := by unfold signed64; omega
  have hr : (Role.output == Role.input) = false := rfl
  rw [aligned_address layout geometry t 2 t _ 0 true (by simp) hs]
  simp [location, layout, ht, outputCell, hr]

theorem epilogue_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (acc : α)
    (s : Machine α) (ht : t < 65536) (h : LoopInvariant input t 16 acc s) :
    Steps ops layout geometry t program s (exitReturned ops t acc s) := by
  have hpc : s.pc = 165 := h.pc
  have e1 := global_step ops layout geometry t 44 24 s ⟨2, 0, false⟩ h.output
  have h1 : Steps ops layout geometry t program s (exitGlobal s) := by
    apply one_step
    rw [transition_at ops layout geometry t program s (.base (.toGlobal 44 24))
      h.stopped (by rw [hpc]; rfl), base_step]
    exact e1
  have hZero : Steps ops layout geometry t program (exitGlobal s) (exitZero ops s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (exitGlobal s) (.base (.literalFloat 68 0 1))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[s.pc+1]? = _; rw [hpc]; rfl), base_step]
    exact zero_float_step ops layout geometry t 68 (exitGlobal s)
  have hxRelu : (exitZero ops s).registers.scalar 69 = some acc := by
    change s.registers.scalar 69 = some acc
    exact h.accumulator
  have eRelu := binaryFloat_step ops layout geometry t 67 69 68 .max
    (exitZero ops s) acc (ops.literal 0 1) hxRelu (by rfl)
  have hRelu : Steps ops layout geometry t program (exitZero ops s) (exitRelu ops acc s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (exitZero ops s) (.base (.binaryFloat 67 .max 69 68))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[s.pc+2]? = _; rw [hpc]; rfl), base_step]
    exact eRelu
  have e2 := half_step ops layout geometry t 33 67 (exitRelu ops acc s)
    (ops.max acc (ops.literal 0 1)) (by rfl)
  have h2 : Steps ops layout geometry t program (exitRelu ops acc s) (exitHalf ops acc s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (exitRelu ops acc s) (.base (.toHalf 33 67))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[s.pc+3]? = _; rw [hpc]; rfl), base_step]
    exact e2
  have hb : signed32 (t : Int) ∧ signed32 2 ∧ signed64 ((t : Int)*2) := by
    unfold signed32 signed64; omega
  have hx : (exitHalf ops acc s).registers.i32 1 = some (t : Int) := by
    change s.registers.i32 1 = some (t : Int)
    exact h.thread
  have e3 := wide_step ops layout geometry t 45 1 2 (t : Int) (exitHalf ops acc s) hx hb
  have he : (t : Int)*2 = ((t*2 : Nat) : Int) := by simp
  rw [he] at e3
  have h3 : Steps ops layout geometry t program (exitHalf ops acc s) (exitWide ops t acc s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (exitHalf ops acc s) (.base (.mulWideSigned32 45 1 2))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[s.pc+4]? = _; rw [hpc]; rfl), base_step]
    exact e3
  have hp : signed64 ((t*2 : Nat) : Int) ∧ signed64 (0+((t*2 : Nat) : Int)) := by
    unfold signed64; simp only [Int.natCast_mul]; omega
  have e4 := pointer_add_step ops layout geometry t 46 44 (.reg 45) ⟨2, 0, true⟩
    ((t*2 : Nat) : Int) (exitWide ops t acc s) (by rfl) (by simp [operand64, exitWide, setIndex64_i64]) hp
  simp only [Int.zero_add] at e4
  have h4 : Steps ops layout geometry t program (exitWide ops t acc s) (exitAddress ops t acc s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (exitWide ops t acc s) (.base (.addSigned64 46 44 (.reg 45)))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[s.pc+5]? = _; rw [hpc]; rfl), base_step]
    exact e4
  have e5 := store_step ops layout geometry t 46 33 0 (exitAddress ops t acc s)
    ⟨2, ((t*2 : Nat) : Int), true⟩ (outputCell t) (ops.toHalf (ops.max acc (ops.literal 0 1))) (by rfl)
    (output_address t ht) (by rfl)
  have h5 : Steps ops layout geometry t program (exitAddress ops t acc s) (exitStored ops t acc s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (exitAddress ops t acc s) (.base (.storeHalf 46 0 33))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[s.pc+6]? = _; rw [hpc]; rfl), base_step]
    exact e5
  have h6 : Steps ops layout geometry t program (exitStored ops t acc s) (exitReturned ops t acc s) := by
    apply one_step
    rw [transition_at ops layout geometry t program (exitStored ops t acc s) (.base .ret)
      (by change s.registers.stopped = false; exact h.stopped)
      (by change program[s.pc+7]? = _; rw [hpc]; rfl), base_step]
    exact return_step ops layout geometry t _
  apply steps_trans _ _ _ _ _ _ _ _ h1
  apply steps_trans _ _ _ _ _ _ _ _ hZero
  apply steps_trans _ _ _ _ _ _ _ _ hRelu
  apply steps_trans _ _ _ _ _ _ _ _ h2
  apply steps_trans _ _ _ _ _ _ _ _ h3
  apply steps_trans _ _ _ _ _ _ _ _ h4
  exact steps_trans _ _ _ _ _ _ _ _ h5 h6

theorem runTerms_memory (ops : Ops α) (input : Nat → Nat → α) (t c j n : Nat) (acc : α)
    (s : Machine α) :
    (runTerms ops input t c j n acc s).registers.base.memory = s.registers.base.memory := by
  induction n generalizing j acc s with
  | zero => rfl
  | succ n ih => simp only [runTerms, ih, chunkStep, termResult_memory]

theorem bodyEnd_memory (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) :
    (bodyEnd ops input t c acc s).registers.base.memory = s.registers.base.memory := by
  simp only [bodyEnd, runTerms_memory, bodyStart, setPointer_base]

theorem iteration_memory (ops : Ops α) (input : Nat → Nat → α) (t c : Nat) (acc : α)
    (s : Machine α) :
    (iteration ops input t c acc s).registers.base.memory = s.registers.base.memory := by
  simp only [iteration, control_memory, bodyEnd_memory]

theorem runChunks_memory (ops : Ops α) (input : Nat → Nat → α) (t c n : Nat) (acc : α)
    (s : Machine α) :
    (runChunks ops input t c n acc s).registers.base.memory = s.registers.base.memory := by
  induction n generalizing c acc s with
  | zero => rfl
  | succ n ih => simp only [runChunks, ih, iteration_memory]

theorem loopExit_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (loopExit ops input t s).registers.base.memory = s.memory := by
  simp only [loopExit, runChunks_memory, initialized_base]

theorem exitReturned_memory (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) :
    (exitReturned ops t acc s).registers.base.memory =
      fun l => if l = outputCell t then some (ops.toHalf (ops.max acc (ops.literal 0 1))) else s.registers.base.memory l := rfl

theorem exitReturned_stopped (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) :
    (exitReturned ops t acc s).registers.stopped = true := rfl

theorem exitReturned_pc (ops : Ops α) (t : Nat) (acc : α) (s : Machine α) :
    (exitReturned ops t acc s).pc = s.pc+8 := rfl

def laneResult (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Machine α :=
  exitReturned ops t (dotValue ops input t) (loopExit ops input t s)

theorem source_lane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (ht : t < 65536) (hreads : Reads input (start s)) :
    Steps ops layout geometry t program (start s) (laneResult ops input t s) ∧
    (laneResult ops input t s).registers.stopped = true ∧ (laneResult ops input t s).pc = 173 := by
  have hl := source_to_loop_exit ops input t s ht hreads
  have he := epilogue_execute ops input t (dotValue ops input t) (loopExit ops input t s) ht hl.2
  refine ⟨steps_trans _ _ _ _ _ _ _ _ hl.1 he, exitReturned_stopped _ _ _ _, ?_⟩
  rw [laneResult, exitReturned_pc, hl.2.pc]
  rfl

theorem laneResult_memory (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (laneResult ops input t s).registers.base.memory =
      fun l => if l = outputCell t then some (ops.toHalf (ops.max (dotValue ops input t) (ops.literal 0 1))) else s.memory l := by
  rw [laneResult, exitReturned_memory, loopExit_memory]

end FfnUp
#print axioms FfnUp.epilogue_execute
#print axioms FfnUp.source_lane
#print axioms FfnUp.laneResult_memory
end LarkPtxMatrix
