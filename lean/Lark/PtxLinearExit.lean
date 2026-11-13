import Lark.PtxLinearBody

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- Actual compiled Linear bias epilogue and return. Development evidence:
   whole-launch reference extraction and actual-trace race proofs are needed
   before this becomes a complete independent kernel certificate. -/
namespace LarkPtxLinear.Linear.Exit
open LarkNonlinear LarkPtxPointwise
open LarkPtxDot
open LarkPtxMatrix
open LarkPtxLinear.Linear.Body

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

def outputCell (t : Nat) : Location := ⟨.global, 0, 3, t⟩
def biasCell (t : Nat) : Location := ⟨.global, 0, 2, t%512⟩
def biasPointer (t : Nat) : Pointer := ⟨2, ((t%512*2 : Nat) : Int), true⟩
def outputPointer (t : Nat) : Pointer := ⟨3, ((t*2 : Nat) : Int), true⟩

def exitBiasGlobal (s : Machine α) : Machine α := setPointer s 47 ⟨2, 0, true⟩
def exitBiasShift (t : Nat) (s : Machine α) : Machine α :=
  setIndex64 (exitBiasGlobal s) 48 ((t%512*2 : Nat) : Int)
def exitBiasAddress (t : Nat) (s : Machine α) : Machine α :=
  setPointer (exitBiasShift t s) 49 (biasPointer t)
def exitBiasLoad (t : Nat) (bias : α) (s : Machine α) : Machine α :=
  loadedHalf (exitBiasAddress t s) t 33 (biasCell t) bias
def exitBiasFloat (ops : Ops α) (t : Nat) (bias : α) (s : Machine α) : Machine α :=
  setFloat (exitBiasLoad t bias s) 67 (ops.fromHalf bias)
def exitAdded (ops : Ops α) (t : Nat) (acc bias : α) (s : Machine α) : Machine α :=
  setFloat (exitBiasFloat ops t bias s) 68 (ops.add acc (ops.fromHalf bias))
def exitHalf (ops : Ops α) (t : Nat) (acc bias : α) (s : Machine α) : Machine α :=
  setHalf (exitAdded ops t acc bias s) 34 (ops.toHalf (ops.add acc (ops.fromHalf bias)))
def exitWide (ops : Ops α) (t : Nat) (acc bias : α) (s : Machine α) : Machine α :=
  setIndex64 (exitHalf ops t acc bias s) 50 ((t*2 : Nat) : Int)
def exitAddress (ops : Ops α) (t : Nat) (acc bias : α) (s : Machine α) : Machine α :=
  setPointer (exitWide ops t acc bias s) 51 (outputPointer t)
def exitStored (ops : Ops α) (t : Nat) (acc bias : α) (s : Machine α) : Machine α :=
  storedHalf (exitAddress ops t acc bias s) t (outputCell t)
    (ops.toHalf (ops.add acc (ops.fromHalf bias)))
def exitReturned (ops : Ops α) (t : Nat) (acc bias : α) (s : Machine α) : Machine α :=
  returned (exitStored ops t acc bias s)

theorem bias_address (t : Nat) :
    address LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t (biasPointer t) 0 false =
      some (biasCell t) := by
  have hc : t%512 < 512 := Nat.mod_lt _ (by decide)
  have he : ((t%512*2 : Nat) : Int)+0 = ((t%512 : Nat) : Int)*2 := by simp
  have hs : signed64 (((t%512 : Nat) : Int)*2) := by unfold signed64; omega
  unfold biasPointer
  rw [aligned_address LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 2 (t%512) _ 0 false he hs]
  exact read_location LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 2 _ ⟨.input, 512⟩
    (by rfl) hc

theorem output_address (t : Nat) (ht : t < 32768) :
    address LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t (outputPointer t) 0 true =
      some (outputCell t) := by
  have he : ((t*2 : Nat) : Int)+0 = (t : Int)*2 := by simp
  have hs : signed64 ((t : Int)*2) := by unfold signed64; omega
  have hr : (Role.output == Role.input) = false := rfl
  unfold outputPointer
  rw [aligned_address LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 3 t _ 0 true he hs]
  simp [location, LarkPtxLinear.Linear.layout, outputCell, ht, hr]

theorem epilogue_execute (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (acc bias : α)
    (s : Machine α) (ht : t < 32768) (h : LoopInvariant input t 16 acc s)
    (hbias : s.registers.base.memory (biasCell t) = some bias) :
    LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program s (exitReturned ops t acc bias s) := by
  have hpc : s.pc = 168 := h.pc
  have e1 := global_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 47 26 s
    ⟨2, 0, false⟩ h.bias
  have h1 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program s (exitBiasGlobal s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program s (.base (.base (.toGlobal 47 26)))
      h.stopped (by rw [hpc]; rfl), LarkPtxLinear.dot_step]
    exact e1
  have hc : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hx : (exitBiasGlobal s).registers.i64 18 = some ((t%512 : Nat) : Int) := by
    simpa only [exitBiasGlobal, setPointer_i64, if_neg (by decide : 18 ≠ 47)] using h.biasColumn
  have hs : signed64 ((t%512 : Nat) : Int) ∧ (1 : Nat) < 4294967296 := by
    unfold signed64; omega
  have e2 := LarkPtxLinear.shiftLeft64_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry
    t 48 18 1 ((t%512 : Nat) : Int) (exitBiasGlobal s) hx hs
  have heShift : 2*(t%512) = t%512*2 := by omega
  rw [LarkPtxLinear.column_shift_value (t%512) hc, heShift] at e2
  have h2 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitBiasGlobal s) (exitBiasShift t s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitBiasGlobal s) (.shiftLeft64 48 18 1)
      (by change s.registers.stopped = false; exact h.stopped)
      (by change LarkPtxLinear.Linear.program[s.pc+1]? = _; rw [hpc]; rfl)]
    exact e2
  have hb : signed64 ((t%512*2 : Nat) : Int) ∧ signed64 (0+((t%512*2 : Nat) : Int)) := by
    unfold signed64; simp only [Int.natCast_mul]; omega
  have e3 := pointer_add_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 49 47 (.reg 48)
    ⟨2, 0, true⟩ ((t%512*2 : Nat) : Int) (exitBiasShift t s) (by rfl)
    (by simp [operand64, exitBiasShift, setIndex64_i64]) hb
  simp only [Int.zero_add] at e3
  have h3 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitBiasShift t s) (exitBiasAddress t s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitBiasShift t s) (.base (.base (.addSigned64 49 47 (.reg 48))))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change LarkPtxLinear.Linear.program[s.pc+2]? = _; rw [hpc]; rfl), LarkPtxLinear.dot_step]
    exact e3
  have hm : (exitBiasAddress t s).registers.base.memory (biasCell t) = some bias := by
    simpa only [exitBiasAddress, exitBiasShift, exitBiasGlobal, setPointer_base, setIndex64_base] using hbias
  have e4 := loadHalf_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 33 49 0
    (exitBiasAddress t s) (biasPointer t) (biasCell t) bias (by rfl) (bias_address t) hm
  have h4 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitBiasAddress t s) (exitBiasLoad t bias s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitBiasAddress t s) (.base (.base (.loadHalf 33 49 0)))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change LarkPtxLinear.Linear.program[s.pc+3]? = _; rw [hpc]; rfl), LarkPtxLinear.dot_step]
    exact e4
  have e5 := fromHalf_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 67 33
    (exitBiasLoad t bias s) bias (by simp [exitBiasLoad])
  have h5 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitBiasLoad t bias s) (exitBiasFloat ops t bias s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitBiasLoad t bias s) (.base (.base (.fromHalf 67 33)))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change LarkPtxLinear.Linear.program[s.pc+4]? = _; rw [hpc]; rfl), LarkPtxLinear.dot_step]
    exact e5
  have hacc : (exitBiasFloat ops t bias s).registers.scalar 69 = some acc := by
    change s.registers.scalar 69 = some acc
    exact h.accumulator
  have e6 := binaryFloat_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 68 69 67 .add
    (exitBiasFloat ops t bias s) acc (ops.fromHalf bias) hacc (by simp [exitBiasFloat])
  have h6 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitBiasFloat ops t bias s) (exitAdded ops t acc bias s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitBiasFloat ops t bias s) (.base (.base (.binaryFloat 68 .add 69 67)))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change LarkPtxLinear.Linear.program[s.pc+5]? = _; rw [hpc]; rfl), LarkPtxLinear.dot_step]
    exact e6
  have e7 := half_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 34 68
    (exitAdded ops t acc bias s) (ops.add acc (ops.fromHalf bias)) (by simp [exitAdded])
  have h7 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitAdded ops t acc bias s) (exitHalf ops t acc bias s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitAdded ops t acc bias s) (.base (.base (.toHalf 34 68)))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change LarkPtxLinear.Linear.program[s.pc+6]? = _; rw [hpc]; rfl), LarkPtxLinear.dot_step]
    exact e7
  have htBound : signed32 (t : Int) ∧ signed32 2 ∧ signed64 ((t : Int)*2) := by
    unfold signed32 signed64; omega
  have htRegister : (exitHalf ops t acc bias s).registers.i32 1 = some (t : Int) := by
    change s.registers.i32 1 = some (t : Int)
    exact h.thread
  have e8 := wide_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 50 1 2 (t : Int)
    (exitHalf ops t acc bias s) htRegister htBound
  have heWide : (t : Int)*2 = ((t*2 : Nat) : Int) := by simp
  rw [heWide] at e8
  have h8 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitHalf ops t acc bias s) (exitWide ops t acc bias s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitHalf ops t acc bias s) (.base (.base (.mulWideSigned32 50 1 2)))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change LarkPtxLinear.Linear.program[s.pc+7]? = _; rw [hpc]; rfl), LarkPtxLinear.dot_step]
    exact e8
  have hOutPointer : (exitWide ops t acc bias s).registers.values (.int64 3) = some (.address ⟨3, 0, true⟩) := by
    apply pointer_values
    change s.registers.pointer 3 = some ⟨3, 0, true⟩
    exact h.output
  have hout : signed64 ((t*2 : Nat) : Int) ∧ signed64 (0+((t*2 : Nat) : Int)) := by
    unfold signed64; simp only [Int.natCast_mul]; omega
  have e9 := pointer_add_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 51 3 (.reg 50)
    ⟨3, 0, true⟩ ((t*2 : Nat) : Int) (exitWide ops t acc bias s) hOutPointer
    (by simp [operand64, exitWide, setIndex64_i64]) hout
  simp only [Int.zero_add] at e9
  have h9 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitWide ops t acc bias s) (exitAddress ops t acc bias s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitWide ops t acc bias s) (.base (.base (.addSigned64 51 3 (.reg 50))))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change LarkPtxLinear.Linear.program[s.pc+8]? = _; rw [hpc]; rfl), LarkPtxLinear.dot_step]
    exact e9
  have e10 := store_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t 51 34 0
    (exitAddress ops t acc bias s) (outputPointer t) (outputCell t)
    (ops.toHalf (ops.add acc (ops.fromHalf bias))) (by rfl) (output_address t ht) (by rfl)
  have h10 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitAddress ops t acc bias s) (exitStored ops t acc bias s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitAddress ops t acc bias s) (.base (.base (.storeHalf 51 0 34)))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change LarkPtxLinear.Linear.program[s.pc+9]? = _; rw [hpc]; rfl), LarkPtxLinear.dot_step]
    exact e10
  have h11 : LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitStored ops t acc bias s) (exitReturned ops t acc bias s) := by
    apply LarkPtxLinear.one_step
    rw [LarkPtxLinear.transition_at ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
      LarkPtxLinear.Linear.program (exitStored ops t acc bias s) (.base (.base .ret))
      (by change s.registers.stopped = false; exact h.stopped)
      (by change LarkPtxLinear.Linear.program[s.pc+10]? = _; rw [hpc]; rfl), LarkPtxLinear.dot_step]
    exact return_step ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t _
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h1
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h2
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h3
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h4
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h5
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h6
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h7
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h8
  apply LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h9
  exact LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ h10 h11

theorem exitReturned_memory (ops : Ops α) (t : Nat) (acc bias : α) (s : Machine α) :
    (exitReturned ops t acc bias s).registers.base.memory =
      fun l => if l = outputCell t then some (ops.toHalf (ops.add acc (ops.fromHalf bias)))
        else s.registers.base.memory l := rfl

theorem exitReturned_stopped (ops : Ops α) (t : Nat) (acc bias : α) (s : Machine α) :
    (exitReturned ops t acc bias s).registers.stopped = true := rfl

theorem exitReturned_pc (ops : Ops α) (t : Nat) (acc bias : α) (s : Machine α) :
    (exitReturned ops t acc bias s).pc = s.pc+11 := rfl

def Inputs (input : Nat → Nat → α) (base : State α) : Prop :=
  Reads input (LarkPtxLinear.Linear.start base) ∧
  (∀ i, i < 512 → base.memory ⟨.global, 0, 2, i⟩ = some (input 2 i))

def laneValue (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  ops.toHalf (ops.add (dotValue ops input t) (ops.fromHalf (input 2 (t%512))))

theorem source_lane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (base : State α)
    (ht : t < 32768) (hinputs : Inputs input base) :
    ∃ final, LarkPtxLinear.Steps ops LarkPtxLinear.Linear.layout LarkPtxLinear.Linear.geometry t
        LarkPtxLinear.Linear.program (LarkPtxLinear.Linear.start base) final ∧
      final.registers.stopped = true ∧ final.pc = 179 ∧
      final.registers.base.memory =
        (fun l => if l = outputCell t then some (laneValue ops input t) else base.memory l) := by
  obtain ⟨entry, first, ready⟩ := LarkPtxLinear.Linear.Init.prologue_ready ops t base ht
  have invariant := ready_loop ops input t base entry ready hinputs.1
  have loop := runChunks_execute ops input t 0 16 (ops.literal 0 1) entry ht (by decide) invariant
  have hmemory : (runChunks ops input t 0 16 (ops.literal 0 1) entry).registers.base.memory =
      base.memory := by rw [runChunks_memory, ready.frame.memory]
  have hbias : (runChunks ops input t 0 16 (ops.literal 0 1) entry).registers.base.memory (biasCell t) =
      some (input 2 (t%512)) := by
    rw [hmemory]
    exact hinputs.2 (t%512) (Nat.mod_lt _ (by decide))
  have finish := epilogue_execute ops input t (dotValue ops input t) (input 2 (t%512))
    (runChunks ops input t 0 16 (ops.literal 0 1) entry) ht loop.2 hbias
  refine ⟨exitReturned ops t (dotValue ops input t) (input 2 (t%512))
      (runChunks ops input t 0 16 (ops.literal 0 1) entry), ?_,
    exitReturned_stopped _ _ _ _ _, ?_, ?_⟩
  · exact LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ first
      (LarkPtxLinear.steps_trans _ _ _ _ _ _ _ _ loop.1 finish)
  · rw [exitReturned_pc, loop.2.pc]
    rfl
  · rw [exitReturned_memory, hmemory]
    rfl

theorem initial_inputs (input : Nat → Nat → α) (outside : Location → Option α) :
    Inputs input (initial LarkPtxLinear.Linear.layout input outside) := by
  refine ⟨initial_reads input outside, ?_⟩
  intro i hi
  simp [initial, LarkPtxLinear.Linear.layout, hi]

end LarkPtxLinear.Linear.Exit

#print axioms LarkPtxLinear.Linear.Exit.runTerms_memory
#print axioms LarkPtxLinear.Linear.Exit.bodyEnd_memory
#print axioms LarkPtxLinear.Linear.Exit.iteration_memory
#print axioms LarkPtxLinear.Linear.Exit.runChunks_memory
#print axioms LarkPtxLinear.Linear.Exit.bias_address
#print axioms LarkPtxLinear.Linear.Exit.output_address
#print axioms LarkPtxLinear.Linear.Exit.epilogue_execute
#print axioms LarkPtxLinear.Linear.Exit.exitReturned_memory
#print axioms LarkPtxLinear.Linear.Exit.exitReturned_stopped
#print axioms LarkPtxLinear.Linear.Exit.exitReturned_pc
#print axioms LarkPtxLinear.Linear.Exit.source_lane
#print axioms LarkPtxLinear.Linear.Exit.initial_inputs
