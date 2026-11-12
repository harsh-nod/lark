import Lark.NativeAwqGemmFragmentLoad

/-! Source-order execution of each unrolled four-half operand load group.
The same induction covers A and B without replacing their source programs. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def operandBase (p : Shape) (half bank : Nat) (left : Bool) : Nat :=
  if left then leftBase p half else rightBase p half bank
def operandStart (p : Shape) (half bank : Nat) (left : Bool) : Nat :=
  if left then passPC p half else passPC p half+4+5*bank
def operandCell (p : Shape) (t half bank : Nat) (left : Bool) (e : Nat) : Location :=
  if left then sharedCell t 0 (aFragment (laneId t) half e) else sharedCell t 1 (bFragment p (laneId t) half bank e)
def operandValue (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t half bank : Nat) (left : Bool) (e : Nat) : α :=
  if left then aOperand p ops input tile t half e else bOperand p input tile t half bank e
def operandLoaded (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank : Nat) (left : Bool) (e : Nat) (s : State α) : State α :=
  fragmentLoaded t (operandBase p half bank left+e) (operandStart p half bank left+e+1)
    (operandCell p t half bank left e) (operandValue p ops input tile t half bank left e) s

theorem operand_load_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t half bank e extra : Nat) (left : Bool) (s : State α)
    (hb : blockId t=b) (hh : half<2) (hbank : bank<banks p) (he : e<4)
    (hi : s.indices t 0=some ((laneId t : Nat) : Int)) (reads : TileReads p ops input tile b s)
    (hp : s.pc t=operandStart p half bank left+e) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (operandLoaded p ops input tile t half bank left e s) := by
  cases left with
  | false => exact b_fragment_load_run p ops input tile b t half bank e extra s hb hh hbank he hi reads hp
  | true => exact a_fragment_load_run p ops input tile b t half e extra s hb hh he hi reads hp

def operandLoop (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank : Nat) (left : Bool) : Nat → Nat → State α → State α
  | _,0,s => s
  | e,n+1,s => operandLoop p ops input tile t half bank left (e+1) n (operandLoaded p ops input tile t half bank left e s)

theorem operand_loop_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank e n : Nat) (left : Bool) (s : State α) :
    (operandLoop p ops input tile t half bank left e n s).memory=s.memory ∧
      (operandLoop p ops input tile t half bank left e n s).indices=s.indices ∧
        (operandLoop p ops input tile t half bank left e n s).epochs=s.epochs := by
  induction n generalizing e s with
  | zero => exact ⟨rfl,rfl,rfl⟩
  | succ n ih => exact ih (e+1) (operandLoaded p ops input tile t half bank left e s)

theorem operand_loop_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank e n : Nat) (left : Bool) (s : State α) (hp : s.pc t=operandStart p half bank left+e) :
    (operandLoop p ops input tile t half bank left e n s).pc t=operandStart p half bank left+(e+n) := by
  induction n generalizing e s with
  | zero => exact hp
  | succ n ih =>
    have next := ih (e+1) (operandLoaded p ops input tile t half bank left e s)
      (by simp [operandLoaded,fragment_loaded_pc,Nat.add_assoc])
    simpa only [operandLoop,show e+1+n=e+(n+1) by omega] using next

theorem operand_loop_other_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t u half bank e n : Nat) (left : Bool) (s : State α) (hu : u≠t) :
    (operandLoop p ops input tile t half bank left e n s).pc u=s.pc u := by
  induction n generalizing e s with
  | zero => rfl
  | succ n ih =>
    rw [operandLoop,ih]
    simp [operandLoaded,fragment_loaded_pc,hu]

theorem operand_loop_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t half bank e n extra : Nat) (left : Bool) (s : State α)
    (hb : blockId t=b) (hh : half<2) (hbank : bank<banks p) (hn : e+n≤4)
    (hi : s.indices t 0=some ((laneId t : Nat) : Int)) (reads : TileReads p ops input tile b s)
    (hp : s.pc t=operandStart p half bank left+e) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+n) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (operandLoop p ops input tile t half bank left e n s) := by
  induction n generalizing e extra s with
  | zero => rfl
  | succ n ih =>
    rewrite [show extra+(n+1)=(extra+n)+1 by omega,
      operand_load_eq p ops input tile b t half bank e (extra+n) left s hb hh hbank (by omega) hi reads hp]
    exact ih (e+1) extra (operandLoaded p ops input tile t half bank left e s) (by omega) hi
      (tile_reads_of_memory p ops input tile b s _ reads rfl)
      (by simp [operandLoaded,fragment_loaded_pc,Nat.add_assoc])

theorem operand_loop_reg_outside (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t u half bank e n r : Nat) (left : Bool) (s : State α)
    (hr : ∀ q, e≤q → q<e+n → ¬(u=t ∧ r=operandBase p half bank left+q)) :
    (operandLoop p ops input tile t half bank left e n s).regs u r=s.regs u r := by
  induction n generalizing e s with
  | zero => rfl
  | succ n ih =>
    rw [operandLoop,ih (e+1) (operandLoaded p ops input tile t half bank left e s)
      (by intro q hlo hhi; exact hr q (by omega) (by omega))]
    simp only [operandLoaded,fragment_loaded_regs,if_neg (hr e (by omega) (by omega))]

theorem operand_loop_reg_written (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank e n q : Nat) (left : Bool) (s : State α) (hlo : e≤q) (hhi : q<e+n) :
    (operandLoop p ops input tile t half bank left e n s).regs t (operandBase p half bank left+q)=
      some (operandValue p ops input tile t half bank left q) := by
  induction n generalizing e s with
  | zero => omega
  | succ n ih =>
    rw [operandLoop]
    by_cases same : q=e
    · subst q
      rw [operand_loop_reg_outside p ops input tile t t half bank (e+1) n (operandBase p half bank left+e)
        left (operandLoaded p ops input tile t half bank left e s) (by intro q hlo hhi; omega)]
      simp [operandLoaded,fragment_loaded_regs]
    · exact ih (e+1) (operandLoaded p ops input tile t half bank left e s) (by omega) (by omega)

theorem operand_loop_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile t half bank e n : Nat) (left : Bool) (s : State α) :
    (operandLoop p ops input tile t half bank left e n s).trace.length=s.trace.length+n := by
  induction n generalizing e s with
  | zero => rfl
  | succ n ih =>
    rw [operandLoop,ih]
    simp only [operandLoaded,fragment_loaded_trace,List.length_cons]
    omega

#print axioms operand_load_eq
#print axioms operand_loop_frames
#print axioms operand_loop_pc
#print axioms operand_loop_other_pc
#print axioms operand_loop_eq
#print axioms operand_loop_reg_outside
#print axioms operand_loop_reg_written
#print axioms operand_loop_trace_length
end LarkNativeAwqGemm
