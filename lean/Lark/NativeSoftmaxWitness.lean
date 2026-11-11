import Lark.NativeSoftmaxFootprint

/-! Instruction-level trace counterexample for the full source, for arbitrary
scalar operations and values. These are explicit intermediate states; reaching
them from the whole source initializer remains a separate proof obligation.
-/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def reader : Access := ⟨0,globalCell 0 50256,false,⟨0,4,0⟩⟩
def writerAccess : Access := ⟨80,globalCell 0 50256,true,⟨0,4,0⟩⟩

def sourceScalarStep (p : Shape) (guarded : Bool) (ops : Ops α) (t : Nat) (s : State α) :
    Option (State α) := do
  match ← (program guarded)[s.pc t]? with
  | .scalar i => execute ops (layout p) (geometry p) t i s
  | .shuffle .. => none

def readerStart (offset component : Nat) (x : α) : State α where
  pc := fun _ => 102
  indices := fun _ r => if r = 18 then some (component : Int) else if r = 20 then some (offset : Int) else none
  regs := fun _ _ => none
  memory := fun l => if l = globalCell 0 offset then some x else none
  epochs := fun _ => ⟨0,4,0⟩
  trace := []

def writerStart (offset : Nat) (value denominator : α) : State α where
  pc := fun _ => 111
  indices := fun _ r => if r = 23 then some (offset : Int) else none
  regs := fun _ r => if r = 13 then some value else if r = 12 then some denominator else none
  memory := fun _ => none
  epochs := fun _ => ⟨0,4,0⟩
  trace := []

def guardStart : State Unit where
  pc := fun _ => 99
  indices := fun _ r => if r = 19 then some 51200 else none
  regs := fun _ _ => none
  memory := fun _ => none
  epochs := fun _ => ⟨0,4,0⟩
  trace := []

def unitOps : Ops Unit :=
  ⟨fun _ _ => (),fun _ _ => (),fun _ _ => (),fun _ _ => (),fun _ _ => (),fun _ _ => (),
    fun _ => (),fun _ => (),fun _ => (),fun _ => (),fun _ => ()⟩

def readInstruction : Instr :=
  .store .local 1 (.ivar 18) (.un .fromHalf (.load .global 0 (.ivar 20)))
def writeInstruction : Instr :=
  .store .global 0 (.ivar 23) (.un .toHalf (.bin .div (.reg 13) (.reg 12)))
def guardInstruction : Instr := .branch (.lt (.ivar 19) (.const 50257)) 102

theorem reader_code : racyProgram[102]? = some (.scalar readInstruction) := by decide
theorem writer_code : racyProgram[111]? = some (.scalar writeInstruction) := by decide
theorem guard_code : fixedProgram[99]? = some (.scalar guardInstruction) := by decide

theorem scalar_at (p : Shape) (guarded : Bool) (ops : Ops α) (t pc : Nat) (s : State α)
    (i : Instr) (hp : s.pc t = pc) (hc : (program guarded)[pc]? = some (.scalar i)) :
    sourceScalarStep p guarded ops t s = execute ops (layout p) (geometry p) t i s := by
  simp only [sourceScalarStep,hp,hc,bind,Option.some_bind]

theorem output_location_of (l : Layout) (g : Geometry) (t buffer offset size : Nat) (write : Bool)
    (hl : l.global[buffer]? = some ⟨.output,size⟩) (hb : offset < size) :
    location l g t .global buffer (offset : Int) write = some (globalCell buffer offset) := by
  cases write <;> simp [location,hl,globalCell,hb,
    show (Role.output == Role.input) = false from rfl]

theorem witness_output_location (p : Shape) (t offset : Nat) (write : Bool)
    (hb : offset < p.rows * 50257) :
    location (layout p) (geometry p) t .global 0 (offset : Int) write = some (globalCell 0 offset) :=
  output_location_of (layout p) (geometry p) t 0 offset (p.rows * 50257) write rfl hb

theorem witness_private_location (p : Shape) (component : Nat) (hc : component < 8) :
    location (layout p) (geometry p) 0 .local 1 (component : Int) true = some ⟨.local,0,1,component⟩ := by
  simp [location,layout,hc]

theorem store_trace_of (ops : Ops α) (l : Layout) (g : Geometry) (t buffer : Nat)
    (space : Space) (ix : Index) (e : Expr) (s afterRead : State α) (offset : Int) (loc : Location) (value : α)
    (hi : evalIndex g t s ix = some offset) (hl : location l g t space buffer offset true = some loc)
    (he : evalExpr ops l g t e s = some (value,afterRead)) :
    (execute ops l g t (.store space buffer ix e) s).map State.trace =
      some (⟨t,loc,true,afterRead.epochs t⟩ :: afterRead.trace) := by
  simp [execute,hi,hl,he,record,advance]

theorem half_load_of (ops : Ops α) (l : Layout) (g : Geometry) (t buffer : Nat)
    (ix : Index) (s : State α) (offset : Int) (loc : Location) (value : α)
    (hi : evalIndex g t s ix = some offset) (hl : location l g t .global buffer offset false = some loc)
    (hm : s.memory loc = some value) :
    evalExpr ops l g t (.un .fromHalf (.load .global buffer ix)) s =
      some (ops.fromHalf value,record s t loc false) := by
  simp [evalExpr,hi,hl,hm,applyUnary]

theorem reader_step_at (p : Shape) (ops : Ops α) (offset component : Nat) (x : α)
    (hb : offset < p.rows * 50257) (hc : component < 8) :
    (sourceScalarStep p false ops 0 (readerStart offset component x)).map State.trace =
      some [⟨0,⟨.local,0,1,component⟩,true,⟨0,4,0⟩⟩,⟨0,globalCell 0 offset,false,⟨0,4,0⟩⟩] := by
  rewrite [scalar_at p false ops 0 102 (readerStart offset component x) readInstruction rfl reader_code]
  have he := half_load_of ops (layout p) (geometry p) 0 0 (.ivar 20)
    (readerStart offset component x) (offset : Int) (globalCell 0 offset) x
    (by simp [evalIndex,readerStart]) (witness_output_location p 0 offset false hb)
    (by simp [readerStart])
  have h := store_trace_of ops (layout p) (geometry p) 0 1 .local (.ivar 18)
    (.un .fromHalf (.load .global 0 (.ivar 20))) (readerStart offset component x)
    (record (readerStart offset component x) 0 (globalCell 0 offset) false) (component : Int)
    ⟨.local,0,1,component⟩ (ops.fromHalf x)
    (by simp [evalIndex,readerStart]) (witness_private_location p component hc) he
  exact h

theorem writer_step_at (p : Shape) (ops : Ops α) (offset : Nat) (value denominator : α)
    (hb : offset < p.rows * 50257) :
    (sourceScalarStep p false ops 80 (writerStart offset value denominator)).map State.trace =
      some [⟨80,globalCell 0 offset,true,⟨0,4,0⟩⟩] := by
  rewrite [scalar_at p false ops 80 111 (writerStart offset value denominator) writeInstruction rfl writer_code]
  have he : evalExpr ops (layout p) (geometry p) 80
      (.un .toHalf (.bin .div (.reg 13) (.reg 12))) (writerStart offset value denominator) =
      some (ops.toHalf (ops.div value denominator),writerStart offset value denominator) := by
    simp [evalExpr,writerStart,applyUnary,applyBinary]
  exact store_trace_of ops (layout p) (geometry p) 80 0 .global (.ivar 23)
    (.un .toHalf (.bin .div (.reg 13) (.reg 12))) (writerStart offset value denominator)
    (writerStart offset value denominator) (offset : Int) (globalCell 0 offset)
    (ops.toHalf (ops.div value denominator))
    (by simp [evalIndex,writerStart]) (witness_output_location p 80 offset true hb) he

theorem reader_step (p : Shape) (ops : Ops α) (x : α) :
    (sourceScalarStep p false ops 0 (readerStart 50256 2 x)).map State.trace =
      some [⟨0,⟨.local,0,1,2⟩,true,⟨0,4,0⟩⟩,reader] := by
  exact reader_step_at p ops 50256 2 x (by have h := p.positive; omega) (by decide)

theorem writer_step (p : Shape) (ops : Ops α) (value denominator : α) :
    (sourceScalarStep p false ops 80 (writerStart 50256 value denominator)).map State.trace =
      some [writerAccess] := by
  exact writer_step_at p ops 50256 value denominator (by have h := p.positive; omega)

theorem guard_step (p : Shape) :
    (sourceScalarStep p true unitOps 0 guardStart).map (fun s => (s.pc 0,s.trace)) = some (102,[]) := by
  rewrite [scalar_at p true unitOps 0 99 guardStart guardInstruction rfl guard_code]
  simp [guardInstruction,execute,guardStart,evalPredicate,evalIndex,int32,advance]

theorem pair_conflict (p : Shape) : conflict (geometry p) reader writerAccess = true := by
  simp [conflict,ordered,geometry,reader,writerAccess,globalCell,sameLocation]

theorem pair_invalidates_rf (p : Shape) (trace : List Access)
    (hr : reader ∈ trace) (hw : writerAccess ∈ trace) : raceFree (geometry p) trace = false := by
  cases h : raceFree (geometry p) trace with
  | false => rfl
  | true =>
      have hn := (List.all_eq_true.mp ((List.all_eq_true.mp h) reader hr)) writerAccess hw
      simp [pair_conflict p] at hn

#print axioms reader_code
#print axioms writer_code
#print axioms guard_code
#print axioms scalar_at
#print axioms output_location_of
#print axioms witness_output_location
#print axioms witness_private_location
#print axioms store_trace_of
#print axioms half_load_of
#print axioms reader_step_at
#print axioms writer_step_at
#print axioms reader_step
#print axioms writer_step
#print axioms guard_step
#print axioms pair_conflict
#print axioms pair_invalidates_rf
end LarkNativeSoftmax
