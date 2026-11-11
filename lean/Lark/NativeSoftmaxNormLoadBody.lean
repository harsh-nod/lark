import Lark.NativeSoftmaxNormLoadHead

/-! Actual output read/fromHalf/private-bank1 store and counter/back-edge.
The value argument is the current output cell, so the original's unused clamped
reads do not assume that another lane has left its output unmodified. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem eval_norm_load_address (p : Shape) (t row col : Nat) (s : State α)
    (hr : row<p.rows) (hc : col<50257) (h0 : s.indices t 0=some (row : Int))
    (h19 : s.indices t 19=some (col : Int)) :
    evalIndex (geometry p) t s (.add (.mul (.ivar 0) (.const 50257)) (.ivar 19))=
      some ((address row col : Nat) : Int) := by
  have hb := p.bound
  have hm := eval_nat_mul (geometry p) t row 50257 s (.ivar 0) h0 (by decide) (by omega)
  exact eval_nat_sum (geometry p) t (row*50257) col s _ _ hm h19 (by omega)

def normLoadAddress (guarded : Bool) (row col t : Nat) (s : State α) : State α :=
  setIndex s t 20 ((address row col : Nat) : Int) (normPc guarded 101)

theorem norm_load_address_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (row col t extra : Nat) (s : State α) (hr : row<p.rows) (hc : col<50257)
    (h0 : s.indices t 0=some (row : Int)) (h19 : s.indices t 19=some (col : Int))
    (hp : s.pc t=normPc guarded 100) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+1) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (normLoadAddress guarded row col t s) := by
  have ix := eval_norm_load_address p t row col s hr hc h0 h19
  have e := execute_index_of ops (layout p) (geometry p) t 20 (normPc guarded 101)
    (.add (.mul (.ivar 0) (.const 50257)) (.ivar 19)) s _ ix
    ((congrArg (·+1) hp).trans (norm_pc_next guarded 100).symm)
  exact scalar_step p guarded ops t (normPc guarded 100) extra _ s _ (norm_load_body_codes guarded).1 hp e

theorem norm_output_read_location_of (l : Layout) (g : Geometry) (t offset size : Nat)
    (hl : l.global[0]?=some ⟨.output,size⟩) (hb : offset<size) :
    location l g t .global 0 (offset : Int) false=some (globalCell 0 offset) := by
  simp [location,hl,globalCell,hb]

theorem norm_converted_output_eval_of (ops : Ops α) (l : Layout) (g : Geometry)
    (t offset r : Nat) (value : α) (s : State α)
    (hl : location l g t .global 0 (offset : Int) false=some (globalCell 0 offset))
    (hi : s.indices t r=some (offset : Int)) (hm : s.memory (globalCell 0 offset)=some value) :
    evalExpr ops l g t (.un .fromHalf (.load .global 0 (.ivar r))) s=
      some (ops.fromHalf value,record s t (globalCell 0 offset) false) := by
  simp only [evalExpr,evalIndex,hi,hl,hm,applyUnary,bind,pure,Option.bind]

theorem norm_local_location (p : Shape) (t component : Nat) (hc : component<8) (write : Bool) :
    location (layout p) (geometry p) t .local 1 (component : Int) write=some (localCell 1 t component) := by
  simp [location,layout,localCell,show ¬ (component : Int)<0 by omega,hc]

def normLoadStored (guarded : Bool) (ops : Ops α) (row col component t : Nat) (value : α) (s : State α) : State α :=
  written t (normPc guarded 102) (localCell 1 t component) (ops.fromHalf value)
    (record s t (globalCell 0 (address row col)) false)

theorem norm_load_store_execute (p : Shape) (guarded : Bool) (ops : Ops α)
    (row col component t : Nat) (value : α) (s : State α) (hc : component<8)
    (hb : address row col<p.rows*50257) (hp : s.pc t=normPc guarded 101)
    (h18 : s.indices t 18=some (component : Int))
    (h20 : s.indices t 20=some ((address row col : Nat) : Int))
    (hm : s.memory (globalCell 0 (address row col))=some value) :
    execute ops (layout p) (geometry p) t
      (.store .local 1 (.ivar 18) (.un .fromHalf (.load .global 0 (.ivar 20)))) s=
      some (normLoadStored guarded ops row col component t value s) := by
  have load := norm_converted_output_eval_of ops (layout p) (geometry p) t (address row col) 20 value s
    (norm_output_read_location_of (layout p) (geometry p) t _ _ rfl hb) h20 hm
  exact execute_store_effect ops (layout p) (geometry p) t (normPc guarded 102) .local 1 (.ivar 18)
    (.un .fromHalf (.load .global 0 (.ivar 20))) s _ (component : Int) (localCell 1 t component) _
    h18 (norm_local_location p t component hc true) load
    ((congrArg (·+1) hp).trans (norm_pc_next guarded 101).symm)

theorem norm_load_store_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (row col component t extra : Nat) (value : α) (s : State α) (hc : component<8)
    (hb : address row col<p.rows*50257) (hp : s.pc t=normPc guarded 101)
    (h18 : s.indices t 18=some (component : Int))
    (h20 : s.indices t 20=some ((address row col : Nat) : Int))
    (hm : s.memory (globalCell 0 (address row col))=some value) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+1) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (normLoadStored guarded ops row col component t value s) :=
  scalar_step p guarded ops t (normPc guarded 101) extra _ s _ (norm_load_body_codes guarded).2.1 hp
    (norm_load_store_execute p guarded ops row col component t value s hc hb hp h18 h20 hm)

def normLoadAdvance (guarded : Bool) (t component : Nat) (s : State α) : State α :=
  advance (setIndex s t 18 ((component+1 : Nat) : Int) (normPc guarded 103)) t 97

theorem norm_load_advance_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (t component extra : Nat) (s : State α) (hc : component<8)
    (hp : s.pc t=normPc guarded 102) (hi : s.indices t 18=some (component : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (normLoadAdvance guarded t component s) := by
  let s1 := setIndex s t 18 ((component+1 : Nat) : Int) (normPc guarded 103)
  have ix := eval_nat_sum (geometry p) t component 1 s (.ivar 18) (.const 1) hi rfl (by omega)
  have e1 := execute_index_of ops (layout p) (geometry p) t 18 (normPc guarded 103)
    (.add (.ivar 18) (.const 1)) s _ ix ((congrArg (·+1) hp).trans (norm_pc_next guarded 102).symm)
  have e2 : execute ops (layout p) (geometry p) t (.jump 97) s1=some (normLoadAdvance guarded t component s) := rfl
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t (normPc guarded 102) _ _ s s1 (norm_load_body_codes guarded).2.2.1 hp e1]
  exact scalar_step p guarded ops t (normPc guarded 103) extra _ s1 _ (norm_load_body_codes guarded).2.2.2
    (by simp [s1,setIndex,advance]) e2

theorem norm_load_stored_fields (guarded : Bool) (ops : Ops α) (row col component t : Nat) (value : α) (s : State α) :
    (normLoadStored guarded ops row col component t value s).pc t=normPc guarded 102 ∧
    (normLoadStored guarded ops row col component t value s).indices=s.indices ∧
    (normLoadStored guarded ops row col component t value s).epochs=s.epochs ∧
    (normLoadStored guarded ops row col component t value s).regs=s.regs ∧
    (normLoadStored guarded ops row col component t value s).trace=
      ⟨t,localCell 1 t component,true,s.epochs t⟩::⟨t,globalCell 0 (address row col),false,s.epochs t⟩::s.trace := by
  simp [normLoadStored,written,record,advance]

theorem norm_load_stored_value (guarded : Bool) (ops : Ops α) (row col component t : Nat) (value : α) (s : State α) :
    (normLoadStored guarded ops row col component t value s).memory (localCell 1 t component)=some (ops.fromHalf value) := by
  simp [normLoadStored,written_memory,record]

theorem norm_load_stored_memory_other (guarded : Bool) (ops : Ops α) (row col component t : Nat) (value : α) (s : State α)
    (l : Location) (hl : l ≠ localCell 1 t component) :
    (normLoadStored guarded ops row col component t value s).memory l=s.memory l := by
  simp [normLoadStored,written_memory,record,hl]

theorem norm_load_stored_good (guarded : Bool) (ops : Ops α) (row col component t : Nat) (value : α) (s : State α)
    (hread : Good ⟨t,globalCell 0 (address row col),false,s.epochs t⟩) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normLoadStored guarded ops row col component t value s).trace, Good a := by
  intro a ha
  rewrite [(norm_load_stored_fields guarded ops row col component t value s).2.2.2.2] at ha
  rcases List.mem_cons.mp ha with h | h
  · subst a; exact Good.privateAccess rfl rfl
  · rcases List.mem_cons.mp h with h | h
    · subst a; exact hread
    · exact good a h

#print axioms eval_norm_load_address
#print axioms norm_load_address_eq
#print axioms norm_output_read_location_of
#print axioms norm_converted_output_eval_of
#print axioms norm_local_location
#print axioms norm_load_store_execute
#print axioms norm_load_store_eq
#print axioms norm_load_advance_eq
#print axioms norm_load_stored_fields
#print axioms norm_load_stored_value
#print axioms norm_load_stored_memory_other
#print axioms norm_load_stored_good
end LarkNativeSoftmax
