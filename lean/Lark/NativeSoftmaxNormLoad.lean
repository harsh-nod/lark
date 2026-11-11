import Lark.NativeSoftmaxNormLoadBody

/-! Complete actual normalization-buffer component for either source. Invalid
repaired components skip the read/store; original components sample the current
clamped output. Both paths return to PC97 under the original instruction fuel. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normSample (ops : Ops α) (row col : Nat) (s : State α) : α :=
  (s.memory (globalCell 0 (address row col))).getD (ops.literal 0 1)

theorem norm_sample_of_present (ops : Ops α) (row col : Nat) (s : State α)
    (hp : ∃ value, s.memory (globalCell 0 (address row col))=some value) :
    s.memory (globalCell 0 (address row col))=some (normSample ops row col s) := by
  obtain ⟨value,hv⟩ := hp
  simp only [normSample,hv,Option.getD_some]

theorem norm_selected_column_bound (guarded : Bool) (col : Nat) (hl : guarded=false ∨ col<50257) :
    normSelectedColumn guarded col<50257 := by
  cases guarded with
  | false => exact clamped_bound col
  | true => simpa [normSelectedColumn] using hl

theorem norm_choice_pc_of_load (guarded : Bool) (col : Nat) (hl : guarded=false ∨ col<50257) :
    normChoicePc guarded col=normPc guarded 100 := by
  cases guarded <;> simp_all [normChoicePc,normPc]

theorem norm_choice_pc_of_skip (guarded : Bool) (col : Nat) (hl : ¬ (guarded=false ∨ col<50257)) :
    normChoicePc guarded col=normPc guarded 102 := by
  cases guarded <;> simp_all [normChoicePc,normPc]

def normLoadCost (guarded : Bool) (col : Nat) : Nat :=
  4+normChoiceCost guarded col+if guarded=false ∨ col<50257 then 2 else 0

def normLoadState (guarded : Bool) (ops : Ops α) (row tid iteration component t : Nat) (s : State α) : State α :=
  let col := column tid iteration component
  let head := normLoadHead guarded tid iteration component t s
  let middle := if guarded=false ∨ col<50257 then
    normLoadStored guarded ops row (normSelectedColumn guarded col) component t
      (normSample ops row (normSelectedColumn guarded col) s)
      (normLoadAddress guarded row (normSelectedColumn guarded col) t head)
    else head
  normLoadAdvance guarded t component middle

theorem norm_load_component_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (row tid iteration component t extra : Nat) (s : State α)
    (hr : row<p.rows) (ht : tid<1024) (hi : iteration<7) (hc : component<8)
    (h0 : s.indices t 0=some (row : Int))
    (h17 : s.indices t 17=some ((base tid iteration : Nat) : Int))
    (h18 : s.indices t 18=some (component : Int)) (hp : s.pc t=97) (present : NormPresent row s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t
      (extra+normLoadCost guarded (column tid iteration component)) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (normLoadState guarded ops row tid iteration component t s) := by
  let col := column tid iteration component
  let head := normLoadHead guarded tid iteration component t s
  have hf := norm_load_head_fields guarded tid iteration component t s
  have h18h : head.indices t 18=some (component : Int) :=
    (norm_load_head_index_other guarded tid iteration component t 18 s (by decide)).trans h18
  by_cases hl : guarded=false ∨ col<50257
  · let selected := normSelectedColumn guarded col
    let value := normSample ops row selected s
    let addressed := normLoadAddress guarded row selected t head
    let stored := normLoadStored guarded ops row selected component t value addressed
    have hs : selected<50257 := norm_selected_column_bound guarded col hl
    have h0h : head.indices t 0=some (row : Int) :=
      (norm_load_head_index_other guarded tid iteration component t 0 s (by decide)).trans h0
    have hpc : head.pc t=normPc guarded 100 := hf.1.trans (norm_choice_pc_of_load guarded col hl)
    have h18a : addressed.indices t 18=some (component : Int) := by
      simpa only [addressed,normLoadAddress,setIndex,advance,↓reduceIte] using h18h
    have h20a : addressed.indices t 20=some ((address row selected : Nat) : Int) := by
      simp [addressed,normLoadAddress,setIndex,advance]
    have hpca : addressed.pc t=normPc guarded 101 := by simp [addressed,normLoadAddress,setIndex,advance]
    have hma : addressed.memory=s.memory := (norm_load_head_frames guarded tid iteration component t s).1
    have hm : addressed.memory (globalCell 0 (address row selected))=some value :=
      (congrFun hma _).trans (norm_sample_of_present ops row selected s (present selected hs))
    have hpcs : stored.pc t=normPc guarded 102 := (norm_load_stored_fields guarded ops row selected component t value addressed).1
    have h18s : stored.indices t 18=some (component : Int) :=
      (congrArg (fun ix => ix t 18) (norm_load_stored_fields guarded ops row selected component t value addressed).2.1).trans h18a
    rewrite [show extra+normLoadCost guarded (column tid iteration component)=
        (extra+4)+2+normChoiceCost guarded col by dsimp only [normLoadCost]; change _+(_+if guarded=false ∨ col<50257 then 2 else 0)=_; rewrite [if_pos hl]; dsimp only [col]; omega,
      norm_load_head_eq p guarded ops tid iteration component t (extra+4) s ht hi hc h17 h18 hp]
    have hrun : LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+4) head=
        LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (normLoadAdvance guarded t component stored) := by
      rewrite [show extra+4=(extra+3)+1 by omega,
        norm_load_address_eq p guarded ops row selected t (extra+3) head hr hs h0h hf.2 hpc]
      rewrite [show extra+3=(extra+2)+1 by omega,
        norm_load_store_eq p guarded ops row selected component t (extra+2) value addressed hc
          (address_bound p row selected hr hs) hpca h18a h20a hm]
      exact norm_load_advance_eq p guarded ops t component extra stored hc hpcs h18s
    simpa only [normLoadState,show column tid iteration component=col by rfl,if_pos hl] using hrun
  · have hpc : head.pc t=normPc guarded 102 := hf.1.trans (norm_choice_pc_of_skip guarded col hl)
    rewrite [show extra+normLoadCost guarded (column tid iteration component)=
        (extra+2)+2+normChoiceCost guarded col by dsimp only [normLoadCost]; change _+(_+if guarded=false ∨ col<50257 then 2 else 0)=_; rewrite [if_neg hl]; dsimp only [col]; omega,
      norm_load_head_eq p guarded ops tid iteration component t (extra+2) s ht hi hc h17 h18 hp]
    have hrun := norm_load_advance_eq p guarded ops t component extra head hc hpc h18h
    simpa only [normLoadState,show column tid iteration component=col by rfl,if_neg hl] using hrun

theorem norm_load_component_fields (guarded : Bool) (ops : Ops α)
    (row tid iteration component t : Nat) (s : State α) :
    (normLoadState guarded ops row tid iteration component t s).pc t=97 ∧
    (normLoadState guarded ops row tid iteration component t s).indices t 18=some ((component+1 : Nat) : Int) := by
  simp [normLoadState,normLoadAdvance,setIndex,advance]

theorem norm_load_component_epochs (guarded : Bool) (ops : Ops α)
    (row tid iteration component t : Nat) (s : State α) :
    (normLoadState guarded ops row tid iteration component t s).epochs=s.epochs := by
  by_cases hl : guarded=false ∨ column tid iteration component<50257 <;>
    simp [normLoadState,hl,normLoadAdvance,normLoadStored,normLoadAddress,written,record,setIndex,advance,
      (norm_load_head_frames guarded tid iteration component t s).2.2.1]

theorem norm_load_component_regs (guarded : Bool) (ops : Ops α)
    (row tid iteration component t : Nat) (s : State α) :
    (normLoadState guarded ops row tid iteration component t s).regs=s.regs := by
  by_cases hl : guarded=false ∨ column tid iteration component<50257 <;>
    simp [normLoadState,hl,normLoadAdvance,normLoadStored,normLoadAddress,written,record,setIndex,advance,
      (norm_load_head_frames guarded tid iteration component t s).2.2.2]

#print axioms norm_sample_of_present
#print axioms norm_selected_column_bound
#print axioms norm_choice_pc_of_load
#print axioms norm_choice_pc_of_skip
#print axioms norm_load_component_eq
#print axioms norm_load_component_fields
#print axioms norm_load_component_epochs
#print axioms norm_load_component_regs
end LarkNativeSoftmax
