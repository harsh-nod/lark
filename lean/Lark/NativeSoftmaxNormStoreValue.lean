import Lark.NativeSoftmaxNormStoreHead

/-! The actual private-bank1 read for normalization. The scratch value already
contains fromHalf; the load into r13 introduces no further conversion. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normStoreValue (guarded : Bool) (value : α) (t component : Nat) (s : State α) : State α :=
  setReg (record s t (localCell 1 t component) false) t 13 value (normPc guarded 109)

theorem norm_local_value_eval_of (ops : Ops α) (l : Layout) (g : Geometry)
    (t component indexReg : Nat) (value : α) (s : State α)
    (hl : location l g t .local 1 (component : Int) false=some (localCell 1 t component))
    (hi : s.indices t indexReg=some (component : Int))
    (hm : s.memory (localCell 1 t component)=some value) :
    evalExpr ops l g t (.load .local 1 (.ivar indexReg)) s=
      some (value,record s t (localCell 1 t component) false) := by
  simp only [evalExpr,evalIndex,hi,hl,hm,bind,pure,Option.bind]

theorem norm_store_value_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (value : α) (t component extra : Nat) (s : State α) (hc : component<8)
    (hp : s.pc t=normPc guarded 108) (h21 : s.indices t 21=some (component : Int))
    (hm : s.memory (localCell 1 t component)=some value) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+1) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (normStoreValue guarded value t component s) := by
  have load := norm_local_value_eval_of ops (layout p) (geometry p) t component 21 value s
    (norm_local_location p t component hc false) h21 hm
  have hn : normPc guarded 108+1=normPc guarded 109 := (norm_pc_next guarded 108).symm
  have e : execute ops (layout p) (geometry p) t (.assign 13 (.load .local 1 (.ivar 21))) s=
      some (normStoreValue guarded value t component s) := by
    simp only [execute,load,hp,hn,bind,pure,Option.bind]
    rfl
  exact scalar_step p guarded ops t (normPc guarded 108) extra _ s _ (norm_store_head_codes guarded).2.2.2 hp e

theorem norm_store_value_fields (guarded : Bool) (value : α) (t component : Nat) (s : State α) :
    (normStoreValue guarded value t component s).pc t=normPc guarded 109 ∧
    (normStoreValue guarded value t component s).regs t 13=some value ∧
    (normStoreValue guarded value t component s).memory=s.memory ∧
    (normStoreValue guarded value t component s).indices=s.indices ∧
    (normStoreValue guarded value t component s).epochs=s.epochs ∧
    (normStoreValue guarded value t component s).trace=⟨t,localCell 1 t component,false,s.epochs t⟩::s.trace := by
  simp [normStoreValue,setReg,record,advance]

theorem norm_store_value_reg_other (guarded : Bool) (value : α) (t component r : Nat) (s : State α) (hr : r ≠ 13) :
    (normStoreValue guarded value t component s).regs t r=s.regs t r := by
  simp [normStoreValue,setReg,record,advance,hr]

theorem norm_store_value_other (guarded : Bool) (value : α) (t component u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (normStoreValue guarded value t component s) := by simp [OtherThread,normStoreValue,setReg,record,advance,hu]

theorem norm_store_value_good (guarded : Bool) (value : α) (t component : Nat) (s : State α)
    (good : ∀ a ∈ s.trace, Good a) : ∀ a ∈ (normStoreValue guarded value t component s).trace, Good a := by
  intro a ha
  rewrite [(norm_store_value_fields guarded value t component s).2.2.2.2.2] at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact Good.privateAccess rfl rfl
  · exact good a ha

#print axioms norm_local_value_eval_of
#print axioms norm_store_value_eq
#print axioms norm_store_value_fields
#print axioms norm_store_value_reg_other
#print axioms norm_store_value_other
#print axioms norm_store_value_good
end LarkNativeSoftmax
