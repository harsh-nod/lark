import Lark.NativeSoftmaxNormBuffer

/-! Actual normalization store-component test, column index and validity guard.
Both sources use the same guard; only the instruction addresses differ. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of predicate_lt_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normStoreHead (guarded : Bool) (tid iteration component t : Nat) (s : State α) : State α :=
  advance (setIndex (advance s t (normPc guarded 106)) t 22 ((column tid iteration component : Nat) : Int) (normPc guarded 107))
    t (if column tid iteration component<50257 then normPc guarded 108 else normPc guarded 111)

theorem eval_norm_store_column (p : Shape) (t tid iteration component : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8)
    (h17 : s.indices t 17=some ((base tid iteration : Nat) : Int))
    (h21 : s.indices t 21=some (component : Int)) :
    evalIndex (geometry p) t s (.add (.ivar 17) (.mul (.ivar 21) (.const 1024)))=
      some ((column tid iteration component : Nat) : Int) := by
  have hm := eval_nat_mul (geometry p) t component 1024 s (.ivar 21) h21 (by decide) (by omega)
  have hb : base tid iteration+component*1024<2147483648 := by unfold base; omega
  simpa only [column_expansion] using eval_nat_sum (geometry p) t (base tid iteration) (component*1024) s
    (.ivar 17) (.mul (.ivar 21) (.const 1024)) h17 hm hb

theorem norm_store_head_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (tid iteration component t extra : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8)
    (hp : s.pc t=normPc guarded 105)
    (h17 : s.indices t 17=some ((base tid iteration : Nat) : Int)) (h21 : s.indices t 21=some (component : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+3) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (normStoreHead guarded tid iteration component t s) := by
  let col := column tid iteration component
  let s1 := advance s t (normPc guarded 106)
  let s2 := setIndex s1 t 22 (col : Int) (normPc guarded 107)
  have pred := predicate_lt_of (geometry p) t s (.ivar 21) (.const 8) (component : Int) 8 h21 rfl (by omega)
  have hn : normPc guarded 105+1=normPc guarded 106 := (norm_pc_next guarded 105).symm
  have e1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 21) (.const 8)) (normPc guarded 113)) s=some s1 := by
    simp [execute,pred,hp,hn,s1]
  have ix := eval_norm_store_column p t tid iteration component s1 ht hi hc h17 h21
  have e2 := execute_index_of ops (layout p) (geometry p) t 22 (normPc guarded 107)
    (.add (.ivar 17) (.mul (.ivar 21) (.const 1024))) s1 _ ix
    (by simp only [s1,advance,↓reduceIte]; exact (norm_pc_next guarded 106).symm)
  change execute _ _ _ _ _ s1=some s2 at e2
  have h22 : s2.indices t 22=some (col : Int) := by simp [s2,setIndex,advance]
  have hp2 : s2.pc t=normPc guarded 107 := by simp [s2,setIndex,advance]
  have e3 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 22) (.const 50257)) (normPc guarded 111)) s2=
      some (normStoreHead guarded tid iteration component t s) := by
    by_cases hcol : col<50257
    · have pred := predicate_lt_of (geometry p) t s2 (.ivar 22) (.const 50257) (col : Int) 50257 h22 rfl (by omega)
      have hn : normPc guarded 107+1=normPc guarded 108 := (norm_pc_next guarded 107).symm
      simp [execute,pred,hp2,hn,normStoreHead,show column tid iteration component<50257 from hcol,s2,s1,col]
    · have pred := predicate_nlt_of (geometry p) t s2 (.ivar 22) (.const 50257) (col : Int) 50257 h22 rfl (by omega)
      simp [execute,pred,hp2,normStoreHead,show ¬ column tid iteration component<50257 from hcol,s2,s1,col]
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p guarded ops t (normPc guarded 105) _ _ s s1 (norm_store_head_codes guarded).1 hp e1]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t (normPc guarded 106) _ _ s1 s2 (norm_store_head_codes guarded).2.1 (by simp [s1,advance]) e2]
  exact scalar_step p guarded ops t (normPc guarded 107) extra _ s2 _ (norm_store_head_codes guarded).2.2.1 hp2 e3

theorem norm_store_head_fields (guarded : Bool) (tid iteration component t : Nat) (s : State α) :
    (normStoreHead guarded tid iteration component t s).pc t=
      (if column tid iteration component<50257 then normPc guarded 108 else normPc guarded 111) ∧
    (normStoreHead guarded tid iteration component t s).indices t 22=some ((column tid iteration component : Nat) : Int) := by
  simp [normStoreHead,setIndex,advance]

theorem norm_store_head_frames (guarded : Bool) (tid iteration component t : Nat) (s : State α) :
    (normStoreHead guarded tid iteration component t s).memory=s.memory ∧
    (normStoreHead guarded tid iteration component t s).regs=s.regs ∧
    (normStoreHead guarded tid iteration component t s).epochs=s.epochs ∧
    (normStoreHead guarded tid iteration component t s).trace=s.trace := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem norm_store_head_index_other (guarded : Bool) (tid iteration component t r : Nat) (s : State α) (hr : r ≠ 22) :
    (normStoreHead guarded tid iteration component t s).indices t r=s.indices t r := by simp [normStoreHead,setIndex,advance,hr]

theorem norm_store_head_other (guarded : Bool) (tid iteration component t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (normStoreHead guarded tid iteration component t s) := by
  simp [OtherThread,normStoreHead,setIndex,advance,hu]

#print axioms eval_norm_store_column
#print axioms norm_store_head_eq
#print axioms norm_store_head_fields
#print axioms norm_store_head_frames
#print axioms norm_store_head_index_other
#print axioms norm_store_head_other
end LarkNativeSoftmax
