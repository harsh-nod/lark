import Lark.NativeSoftmaxExpBuffer

/-! Actual component and column tests of the exponential output loop. The
column test preserves the source's skip target, so an invalid component can
reach the common increment without reading private data or writing output. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of predicate_lt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expStoreHead (tid iteration component t : Nat) (s : State α) : State α :=
  let col := column tid iteration component
  let s := advance s t 58
  let s := setIndex s t 14 (col : Int) 59
  advance s t (if col<50257 then 60 else 65)

theorem eval_exp_store_column (p : Shape) (t tid iteration component : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8)
    (h9 : s.indices t 9=some ((base tid iteration : Nat) : Int))
    (h13 : s.indices t 13=some (component : Int)) :
    evalIndex (geometry p) t s (.add (.ivar 9) (.mul (.ivar 13) (.const 1024))) =
      some ((column tid iteration component : Nat) : Int) := by
  have hm := eval_nat_mul (geometry p) t component 1024 s (.ivar 13) h13 (by decide) (by omega)
  have hb : base tid iteration+component*1024<2147483648 := by unfold base; omega
  simpa only [column_expansion] using
    eval_nat_sum (geometry p) t (base tid iteration) (component*1024) s
      (.ivar 9) (.mul (.ivar 13) (.const 1024)) h9 hm hb

theorem exp_store_head_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (tid iteration component t extra : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8) (hp : s.pc t=57)
    (h9 : s.indices t 9=some ((base tid iteration : Nat) : Int))
    (h13 : s.indices t 13=some (component : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expStoreHead tid iteration component t s) := by
  let col := column tid iteration component
  let s1 := advance s t 58
  let s2 := setIndex s1 t 14 (col : Int) 59
  have pred := predicate_lt_of (geometry p) t s (.ivar 13) (.const 8) (component : Int) 8 h13 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 13) (.const 8)) 67) s=some s1 := by
    simp [execute,pred,hp,s1]
  have ix := eval_exp_store_column p t tid iteration component s1 ht hi hc h9 h13
  have e2 := execute_index_of ops (layout p) (geometry p) t 14 59
    (.add (.ivar 9) (.mul (.ivar 13) (.const 1024))) s1 _ ix (by simp [s1,advance])
  change execute _ _ _ _ _ s1=some s2 at e2
  have h14 : s2.indices t 14=some (col : Int) := by simp [s2,setIndex,advance]
  have pred2 : evalPredicate (geometry p) t s2 (.lt (.ivar 14) (.const 50257))=some (decide (col<50257)) := by
    simp [evalPredicate,evalIndex,h14,int32]
    omega
  have e3 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 14) (.const 50257)) 65) s2=
      some (expStoreHead tid iteration component t s) := by
    simp only [execute,pred2,bind,pure,Option.bind,decide_eq_true_eq]
    have hpc : s2.pc t+1=60 := by simp [s2,setIndex,advance]
    rewrite [hpc]
    rfl
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p guarded ops t 57 _ _ s s1 (by cases guarded <;> rfl) hp e1]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 58 _ _ s1 s2 (by cases guarded <;> rfl) (by simp [s1,advance]) e2]
  exact scalar_step p guarded ops t 59 extra _ s2 _ (by cases guarded <;> rfl)
    (by simp [s2,setIndex,advance]) e3

theorem exp_store_head_fields (tid iteration component t : Nat) (s : State α) :
    (expStoreHead tid iteration component t s).pc t=(if column tid iteration component<50257 then 60 else 65) ∧
    (expStoreHead tid iteration component t s).indices t 14=some ((column tid iteration component : Nat) : Int) ∧
    (expStoreHead tid iteration component t s).memory=s.memory ∧
    (expStoreHead tid iteration component t s).regs=s.regs ∧
    (expStoreHead tid iteration component t s).epochs=s.epochs ∧
    (expStoreHead tid iteration component t s).trace=s.trace := by
  simp [expStoreHead,setIndex,advance]

theorem exp_store_head_index_other (tid iteration component t r : Nat) (s : State α) (hr : r ≠ 14) :
    (expStoreHead tid iteration component t s).indices t r=s.indices t r := by
  simp [expStoreHead,setIndex,advance,hr]

def expStoreNext (t component : Nat) (s : State α) : State α :=
  advance (setIndex s t 13 ((component+1 : Nat) : Int) 66) t 57

theorem exp_store_next_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (t component extra : Nat) (s : State α) (hc : component<8)
    (hp : s.pc t=65) (h13 : s.indices t 13=some (component : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (expStoreNext t component s) := by
  let next := setIndex s t 13 ((component+1 : Nat) : Int) 66
  have ix := eval_nat_sum (geometry p) t component 1 s (.ivar 13) (.const 1) h13 rfl (by omega)
  have e1 := execute_index_of ops (layout p) (geometry p) t 13 66 (.add (.ivar 13) (.const 1)) s _ ix (by omega)
  change execute _ _ _ _ _ s=some next at e1
  have e2 : execute ops (layout p) (geometry p) t (.jump 57) next=some (expStoreNext t component s) := rfl
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 65 _ _ s next (by cases guarded <;> rfl) hp e1]
  exact scalar_step p guarded ops t 66 extra _ next _ (by cases guarded <;> rfl)
    (by simp [next,setIndex,advance]) e2

theorem exp_store_next_fields (t component : Nat) (s : State α) :
    (expStoreNext t component s).pc t=57 ∧
    (expStoreNext t component s).indices t 13=some ((component+1 : Nat) : Int) ∧
    (expStoreNext t component s).memory=s.memory ∧ (expStoreNext t component s).regs=s.regs ∧
    (expStoreNext t component s).epochs=s.epochs ∧ (expStoreNext t component s).trace=s.trace := by
  simp [expStoreNext,setIndex,advance]

theorem exp_store_next_index_other (t component r : Nat) (s : State α) (hr : r ≠ 13) :
    (expStoreNext t component s).indices t r=s.indices t r := by simp [expStoreNext,setIndex,advance,hr]

#print axioms eval_exp_store_column
#print axioms exp_store_head_eq
#print axioms exp_store_head_fields
#print axioms exp_store_head_index_other
#print axioms exp_store_next_eq
#print axioms exp_store_next_fields
#print axioms exp_store_next_index_other
end LarkNativeSoftmax
