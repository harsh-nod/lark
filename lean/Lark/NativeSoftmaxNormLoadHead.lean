import Lark.NativeSoftmaxNormChoice

/-! Actual normalization component test, column calculation and source-specific
load choice. The original clamp and repaired skip keep their distinct costs. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def normLoadHead (guarded : Bool) (tid iteration component t : Nat) (s : State α) : State α :=
  normChoice guarded t (column tid iteration component)
    (setIndex (advance s t 98) t 19 ((column tid iteration component : Nat) : Int) 99)

theorem eval_norm_load_column (p : Shape) (t tid iteration component : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8)
    (h17 : s.indices t 17=some ((base tid iteration : Nat) : Int))
    (h18 : s.indices t 18=some (component : Int)) :
    evalIndex (geometry p) t s (.add (.ivar 17) (.mul (.ivar 18) (.const 1024)))=
      some ((column tid iteration component : Nat) : Int) := by
  have hm := eval_nat_mul (geometry p) t component 1024 s (.ivar 18) h18 (by decide) (by omega)
  have hb : base tid iteration+component*1024<2147483648 := by unfold base; omega
  simpa only [column_expansion] using eval_nat_sum (geometry p) t (base tid iteration) (component*1024) s
    (.ivar 17) (.mul (.ivar 18) (.const 1024)) h17 hm hb

theorem norm_load_head_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (tid iteration component t extra : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8)
    (h17 : s.indices t 17=some ((base tid iteration : Nat) : Int))
    (h18 : s.indices t 18=some (component : Int)) (hp : s.pc t=97) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t
      (extra+2+normChoiceCost guarded (column tid iteration component)) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (normLoadHead guarded tid iteration component t s) := by
  let col := column tid iteration component
  let s1 := advance s t 98
  let s2 := setIndex s1 t 19 (col : Int) 99
  have pred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 18) (.const 8)
    (component : Int) 8 h18 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 18) (.const 8)) (normPc guarded 104)) s=some s1 := by
    simp [execute,pred,hp,s1]
  have ix := eval_norm_load_column p t tid iteration component s1 ht hi hc h17 h18
  have e2 := execute_index_of ops (layout p) (geometry p) t 19 99
    (.add (.ivar 17) (.mul (.ivar 18) (.const 1024))) s1 _ ix (by simp [s1,advance])
  change execute _ _ _ _ _ s1=some s2 at e2
  rewrite [show extra+2+normChoiceCost guarded (column tid iteration component)=
      ((extra+normChoiceCost guarded col)+1)+1 by dsimp only [col]; omega,
    scalar_step p guarded ops t 97 _ _ s s1 (norm_outer_codes guarded).2.2 hp e1]
  rewrite [scalar_step p guarded ops t 98 _ _ s1 s2 (norm_load_head_codes guarded).1 (by simp [s1,advance]) e2]
  exact norm_choice_eq p guarded ops t col extra s2 (by simp [s2,setIndex,advance]) (by simp [s2,setIndex,advance])

theorem norm_load_head_fields (guarded : Bool) (tid iteration component t : Nat) (s : State α) :
    (normLoadHead guarded tid iteration component t s).pc t=normChoicePc guarded (column tid iteration component) ∧
    (normLoadHead guarded tid iteration component t s).indices t 19=
      some ((normSelectedColumn guarded (column tid iteration component) : Nat) : Int) :=
  norm_choice_fields guarded t (column tid iteration component) _ (by simp [setIndex,advance])

theorem norm_load_head_index_other (guarded : Bool) (tid iteration component t r : Nat) (s : State α) (hr : r ≠ 19) :
    (normLoadHead guarded tid iteration component t s).indices t r=s.indices t r := by
  exact (norm_choice_index_other guarded t (column tid iteration component) r _ hr).trans
    (by simp [setIndex,advance,hr])

theorem norm_load_head_frames (guarded : Bool) (tid iteration component t : Nat) (s : State α) :
    (normLoadHead guarded tid iteration component t s).memory=s.memory ∧
    (normLoadHead guarded tid iteration component t s).trace=s.trace ∧
    (normLoadHead guarded tid iteration component t s).epochs=s.epochs ∧
    (normLoadHead guarded tid iteration component t s).regs=s.regs :=
  norm_choice_frames guarded t (column tid iteration component) _

theorem norm_load_head_other (guarded : Bool) (tid iteration component t u : Nat) (s : State α) (hu : u ≠ t) :
    OtherThread t u s (normLoadHead guarded tid iteration component t s) := by
  cases guarded <;> simp [OtherThread,normLoadHead,normChoice,normOriginalClampedState,setIndex,advance,hu]
  split <;> simp [setIndex,advance,hu]

#print axioms eval_norm_load_column
#print axioms norm_load_head_eq
#print axioms norm_load_head_fields
#print axioms norm_load_head_index_other
#print axioms norm_load_head_frames
#print axioms norm_load_head_other
end LarkNativeSoftmax
