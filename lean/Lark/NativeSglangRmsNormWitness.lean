import Lark.NativeSglangRmsNormAddress

/-! Exact source-instruction witnesses for the unguarded shared partial store.
These execute from an explicit cut state, not from the source initializer.
Complete finite initialized traces are recorded separately by the Python study.
The guarded repair's two-lane instruction tail is also checked explicitly.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def partialCell : Location := ⟨.shared,0,0,0⟩
def cutState (value : α) : State α where
  pc := fun _ => 54
  indices := fun t q => if q = 3 then some 0 else if q = 2 then some (t % 32 : Nat) else none
  regs := fun _ q => if q = 0 then some value else none
  memory := fun _ => none
  epochs := fun _ => {}
  trace := []

def written (t pc : Nat) (value : α) (s : State α) : State α :=
  advance { record s t partialCell true with
    memory := fun l => if l = partialCell then some value else s.memory l } t pc

def originalPair (value : α) : State α :=
  written 1 55 value (written 0 55 value (cutState value))

def guardedPair (value : α) : State α :=
  advance (written 0 56 value (advance (cutState value) 0 55)) 1 56

theorem original_first_store (p : Shape) (ops : Ops α) (value : α) :
    execute ops (layout p) (geometry p) 0 (.store .shared 0 (.ivar 3) (.reg 0))
      (cutState value) = some (written 0 55 value (cutState value)) := by
  simp [execute,evalIndex,evalExpr,location,layout,geometry,cutState,written,
    partialCell,record,advance]

theorem original_second_store (p : Shape) (ops : Ops α) (value : α) :
    execute ops (layout p) (geometry p) 1 (.store .shared 0 (.ivar 3) (.reg 0))
      (written 0 55 value (cutState value)) = some (originalPair value) := by
  simp [execute,evalIndex,evalExpr,location,layout,geometry,cutState,written,
    originalPair,partialCell,record,advance]

theorem original_pair_exec (p : Shape) (ops : Ops α) (value : α) :
    ((execute ops (layout p) (geometry p) 0 (.store .shared 0 (.ivar 3) (.reg 0))
      (cutState value)).bind fun s =>
        execute ops (layout p) (geometry p) 1 (.store .shared 0 (.ivar 3) (.reg 0)) s) =
      some (originalPair value) := by
  rewrite [original_first_store]
  exact original_second_store p ops value

theorem original_pair_trace (value : α) :
    (originalPair value).trace = [⟨1,partialCell,true,{}⟩,⟨0,partialCell,true,{}⟩] := rfl

theorem original_pair_conflict (p : Shape) :
    conflict (geometry p) ⟨0,partialCell,true,{}⟩ ⟨1,partialCell,true,{}⟩ = true := by
  simp [conflict,ordered,geometry,sameLocation,partialCell]

theorem original_pair_racy (p : Shape) (value : α) :
    raceFree (geometry p) (originalPair value).trace = false := by
  simp [raceFree,original_pair_trace,conflict,ordered,geometry,sameLocation,partialCell]

theorem guarded_pair_exec (p : Shape) (ops : Ops α) (value : α) :
    ((execute ops (layout p) (geometry p) 0 (.branch (.eq (.ivar 2) (.const 0)) 56)
      (cutState value)).bind fun s =>
        (execute ops (layout p) (geometry p) 0 (.store .shared 0 (.ivar 3) (.reg 0)) s).bind fun s =>
          execute ops (layout p) (geometry p) 1 (.branch (.eq (.ivar 2) (.const 0)) 56) s) =
      some (guardedPair value) := by
  simp [execute,evalIndex,evalExpr,evalPredicate,int32,location,layout,geometry,
    cutState,written,guardedPair,partialCell,record,advance]

theorem guarded_pair_trace (value : α) :
    (guardedPair value).trace = [⟨0,partialCell,true,{}⟩] := rfl

theorem guarded_pair_race_free (p : Shape) (value : α) :
    raceFree (geometry p) (guardedPair value).trace = true := rfl

#print axioms original_first_store
#print axioms original_second_store
#print axioms original_pair_exec
#print axioms original_pair_trace
#print axioms original_pair_conflict
#print axioms original_pair_racy
#print axioms guarded_pair_exec
#print axioms guarded_pair_trace
#print axioms guarded_pair_race_free
end LarkNativeSglangRmsNorm
