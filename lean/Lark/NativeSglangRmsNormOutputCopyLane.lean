import Lark.NativeSglangRmsNormOutputCopyRound

/-! Successful actual scalar execution of the complete global-copy suffix,
from PC97 to halt109. All16 copied outputs and their32 accesses are retained.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] outputCopies

def copyStart (t : Nat) (s : State α) : State α := setIndex s t 19 0 98
def copiedLane (ops : Ops α) (input : Nat → Nat → α) (row tid t : Nat) (inverse : α) (s : State α) : State α :=
  advance (copyTwoRounds ops input row tid t inverse (copyStart t s)) t 109

theorem copy_start_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α)
    (h0 : s.indices t 0=some (row : Int)) (h1 : s.indices t 1=some (tid : Int))
    (cached : OutputPrefix ops input row tid 16 t inverse s) :
    CopyRoundReady ops input row tid 0 t inverse (copyStart t s) := by
  exact {
    pc := by simp [copyStart,setIndex,advance]
    rowIndex := by simpa [copyStart,setIndex,advance] using h0
    tidIndex := by simpa [copyStart,setIndex,advance] using h1
    iterationIndex := by simp [copyStart,setIndex,advance]
    cached := cached,completed := by intro k hk; omega }

theorem copied_lane_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t extra : Nat) (inverse : α) (s : State α) (hr : row<p.rows) (ht : tid<1024)
    (hp : s.pc t=97) (h0 : s.indices t 0=some (row : Int)) (h1 : s.indices t 1=some (tid : Int))
    (cached : OutputPrefix ops input row tid 16 t inverse s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+125) s=
      some (copiedLane ops input row tid t inverse s) := by
  let entry := copyStart t s
  let copied := copyTwoRounds ops input row tid t inverse entry
  have ready := copy_start_ready ops input row tid t inverse s h0 h1 cached
  have final := copy_two_ready ops input row tid t inverse entry ready
  have begin := execute_index_of ops (layout p) (geometry p) t 19 98 (.const 0) s 0 rfl (by omega)
  rw [scalar_step p true ops t 97 (extra+124) _ s entry (by decide) hp begin]
  rw [show extra+124=(extra+2)+122 by omega,copy_two_eq p ops input row tid t (extra+2) inverse entry hr ht ready]
  rw [copy_rounds_exit_eq p ops t (extra+1) copied final.pc final.iterationIndex]
  have parked : LarkCollective.parked (program true) (advance copied t 109) t=some .halt := by
    have code : (program true)[109]?=some (.scalar .halt) := by decide
    simp only [LarkCollective.parked,advance,↓reduceIte,code]
  rw [LarkCollective.runLane,parked]
  rfl

theorem copied_lane_prefix (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α)
    (h0 : s.indices t 0=some (row : Int)) (h1 : s.indices t 1=some (tid : Int))
    (cached : OutputPrefix ops input row tid 16 t inverse s) :
    GlobalPrefix ops input row tid 16 inverse (copiedLane ops input row tid t inverse s) :=
  (copy_two_ready ops input row tid t inverse (copyStart t s)
    (copy_start_ready ops input row tid t inverse s h0 h1 cached)).completed

theorem copied_lane_fields (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α)
    (h0 : s.indices t 0=some (row : Int)) (h1 : s.indices t 1=some (tid : Int))
    (cached : OutputPrefix ops input row tid 16 t inverse s) :
    (copiedLane ops input row tid t inverse s).pc t=109 ∧
    (copiedLane ops input row tid t inverse s).indices t 0=some (row : Int) ∧
    (copiedLane ops input row tid t inverse s).indices t 1=some (tid : Int) ∧
    OutputPrefix ops input row tid 16 t inverse (copiedLane ops input row tid t inverse s) := by
  have h := copy_two_ready ops input row tid t inverse (copyStart t s)
    (copy_start_ready ops input row tid t inverse s h0 h1 cached)
  exact ⟨by simp [copiedLane,advance],h.rowIndex,h.tidIndex,h.cached⟩

theorem copied_lane_memory_outside (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (l : Location) (hl : OutsideCopies row tid l) :
    (copiedLane ops input row tid t inverse s).memory l=s.memory l :=
  copy_two_memory_outside ops input row tid t inverse (copyStart t s) l hl

theorem copied_lane_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) :
    (copiedLane ops input row tid t inverse s).epochs=s.epochs :=
  copy_two_epochs ops input row tid t inverse (copyStart t s)

theorem copied_lane_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) :
    (copiedLane ops input row tid t inverse s).trace.length=s.trace.length+32 :=
  copy_two_trace_length ops input row tid t inverse (copyStart t s)

theorem copied_lane_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (ht : tid<1024) (he : t=row*1024+tid)
    (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(copiedLane ops input row tid t inverse s).trace,Good event :=
  copy_two_good ops input row tid t inverse (copyStart t s) ht he good

#print axioms copy_start_ready
#print axioms copied_lane_run
#print axioms copied_lane_prefix
#print axioms copied_lane_fields
#print axioms copied_lane_memory_outside
#print axioms copied_lane_epochs
#print axioms copied_lane_trace_length
#print axioms copied_lane_good
end LarkNativeSglangRmsNorm
