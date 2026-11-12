import Lark.NativeSglangRmsNormOutputCopyLoop

/-! Both actual outer global-copy rounds, with the component false exit and
the final outer false exit to halt. The private converted halves survive.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex execute_index_of predicate_lt_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] outputCopies

def copyRoundBegin (t : Nat) (s : State α) : State α := setIndex (advance s t 99) t 20 0 100
def copyRoundEnd (iteration t : Nat) (s : State α) : State α :=
  advance (setIndex (advance s t 107) t 19 ((iteration+1 : Nat) : Int) 108) t 98
def copyRoundAfter (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) : State α :=
  copyRoundEnd iteration t (outputCopies ops input row tid iteration t inverse 0 8 (copyRoundBegin t s))

theorem copy_round_begin_eq (p : Shape) (ops : Ops α) (iteration t extra : Nat) (s : State α)
    (hi : iteration<2) (hp : s.pc t=98) (h19 : s.indices t 19=some (iteration : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+2) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (copyRoundBegin t s) := by
  have pred := predicate_lt_of (geometry p) t s (.ivar 19) (.const 2) (iteration : Int) 2 h19 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 19) (.const 2)) 109) s=
      some (advance s t 99) := by simp [execute,pred,hp]
  have e2 := execute_index_of ops (layout p) (geometry p) t 20 100 (.const 0) (advance s t 99) 0 rfl (by simp [advance])
  rw [scalar_step p true ops t 98 (extra+1) _ s _ (by decide) hp e1]
  exact scalar_step p true ops t 99 extra _ _ _ (by decide) (by simp [advance]) e2

theorem copy_round_end_eq (p : Shape) (ops : Ops α) (iteration t extra : Nat) (s : State α)
    (hi : iteration<2) (hp : s.pc t=100) (h19 : s.indices t 19=some (iteration : Int))
    (h20 : s.indices t 20=some 8) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+3) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (copyRoundEnd iteration t s) := by
  let s1 := advance s t 107
  let s2 := setIndex s1 t 19 ((iteration+1 : Nat) : Int) 108
  have pred := predicate_nlt_of (geometry p) t s (.ivar 20) (.const 8) 8 8 h20 rfl (by decide)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 20) (.const 8)) 107) s=some s1 := by
    simp [execute,pred,s1]
  have plus := eval_nat_sum (geometry p) t iteration 1 s1 (.ivar 19) (.const 1) h19 rfl (by omega)
  have e2 := execute_index_of ops (layout p) (geometry p) t 19 108 (.add (.ivar 19) (.const 1)) s1 _ plus (by simp [s1,advance])
  have e3 : execute ops (layout p) (geometry p) t (.jump 98) s2=some (copyRoundEnd iteration t s) := rfl
  rw [scalar_step p true ops t 100 (extra+2) _ s s1 (by decide) hp e1]
  rw [scalar_step p true ops t 107 (extra+1) _ s1 s2 (by decide) (by simp [s1,advance]) e2]
  exact scalar_step p true ops t 108 extra _ s2 _ (by decide) (by simp [s2,setIndex,advance]) e3

theorem copy_rounds_exit_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hp : s.pc t=98) (h19 : s.indices t 19=some 2) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+1) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (advance s t 109) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 19) (.const 2) 2 2 h19 rfl (by decide)
  have e : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 19) (.const 2)) 109) s=
      some (advance s t 109) := by simp [execute,pred]
  exact scalar_step p true ops t 98 extra _ s _ (by decide) hp e

structure CopyRoundReady (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) : Prop where
  pc : s.pc t=98
  rowIndex : s.indices t 0=some (row : Int)
  tidIndex : s.indices t 1=some (tid : Int)
  iterationIndex : s.indices t 19=some (iteration : Int)
  cached : OutputPrefix ops input row tid 16 t inverse s
  completed : GlobalPrefix ops input row tid (iteration*8) inverse s

theorem copy_round_begin_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α)
    (ready : CopyRoundReady ops input row tid iteration t inverse s) :
    CopyReady ops input row tid iteration 0 t inverse (copyRoundBegin t s) := by
  exact {
    pc := by simp [copyRoundBegin,setIndex,advance]
    rowIndex := by simpa [copyRoundBegin,setIndex,advance] using ready.rowIndex
    tidIndex := by simpa [copyRoundBegin,setIndex,advance] using ready.tidIndex
    iterationIndex := by simpa [copyRoundBegin,setIndex,advance] using ready.iterationIndex
    componentIndex := by simp [copyRoundBegin,setIndex,advance]
    cached := ready.cached,completed := by simpa only [Nat.add_zero] using ready.completed }

theorem copy_round_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) (hi : iteration<2)
    (ready : CopyRoundReady ops input row tid iteration t inverse s) :
    CopyRoundReady ops input row tid (iteration+1) t inverse
      (copyRoundAfter ops input row tid iteration t inverse s) := by
  have r8 := output_copies_ready ops input row tid iteration t 0 8 inverse (copyRoundBegin t s) hi
    (by decide) (copy_round_begin_ready ops input row tid iteration t inverse s ready)
  exact {
    pc := by simp [copyRoundAfter,copyRoundEnd,setIndex,advance]
    rowIndex := by simpa [copyRoundAfter,copyRoundEnd,setIndex,advance] using r8.rowIndex
    tidIndex := by simpa [copyRoundAfter,copyRoundEnd,setIndex,advance] using r8.tidIndex
    iterationIndex := by simp [copyRoundAfter,copyRoundEnd,setIndex,advance]
    cached := r8.cached
    completed := by
      have he : (iteration+1)*8=iteration*8+(0+8) := by omega
      simpa only [copyRoundAfter,copyRoundEnd,setIndex,advance,he] using r8.completed }

theorem copy_round_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t extra : Nat) (inverse : α) (s : State α)
    (hr : row<p.rows) (ht : tid<1024) (hi : iteration<2)
    (ready : CopyRoundReady ops input row tid iteration t inverse s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+61) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
      (copyRoundAfter ops input row tid iteration t inverse s) := by
  let entry := copyRoundBegin t s
  let copied := outputCopies ops input row tid iteration t inverse 0 8 entry
  have r0 := copy_round_begin_ready ops input row tid iteration t inverse s ready
  have r8 := output_copies_ready ops input row tid iteration t 0 8 inverse entry hi (by decide) r0
  rw [show extra+61=(extra+59)+2 by omega,copy_round_begin_eq p ops iteration t (extra+59) s hi ready.pc ready.iterationIndex]
  rw [show extra+59=(extra+3)+7*8 by omega,output_copies_eq p ops input row tid iteration t 0 8 (extra+3) inverse entry hr ht hi (by decide) r0]
  exact copy_round_end_eq p ops iteration t extra copied hi r8.pc r8.iterationIndex r8.componentIndex

theorem copy_round_memory_outside (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) (l : Location) (hi : iteration<2)
    (hl : OutsideCopies row tid l) : (copyRoundAfter ops input row tid iteration t inverse s).memory l=s.memory l :=
  output_copies_memory_outside ops input row tid iteration t 0 8 inverse (copyRoundBegin t s) l hi (by decide) hl

theorem copy_round_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) :
    (copyRoundAfter ops input row tid iteration t inverse s).epochs=s.epochs := by
  simp only [copyRoundAfter,copyRoundEnd,setIndex,advance,output_copies_epochs,copyRoundBegin]

theorem copy_round_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) :
    (copyRoundAfter ops input row tid iteration t inverse s).trace.length=s.trace.length+16 := by
  simp only [copyRoundAfter,copyRoundEnd,setIndex,advance,output_copies_trace_length,copyRoundBegin]

theorem copy_round_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (inverse : α) (s : State α) (ht : tid<1024) (hi : iteration<2)
    (he : t=row*1024+tid) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(copyRoundAfter ops input row tid iteration t inverse s).trace,Good event :=
  output_copies_good ops input row tid iteration t 0 8 inverse (copyRoundBegin t s) ht hi (by decide) he good

def copyTwoRounds (ops : Ops α) (input : Nat → Nat → α) (row tid t : Nat) (inverse : α) (s : State α) : State α :=
  copyRoundAfter ops input row tid 1 t inverse (copyRoundAfter ops input row tid 0 t inverse s)

theorem copy_two_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (ready : CopyRoundReady ops input row tid 0 t inverse s) :
    CopyRoundReady ops input row tid 2 t inverse (copyTwoRounds ops input row tid t inverse s) :=
  copy_round_ready ops input row tid 1 t inverse _ (by decide)
    (copy_round_ready ops input row tid 0 t inverse s (by decide) ready)

theorem copy_two_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t extra : Nat) (inverse : α) (s : State α) (hr : row<p.rows) (ht : tid<1024)
    (ready : CopyRoundReady ops input row tid 0 t inverse s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+122) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (copyTwoRounds ops input row tid t inverse s) := by
  rw [show extra+122=(extra+61)+61 by omega,copy_round_eq p ops input row tid 0 t (extra+61) inverse s hr ht (by decide) ready]
  exact copy_round_eq p ops input row tid 1 t extra inverse _ hr ht (by decide)
    (copy_round_ready ops input row tid 0 t inverse s (by decide) ready)

theorem copy_two_memory_outside (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (l : Location) (hl : OutsideCopies row tid l) :
    (copyTwoRounds ops input row tid t inverse s).memory l=s.memory l :=
  (copy_round_memory_outside ops input row tid 1 t inverse _ l (by decide) hl).trans
    (copy_round_memory_outside ops input row tid 0 t inverse s l (by decide) hl)

theorem copy_two_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) :
    (copyTwoRounds ops input row tid t inverse s).epochs=s.epochs :=
  (copy_round_epochs ops input row tid 1 t inverse _).trans (copy_round_epochs ops input row tid 0 t inverse s)

theorem copy_two_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) :
    (copyTwoRounds ops input row tid t inverse s).trace.length=s.trace.length+32 := by
  simp only [copyTwoRounds,copy_round_trace_length]

theorem copy_two_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (ht : tid<1024) (he : t=row*1024+tid)
    (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(copyTwoRounds ops input row tid t inverse s).trace,Good event :=
  copy_round_good ops input row tid 1 t inverse _ ht (by decide) he
    (copy_round_good ops input row tid 0 t inverse s ht (by decide) he good)

#print axioms copy_round_begin_eq
#print axioms copy_round_end_eq
#print axioms copy_rounds_exit_eq
#print axioms copy_round_begin_ready
#print axioms copy_round_ready
#print axioms copy_round_eq
#print axioms copy_round_memory_outside
#print axioms copy_round_epochs
#print axioms copy_round_trace_length
#print axioms copy_round_good
#print axioms copy_two_ready
#print axioms copy_two_eq
#print axioms copy_two_memory_outside
#print axioms copy_two_epochs
#print axioms copy_two_trace_length
#print axioms copy_two_good
end LarkNativeSglangRmsNorm
