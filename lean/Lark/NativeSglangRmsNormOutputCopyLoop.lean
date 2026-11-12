import Lark.NativeSglangRmsNormOutputCopy

/-! The actual eight-component global-copy loop. Each stored value is retained
through subsequent distinct writes, while every private cached half survives.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def flatAddress (row tid k : Nat) : Nat := address row (column tid (k/8) (k%8))

theorem flat_address_rank (row tid iteration component : Nat) (hc : component<8) :
    flatAddress row tid (iteration*8+component)=address row (column tid iteration component) := by
  have hd : (iteration*8+component)/8=iteration := by omega
  have hm : (iteration*8+component)%8=component := by omega
  simp only [flatAddress,hd,hm]

theorem flat_address_injective (row tid a b : Nat) (ha : a<16) (hb : b<16)
    (he : flatAddress row tid a=flatAddress row tid b) : a=b := by
  unfold flatAddress address column at he
  omega

def GlobalPrefix (ops : Ops α) (input : Nat → Nat → α) (row tid count : Nat)
    (inverse : α) (s : State α) : Prop :=
  ∀ k,k<count → s.memory (globalCell 0 (flatAddress row tid k))=
    some (outputScaled ops input row tid (k/8) (k%8) inverse)

theorem output_copy_prefix (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) (hi : iteration<2) (hc : component<8)
    (done : GlobalPrefix ops input row tid (iteration*8+component) inverse s) :
    GlobalPrefix ops input row tid (iteration*8+component+1) inverse
      (outputCopyAfter ops input row tid iteration component t inverse s) := by
  intro k hk
  by_cases heq : k=iteration*8+component
  · subst k
    have hd : (iteration*8+component)/8=iteration := by omega
    have hm : (iteration*8+component)%8=component := by omega
    simpa only [flat_address_rank row tid iteration component hc,hd,hm] using
      output_copy_written ops input row tid iteration component t inverse s
  · have hn : globalCell 0 (flatAddress row tid k)≠globalCell 0 (address row (column tid iteration component)) := by
      intro he
      have hoff := congrArg Location.offset he
      change flatAddress row tid k=address row (column tid iteration component) at hoff
      rw [← flat_address_rank row tid iteration component hc] at hoff
      exact heq (flat_address_injective row tid k (iteration*8+component) (by omega) (by omega) hoff)
    rw [output_copy_memory,if_neg hn]
    exact done k (by omega)

theorem output_copy_cached (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α)
    (cached : OutputPrefix ops input row tid 16 t inverse s) :
    OutputPrefix ops input row tid 16 t inverse (outputCopyAfter ops input row tid iteration component t inverse s) := by
  intro k hk
  rw [output_copy_memory,if_neg (by simp [privateCell,globalCell])]
  exact cached k hk

structure CopyReady (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) : Prop where
  pc : s.pc t=100
  rowIndex : s.indices t 0=some (row : Int)
  tidIndex : s.indices t 1=some (tid : Int)
  iterationIndex : s.indices t 19=some (iteration : Int)
  componentIndex : s.indices t 20=some (component : Int)
  cached : OutputPrefix ops input row tid 16 t inverse s
  completed : GlobalPrefix ops input row tid (iteration*8+component) inverse s

theorem output_copy_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) (hi : iteration<2) (hc : component<8)
    (ready : CopyReady ops input row tid iteration component t inverse s) :
    CopyReady ops input row tid iteration (component+1) t inverse
      (outputCopyAfter ops input row tid iteration component t inverse s) := by
  have h := output_copy_fields ops input row tid iteration component t inverse s
  exact {
    pc := h.1,rowIndex := h.2.1.trans ready.rowIndex,tidIndex := h.2.2.1.trans ready.tidIndex
    iterationIndex := h.2.2.2.1.trans ready.iterationIndex,componentIndex := h.2.2.2.2.1
    cached := output_copy_cached ops input row tid iteration component t inverse s ready.cached
    completed := by simpa only [Nat.add_assoc] using output_copy_prefix ops input row tid iteration component t inverse s hi hc ready.completed }

def outputCopies (ops : Ops α) (input : Nat → Nat → α) (row tid iteration t : Nat) (inverse : α) :
    Nat → Nat → State α → State α
  | _,0,s => s
  | component,remaining+1,s => outputCopies ops input row tid iteration t inverse (component+1) remaining
      (outputCopyAfter ops input row tid iteration component t inverse s)

theorem output_copies_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (inverse : α) (s : State α)
    (hi : iteration<2) (hcount : component+remaining≤8)
    (ready : CopyReady ops input row tid iteration component t inverse s) :
    CopyReady ops input row tid iteration (component+remaining) t inverse
      (outputCopies ops input row tid iteration t inverse component remaining s) := by
  induction remaining generalizing component s with
  | zero => simpa only [outputCopies,Nat.add_zero] using ready
  | succ remaining ih =>
      have h := ih (component+1) _ (by omega) (output_copy_ready ops input row tid iteration component t inverse s hi (by omega) ready)
      simpa only [outputCopies,show component+1+remaining=component+(remaining+1) by omega] using h

theorem output_copies_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining extra : Nat) (inverse : α) (s : State α)
    (hr : row<p.rows) (ht : tid<1024) (hi : iteration<2) (hcount : component+remaining≤8)
    (ready : CopyReady ops input row tid iteration component t inverse s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+7*remaining) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
      (outputCopies ops input row tid iteration t inverse component remaining s) := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih =>
      rw [show extra+7*(remaining+1)=(extra+7*remaining)+7 by omega,
        output_copy_cycle p ops input row tid iteration component t (extra+7*remaining) inverse s hr ht hi (by omega)
          ready.rowIndex ready.tidIndex ready.iterationIndex ready.componentIndex ready.pc ready.cached]
      exact ih (component+1) _ (by omega) (output_copy_ready ops input row tid iteration component t inverse s hi (by omega) ready)

def OutsideCopies (row tid : Nat) (l : Location) : Prop :=
  ∀ iteration,iteration<2 → ∀ component,component<8 → l≠globalCell 0 (address row (column tid iteration component))

theorem output_copies_memory_outside (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (inverse : α) (s : State α) (l : Location)
    (hi : iteration<2) (hcount : component+remaining≤8) (hl : OutsideCopies row tid l) :
    (outputCopies ops input row tid iteration t inverse component remaining s).memory l=s.memory l := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih =>
      change (outputCopies ops input row tid iteration t inverse (component+1) remaining
        (outputCopyAfter ops input row tid iteration component t inverse s)).memory l=_
      rw [ih (component+1) _ (by omega),output_copy_memory,if_neg (hl iteration hi component (by omega))]

theorem output_copies_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (inverse : α) (s : State α) :
    (outputCopies ops input row tid iteration t inverse component remaining s).epochs=s.epochs := by
  induction remaining generalizing component s with
  | zero => rfl
  | succ remaining ih => exact (ih (component+1) _).trans (output_copy_fields ops input row tid iteration component t inverse s).2.2.2.2.2.2

theorem output_copies_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (inverse : α) (s : State α) :
    (outputCopies ops input row tid iteration t inverse component remaining s).trace.length=s.trace.length+2*remaining := by
  induction remaining generalizing component s with
  | zero => simp [outputCopies]
  | succ remaining ih => simp only [outputCopies,ih,output_copy_trace,List.length_cons]; omega

theorem output_copies_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (inverse : α) (s : State α)
    (ht : tid<1024) (hi : iteration<2) (hcount : component+remaining≤8) (he : t=row*1024+tid)
    (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(outputCopies ops input row tid iteration t inverse component remaining s).trace,Good event := by
  induction remaining generalizing component s with
  | zero => exact good
  | succ remaining ih =>
      exact ih (component+1) _ (by omega)
        (output_copy_good ops input row tid iteration component t inverse s ht hi (by omega) he good)

#print axioms flat_address_rank
#print axioms flat_address_injective
#print axioms output_copy_prefix
#print axioms output_copy_cached
#print axioms output_copy_ready
#print axioms output_copies_ready
#print axioms output_copies_eq
#print axioms output_copies_memory_outside
#print axioms output_copies_epochs
#print axioms output_copies_trace_length
#print axioms output_copies_good
end LarkNativeSglangRmsNorm
