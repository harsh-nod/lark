import Lark.NativeSglangRmsNormAdd

/-! The actual last add and original/guarded shared-store instruction tails.
Stores are kept even when their values coincide. No race-freedom premise is
assumed, so the original source's conflicting writes remain in the trace.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
open LarkReduction (setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def firstBarrier (repaired : Bool) : Nat := if repaired then 56 else 55
def partialSlot (t warp : Nat) : Location := ⟨.shared,t/1024,0,warp⟩
def partialWrite (t pc warp : Nat) (value : α) (s : State α) : State α :=
  advance { record s t (partialSlot t warp) true with
    memory := fun l => if l = partialSlot t warp then some value else s.memory l } t pc

def partialTail (repaired : Bool) (t lane warp : Nat) (value : α) (s : State α) : State α :=
  if repaired then
    if lane=0 then partialWrite t 56 warp value (advance s t 55) else advance s t 56
  else partialWrite t 55 warp value s

def lastPartial (repaired : Bool) (ops : Ops α) (t : Nat) (a b : α) (s : State α) : State α :=
  partialTail repaired t ((t%1024)%32) ((t%1024)/32) (ops.add a b) (addAfter ops t 53 a b s)

theorem partial_slot_location (p : Shape) (t warp : Nat) (hw : warp < 32) :
    location (layout p) (geometry p) t .shared 0 (warp : Int) true = some (partialSlot t warp) := by
  simp [location,layout,geometry,partialSlot,show ¬(warp : Int)<0 by omega,hw]

theorem partial_store_execute (p : Shape) (ops : Ops α) (t pc warp : Nat) (value : α) (s : State α)
    (hw : warp<32) (hi : s.indices t 3 = some (warp : Int))
    (ha : s.regs t 0 = some value) (hp : s.pc t = pc) :
    execute ops (layout p) (geometry p) t (.store .shared 0 (.ivar 3) (.reg 0)) s =
      some (partialWrite t (pc+1) warp value s) := by
  simp [execute,evalIndex,hi,partial_slot_location p t warp hw,evalExpr,ha,hp,partialWrite,record]

theorem original_partial_tail (p : Shape) (ops : Ops α) (t lane warp extra : Nat)
    (value : α) (s : State α) (hw : warp<32) (hi : s.indices t 3 = some (warp : Int))
    (ha : s.regs t 0 = some value) (hp : s.pc t=54) :
    LarkCollective.runLane ops (layout p) (geometry p) (program false) t (extra+2) s =
      some (partialTail false t lane warp value s) := by
  have he := partial_store_execute p ops t 54 warp value s hw hi ha hp
  rw [scalar_step p false ops t 54 (extra+1) _ s _ original_partial_store hp he]
  have hc : LarkCollective.parked (program false) (partialWrite t 55 warp value s) t = some .block := by
    simp only [LarkCollective.parked,partialWrite,advance,↓reduceIte]
    rw [original_barriers.1]
    rfl
  rw [LarkCollective.runLane,hc]
  rfl

theorem fixed_partial_tail (p : Shape) (ops : Ops α) (t lane warp extra : Nat)
    (value : α) (s : State α) (hw : warp<32)
    (hi2 : s.indices t 2 = some (lane : Int)) (hi3 : s.indices t 3 = some (warp : Int))
    (ha : s.regs t 0 = some value) (hp : s.pc t=54) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+3) s =
      some (partialTail true t lane warp value s) := by
  have heq : evalPredicate (geometry p) t s (.eq (.ivar 2) (.const 0)) = some (decide (lane=0)) := by
    simp [evalPredicate,evalIndex,hi2,int32] <;> omega
  by_cases hl : lane=0
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 2) (.const 0)) = some true := by simpa [hl] using heq
    let gated := advance s t 55
    have he : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 2) (.const 0)) 56) s = some gated := by
      simp [execute,hg,hp,gated]
    have hs := partial_store_execute p ops t 55 warp value gated hw hi3 ha (by simp [gated,advance])
    rw [scalar_step p true ops t 54 (extra+2) _ s gated repaired_partial_gate hp he]
    rw [scalar_step p true ops t 55 (extra+1) _ gated _ repaired_partial_store (by simp [gated,advance]) hs]
    have hc : LarkCollective.parked (program true) (partialWrite t 56 warp value gated) t = some .block := by
      simp only [LarkCollective.parked,partialWrite,advance,↓reduceIte]
      rw [repaired_barriers.1]
      rfl
    rw [LarkCollective.runLane,hc]
    simp only [partialTail,hl,↓reduceIte]
    rfl
  · have hg : evalPredicate (geometry p) t s (.eq (.ivar 2) (.const 0)) = some false := by simpa [hl] using heq
    have he : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 2) (.const 0)) 56) s =
        some (advance s t 56) := by simp [execute,hg]
    rw [scalar_step p true ops t 54 (extra+2) _ s _ repaired_partial_gate hp he]
    have hc : LarkCollective.parked (program true) (advance s t 56) t = some .block := by
      simp only [LarkCollective.parked,advance,↓reduceIte]
      rw [repaired_barriers.1]
      rfl
    rw [LarkCollective.runLane,hc]
    simp only [partialTail,hl,↓reduceIte]

theorem last_partial_lane (p : Shape) (repaired : Bool) (ops : Ops α) (t : Nat)
    (a b : α) (s : State α) (indices : NativeIndices t s)
    (hp : s.pc t=53) (ha : s.regs t 0=some a) (hb : s.regs t 1=some b) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane s =
      some (lastPartial repaired ops t a b s) := by
  have hw : (t%1024)/32<32 := by omega
  have code : (program repaired)[53]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) := by
    cases repaired <;> decide
  cases repaired with
  | false =>
      change LarkCollective.runLane ops (layout p) (geometry p) (program false) t (509+3) s = _
      rw [add_eq p false ops t 53 (509+2) a b s hp ha hb code]
      exact original_partial_tail p ops t ((t%1024)%32) ((t%1024)/32) 509 (ops.add a b)
        (addAfter ops t 53 a b s) hw indices.2.2.2 (by simp [addAfter,setReg,advance])
        (by simp [addAfter,setReg,advance])
  | true =>
      change LarkCollective.runLane ops (layout p) (geometry p) (program true) t (508+4) s = _
      rw [add_eq p true ops t 53 (508+3) a b s hp ha hb code]
      exact fixed_partial_tail p ops t ((t%1024)%32) ((t%1024)/32) 508 (ops.add a b)
        (addAfter ops t 53 a b s) hw indices.2.2.1 indices.2.2.2 (by simp [addAfter,setReg,advance])
        (by simp [addAfter,setReg,advance])

theorem last_partial_fields (repaired : Bool) (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (lastPartial repaired ops t a b s).pc t=firstBarrier repaired ∧
    (lastPartial repaired ops t a b s).indices=s.indices ∧
    (lastPartial repaired ops t a b s).regs=(addAfter ops t 53 a b s).regs ∧
    (lastPartial repaired ops t a b s).epochs=s.epochs := by
  cases repaired <;> by_cases hz : t%32=0 <;>
    simp [lastPartial,partialTail,firstBarrier,partialWrite,addAfter,setReg,advance,record,hz]

theorem last_partial_other (repaired : Bool) (ops : Ops α) (t u : Nat)
    (a b : α) (s : State α) (hu : u≠t) :
    (lastPartial repaired ops t a b s).pc u=s.pc u ∧
    (lastPartial repaired ops t a b s).regs u=s.regs u := by
  cases repaired <;> by_cases hz : t%32=0 <;>
    simp [lastPartial,partialTail,partialWrite,addAfter,setReg,advance,record,hu,hz]

theorem last_partial_memory (repaired : Bool) (ops : Ops α) (t : Nat)
    (a b : α) (s : State α) (l : Location) (hl : l≠partialSlot t ((t%1024)/32)) :
    (lastPartial repaired ops t a b s).memory l=s.memory l := by
  cases repaired <;> by_cases hz : t%32=0 <;>
    simp [lastPartial,partialTail,partialWrite,addAfter,setReg,advance,record,hl,hz]

theorem last_partial_trace (repaired : Bool) (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (lastPartial repaired ops t a b s).trace =
      (if repaired ∧ (t%1024)%32≠0 then [] else [⟨t,partialSlot t ((t%1024)/32),true,s.epochs t⟩]) ++ s.trace := by
  cases repaired <;> by_cases hz : t%32=0 <;>
    simp [lastPartial,partialTail,partialWrite,addAfter,setReg,advance,record,hz]

theorem last_partial_regs (repaired : Bool) (ops : Ops α) (t : Nat) (a b : α) (s : State α) :
    (lastPartial repaired ops t a b s).regs t 0=some (ops.add a b) := by
  rw [(last_partial_fields repaired ops t a b s).2.2.1]
  simp [addAfter,setReg,advance]

#print axioms partial_slot_location
#print axioms partial_store_execute
#print axioms original_partial_tail
#print axioms fixed_partial_tail
#print axioms last_partial_lane
#print axioms last_partial_fields
#print axioms last_partial_other
#print axioms last_partial_memory
#print axioms last_partial_trace
#print axioms last_partial_regs
end LarkNativeSglangRmsNorm
