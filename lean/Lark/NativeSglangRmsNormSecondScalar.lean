import Lark.NativeSglangRmsNormFirstBlock

/-! The second source reduction's scalar prefix. Only the first logical32
threads read a shared partial. Every other thread skips to the second barrier.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold

def secondActive (ops : Ops α) (t tid : Nat) (value : α) (s : State α) : State α :=
  let s := advance s t 58
  let s := setReg s t 7 (ops.literal 0 1) 59
  let s := advance s t 60
  let s := setReg (record s t (partialSlot t tid) false) t 7 value 61
  setReg s t 8 (ops.literal 0 1) 62

def secondLane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  if t%1024<32 then secondActive ops t (t%1024) (blockPartialValue ops input (t/1024) (t%1024)) s
  else advance s t 76

theorem second_load_execute (p : Shape) (ops : Ops α) (t tid : Nat) (value : α) (s : State α)
    (ht : tid<32) (hi : s.indices t 1=some (tid : Int))
    (hm : s.memory (partialSlot t tid)=some value) (hp : s.pc t=60) :
    execute ops (layout p) (geometry p) t (.assign 7 (.load .shared 0 (.ivar 1))) s=
      some (setReg (record s t (partialSlot t tid) false) t 7 value 61) := by
  have loc : location (layout p) (geometry p) t .shared 0 (tid : Int) false=some (partialSlot t tid) := by
    simp [location,layout,geometry,partialSlot,show ¬(tid : Int)<0 by omega,ht]
  simp [execute,evalExpr,evalIndex,hi,loc,hm,hp,setReg,record,advance]

theorem second_active_lane (p : Shape) (ops : Ops α) (t tid extra : Nat) (value : α) (s : State α)
    (ht : tid<32) (hi1 : s.indices t 1=some (tid : Int)) (hi3 : s.indices t 3=some 0)
    (hm : s.memory (partialSlot t tid)=some value) (hp : s.pc t=57) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+6) s=
      some (secondActive ops t tid value s) := by
  let s1 := advance s t 58
  let s2 := setReg s1 t 7 (ops.literal 0 1) 59
  let s3 := advance s2 t 60
  let s4 := setReg (record s3 t (partialSlot t tid) false) t 7 value 61
  let s5 := setReg s4 t 8 (ops.literal 0 1) 62
  have hgate : evalPredicate (geometry p) t s (.eq (.ivar 3) (.const 0))=some true := by
    simp [evalPredicate,evalIndex,hi3,int32]
  have h1 : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 3) (.const 0)) 76) s=some s1 := by
    simp [execute,hgate,hp,s1]
  have h2 := execute_pure_of ops (layout p) (geometry p) t 7 59 (.lit 0 1) s1 (ops.literal 0 1)
    (by simp [evalExpr]) (by simp [s1,advance])
  have hlt : evalPredicate (geometry p) t s2 (.lt (.ivar 1) (.const 32))=some true := by
    simp [evalPredicate,evalIndex,s2,s1,setReg,advance,hi1,int32] <;> omega
  have h3 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 1) (.const 32)) 61) s2=some s3 := by
    have hp2 : s2.pc t=59 := by simp [s2,setReg,advance]
    simp only [execute,hlt,hp2,bind,pure,Option.bind,↓reduceIte,s3]
  have h4 := second_load_execute p ops t tid value s3 ht hi1 hm (by simp [s3,advance])
  have h5 := execute_pure_of ops (layout p) (geometry p) t 8 62 (.lit 0 1) s4 (ops.literal 0 1)
    (by simp [evalExpr]) (by simp [s4,setReg,advance])
  rw [scalar_step p true ops t 57 (extra+5) _ s s1 (by decide) hp h1]
  rw [scalar_step p true ops t 58 (extra+4) _ s1 s2 (by decide) (by simp [s1,advance]) h2]
  rw [scalar_step p true ops t 59 (extra+3) _ s2 s3 (by decide) (by simp [s2,setReg,advance]) h3]
  rw [scalar_step p true ops t 60 (extra+2) _ s3 s4 (by decide) (by simp [s3,advance]) h4]
  rw [scalar_step p true ops t 61 (extra+1) _ s4 s5 (by decide) (by simp [s4,setReg,advance]) h5]
  have hcut : LarkCollective.parked (program true) s5 t=some .shuffle := by
    have code : (program true)[62]?=some (.shuffle .xor 8 7 (.const 16) 32) := by decide
    simp only [LarkCollective.parked,s5,setReg,advance,↓reduceIte,code]
  rw [LarkCollective.runLane,hcut]
  rfl

theorem second_inactive_lane (p : Shape) (ops : Ops α) (t warp extra : Nat) (s : State α)
    (hw : warp≠0) (hi3 : s.indices t 3=some (warp : Int)) (hp : s.pc t=57) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+2) s=some (advance s t 76) := by
  have hgate : evalPredicate (geometry p) t s (.eq (.ivar 3) (.const 0))=some false := by
    simp [evalPredicate,evalIndex,hi3,int32,hw] <;> omega
  have he : execute ops (layout p) (geometry p) t (.branch (.eq (.ivar 3) (.const 0)) 76) s=some (advance s t 76) := by
    simp [execute,hgate]
  rw [scalar_step p true ops t 57 (extra+1) _ s _ (by decide) hp he]
  have hcut : LarkCollective.parked (program true) (advance s t 76) t=some .block := by
    have code : (program true)[76]?=some (.scalar (.barrier .block)) := by decide
    simp only [LarkCollective.parked,advance,↓reduceIte,code,scalarCut]
  rw [LarkCollective.runLane,hcut]

theorem second_source_lane (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (hi : NativeIndices t s) (hp : s.pc t=57)
    (shared : ∀ tid,tid<32 → s.memory (partialSlot t tid)=some (blockPartialValue ops input (t/1024) tid)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s=some (secondLane ops input t s) := by
  by_cases htid : t%1024<32
  · have hw : t%1024/32=0 := by omega
    change LarkCollective.runLane ops (layout p) (geometry p) (program true) t (506+6) s=_
    rw [second_active_lane p ops t (t%1024) 506 _ s htid hi.2.1
      (by simpa only [hw] using hi.2.2.2) (shared _ htid) hp]
    simp only [secondLane,if_pos htid]
  · have hw : t%1024/32≠0 := by omega
    change LarkCollective.runLane ops (layout p) (geometry p) (program true) t (510+2) s=_
    rw [second_inactive_lane p ops t (t%1024/32) 510 s hw hi.2.2.2 hp]
    simp only [secondLane,if_neg htid]

theorem second_active_fields (ops : Ops α) (t tid : Nat) (value : α) (s : State α) :
    (secondActive ops t tid value s).pc t=62 ∧
    (secondActive ops t tid value s).regs t 7=some value ∧
    (secondActive ops t tid value s).regs t 8=some (ops.literal 0 1) := by
  simp [secondActive,setReg,advance,record]

theorem second_lane_preserves (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (secondLane ops input t s).memory=s.memory ∧ (secondLane ops input t s).indices=s.indices ∧
    (secondLane ops input t s).epochs=s.epochs := by
  unfold secondLane
  split <;> simp [secondActive,setReg,advance,record]

theorem second_lane_other (ops : Ops α) (input : Nat → Nat → α) (t u : Nat) (s : State α) (hu : u≠t) :
    (secondLane ops input t s).pc u=s.pc u ∧ (secondLane ops input t s).regs u=s.regs u := by
  unfold secondLane
  split <;> simp [secondActive,setReg,advance,record,hu]

theorem second_lane_trace (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (secondLane ops input t s).trace=
      (if t%1024<32 then [⟨t,partialSlot t (t%1024),false,s.epochs t⟩] else []) ++ s.trace := by
  unfold secondLane
  split <;> simp_all [secondActive,setReg,advance,record]

#print axioms second_load_execute
#print axioms second_active_lane
#print axioms second_inactive_lane
#print axioms second_source_lane
#print axioms second_active_fields
#print axioms second_lane_preserves
#print axioms second_lane_other
#print axioms second_lane_trace
end LarkNativeSglangRmsNorm
