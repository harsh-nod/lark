import Lark.NativeSglangRmsNormRegisterXor

/-! Source-ordered register addition with explicit register IDs. This supports
the second RMSNorm reduction's accumulator7/peer8 without changing the machine.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def regAddAfter (ops : Ops α) (dest t pc : Nat) (a b : α) (s : State α) : State α :=
  setReg s t dest (ops.add a b) (pc+1)

theorem reg_add_eq (p : Shape) (ops : Ops α) (dest peer t pc extra : Nat) (a b : α) (s : State α)
    (hp : s.pc t=pc) (ha : s.regs t dest=some a) (hb : s.regs t peer=some b)
    (code : (program true)[pc]?=some (.scalar (.assign dest (.bin .add (.reg dest) (.reg peer))))) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+1) s=
      LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (regAddAfter ops dest t pc a b s) := by
  have he := execute_pure_of ops (layout p) (geometry p) t dest (pc+1)
    (.bin .add (.reg dest) (.reg peer)) s (ops.add a b)
    (by simp [evalExpr,applyBinary,ha,hb]) (by omega)
  exact scalar_step p true ops t pc extra _ s _ code hp he

theorem reg_add_lane (p : Shape) (ops : Ops α) (dest peer t pc mask : Nat) (a b : α) (s : State α)
    (hp : s.pc t=pc) (ha : s.regs t dest=some a) (hb : s.regs t peer=some b)
    (code : (program true)[pc]?=some (.scalar (.assign dest (.bin .add (.reg dest) (.reg peer)))))
    (nextCode : (program true)[pc+1]?=some (.shuffle .xor peer dest (.const (mask : Int)) 32)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s=
      some (regAddAfter ops dest t pc a b s) := by
  change LarkCollective.runLane ops (layout p) (geometry p) (program true) t (511+1) s=_
  rw [reg_add_eq p ops dest peer t pc 511 a b s hp ha hb code]
  have parked : LarkCollective.parked (program true) (regAddAfter ops dest t pc a b s) t=some .shuffle := by
    simp only [LarkCollective.parked,regAddAfter,setReg,advance,↓reduceIte,nextCode]
  rw [LarkCollective.runLane,parked]

theorem reg_add_other (ops : Ops α) (dest t pc u : Nat) (a b : α) (s : State α) (hu : u≠t) :
    (regAddAfter ops dest t pc a b s).pc u=s.pc u ∧
    (regAddAfter ops dest t pc a b s).regs u=s.regs u := by
  simp [regAddAfter,setReg,advance,hu]

def regAddFold (ops : Ops α) (dest pc : Nat) (a b : Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => regAddAfter ops dest t pc (a t) (b t) s) s

theorem reg_add_fold_other (ops : Ops α) (dest pc : Nat) (a b : Nat → α)
    (ts : List Nat) (t : Nat) (s : State α) (ht : t∉ts) :
    (regAddFold ops dest pc a b ts s).pc t=s.pc t ∧ (regAddFold ops dest pc a b ts s).regs t=s.regs t := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons u ts ih =>
      have hne : t≠u := by intro he; subst t; simp at ht
      have hn : t∉ts := by intro hm; exact ht (by simp [hm])
      have h := ih (regAddAfter ops dest u pc (a u) (b u) s) hn
      have hs := reg_add_other ops dest u pc t (a u) (b u) s hne
      exact ⟨h.1.trans hs.1,h.2.trans hs.2⟩

theorem reg_add_fold_preserves (ops : Ops α) (dest pc : Nat) (a b : Nat → α) (ts : List Nat) (s : State α) :
    (regAddFold ops dest pc a b ts s).memory=s.memory ∧
    (regAddFold ops dest pc a b ts s).indices=s.indices ∧
    (regAddFold ops dest pc a b ts s).epochs=s.epochs ∧ (regAddFold ops dest pc a b ts s).trace=s.trace := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl,rfl⟩
  | cons t ts ih => exact ih (regAddAfter ops dest t pc (a t) (b t) s)

theorem reg_add_fold_member (ops : Ops α) (dest pc : Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup) (t : Nat) (ht : t∈ts) :
    (regAddFold ops dest pc a b ts s).pc t=pc+1 ∧
    (regAddFold ops dest pc a b ts s).regs t dest=some (ops.add (a t) (b t)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have h := reg_add_fold_other ops dest pc a b ts u (regAddAfter ops dest u pc (a u) (b u) s) hnot
        constructor
        · simpa [regAddAfter,setReg,advance] using h.1
        · simpa [regAddAfter,setReg,advance] using congrFun h.2 dest
      · exact ih (regAddAfter ops dest u pc (a u) (b u) s) hnodup hm

theorem reg_add_fold_run (p : Shape) (ops : Ops α) (dest peer pc mask : Nat) (a b : Nat → α)
    (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (hp : ∀ t∈ts,s.pc t=pc) (ha : ∀ t∈ts,s.regs t dest=some (a t))
    (hb : ∀ t∈ts,s.regs t peer=some (b t))
    (code : (program true)[pc]?=some (.scalar (.assign dest (.bin .add (.reg dest) (.reg peer)))))
    (nextCode : (program true)[pc+1]?=some (.shuffle .xor peer dest (.const (mask : Int)) 32)) :
    ts.foldlM (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane u) s=
      some (regAddFold ops dest pc a b ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      have hother : ∀ u∈ts,u≠t := by intro u hu he; subst u; exact hnot hu
      rw [List.foldlM_cons,reg_add_lane p ops dest peer t pc mask (a t) (b t) s
        (hp t (by simp)) (ha t (by simp)) (hb t (by simp)) code nextCode]
      simp only [bind,Option.some_bind]
      apply ih (regAddAfter ops dest t pc (a t) (b t) s) hnodup
      · intro u hu
        exact (reg_add_other ops dest t pc u (a t) (b t) s (hother u hu)).1.trans (hp u (by simp [hu]))
      · intro u hu
        exact (congrFun (reg_add_other ops dest t pc u (a t) (b t) s (hother u hu)).2 dest).trans (ha u (by simp [hu]))
      · intro u hu
        exact (congrFun (reg_add_other ops dest t pc u (a t) (b t) s (hother u hu)).2 peer).trans (hb u (by simp [hu]))

#print axioms reg_add_eq
#print axioms reg_add_lane
#print axioms reg_add_other
#print axioms reg_add_fold_other
#print axioms reg_add_fold_preserves
#print axioms reg_add_fold_member
#print axioms reg_add_fold_run
end LarkNativeSglangRmsNorm
