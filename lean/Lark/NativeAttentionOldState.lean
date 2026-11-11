import Lark.NativeAttentionWeights

/-! Source selection of the old online state: no private reads on key tile zero,
and two checked per-thread private reads on subsequent key tiles. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setReg execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def privateCell (t buffer index : Nat) : Location := ⟨.local, t, buffer, index⟩

theorem private_location (p : Shape) (t buffer index : Nat) (write : Bool)
    (hb : buffer = 0 ∨ buffer = 1) (hi : index < 4) :
    location (layout p) (geometry p) t .local buffer (index : Int) write = some (privateCell t buffer index) := by
  rcases hb with rfl | rfl
  all_goals exact location_local (layout p) (geometry p) t _ index 4 write (by rfl) hi

theorem load_private (p : Shape) (ops : Ops α) (t buffer qi : Nat) (value : α) (s : State α)
    (hb : buffer = 0 ∨ buffer = 1) (hi : qi < 4) (hq : s.indices t 7 = some (qi : Int))
    (hv : s.memory (privateCell t buffer qi) = some value) :
    evalExpr ops (layout p) (geometry p) t (.load .local buffer (.ivar 7)) s =
      some (value, record s t (privateCell t buffer qi) false) :=
  eval_load_of ops (layout p) (geometry p) t buffer .local (.ivar 7) s (qi : Int) _ value hq
    (private_location p t buffer qi false hb hi) hv

def selectedMaximum (key : Nat) (rowMaximum previous : α) : α := if key = 0 then rowMaximum else previous
def selectedMass (ops : Ops α) (key : Nat) (previous : α) : α := if key = 0 then ops.literal 0 1 else previous
def oldEntry (ops : Ops α) (t : Nat) (rowMaximum : α) (s : State α) : State α :=
  setReg (setReg s t 7 rowMaximum 57) t 8 (ops.literal 0 1) 58
def oldTailFuel (key : Nat) : Nat := if key = 0 then 1 else 3
def oldTail (t qi key : Nat) (previousMaximum previousMass : α) (s : State α) : State α :=
  if key = 0 then advance s t 61 else
    let s := advance s t 59
    let s := setReg (record s t (privateCell t 0 qi) false) t 7 previousMaximum 60
    setReg (record s t (privateCell t 1 qi) false) t 8 previousMass 61
def oldSelected (ops : Ops α) (t qi key : Nat) (rowMaximum previousMaximum previousMass : α) (s : State α) : State α :=
  oldTail t qi key previousMaximum previousMass (oldEntry ops t rowMaximum s)

theorem old_entry_eq (p : Shape) (ops : Ops α) (t extra : Nat) (rowMaximum : α) (s : State α)
    (hm : s.regs t 0 = some rowMaximum) (hp : s.pc t = 56) :
    runLane ops (layout p) (geometry p) program t (extra + 2) s =
      runLane ops (layout p) (geometry p) program t extra (oldEntry ops t rowMaximum s) := by
  let s1 := setReg s t 7 rowMaximum 57
  have h1 := execute_pure_of ops (layout p) (geometry p) t 7 57 (.reg 0) s rowMaximum
    (by simp [evalExpr, hm]) (by omega)
  have h2 := execute_pure_of ops (layout p) (geometry p) t 8 58 (.lit 0 1) s1 (ops.literal 0 1)
    (by rfl) (by simp [s1, setReg, advance])
  exact (source_step p ops t 56 (extra + 1) _ s s1 (by rfl) hp h1).trans
    (source_step p ops t 57 extra _ s1 (oldEntry ops t rowMaximum s) (by rfl)
      (by simp [s1, setReg, advance]) h2)

theorem old_tail_eq (p : Shape) (ops : Ops α) (t qi key extra : Nat) (previousMaximum previousMass : α)
    (s : State α) (hi : qi < 4) (hq : s.indices t 7 = some (qi : Int))
    (hk : s.indices t 5 = some (key : Int))
    (hr : key ≠ 0 → s.memory (privateCell t 0 qi) = some previousMaximum ∧
      s.memory (privateCell t 1 qi) = some previousMass) (hp : s.pc t = 58) :
    runLane ops (layout p) (geometry p) program t (extra + oldTailFuel key) s =
      runLane ops (layout p) (geometry p) program t extra (oldTail t qi key previousMaximum previousMass s) := by
  by_cases hz : key = 0
  · subst key
    have hg := LarkReduction.predicate_nlt_of (geometry p) t s (.const 0) (.ivar 5) 0 0 (by rfl) hk (by omega)
    have he := execute_branch_of ops (layout p) (geometry p) t 59 61 _ s false hg (by omega)
    exact source_step p ops t 58 extra _ s _ (by rfl) hp he
  · let s1 := advance s t 59
    let s2 := setReg (record s1 t (privateCell t 0 qi) false) t 7 previousMaximum 60
    have hg := LarkReduction.predicate_lt_of (geometry p) t s (.const 0) (.ivar 5) 0 (key : Int)
      (by rfl) hk (by omega)
    have h1 := execute_branch_of ops (layout p) (geometry p) t 59 61 _ s true hg (by omega)
    have h2 := execute_assign_of ops (layout p) (geometry p) t 7 60 (.load .local 0 (.ivar 7)) s1 _ previousMaximum
      (load_private p ops t 0 qi previousMaximum s1 (Or.inl rfl) hi hq (hr hz).1) (by simp [s1, advance])
    have h3 := execute_assign_of ops (layout p) (geometry p) t 8 61 (.load .local 1 (.ivar 7)) s2 _ previousMass
      (load_private p ops t 1 qi previousMass s2 (Or.inr rfl) hi hq (hr hz).2)
      (by simp [s2, setReg, advance])
    have e1 := source_step p ops t 58 (extra + 2) _ s s1 (by rfl) hp h1
    have e2 := source_step p ops t 59 (extra + 1) _ s1 s2 (by rfl) (by simp [s1, advance]) h2
    have he3 : execute ops (layout p) (geometry p) t (.assign 8 (.load .local 1 (.ivar 7))) s2 =
        some (oldTail t qi key previousMaximum previousMass s) := by
      simpa only [oldTail, if_neg hz] using h3
    have e3 := source_step p ops t 60 extra _ s2 (oldTail t qi key previousMaximum previousMass s) (by rfl)
      (by simp [s2, setReg, advance]) he3
    simpa only [oldTailFuel, if_neg hz] using e1.trans (e2.trans e3)

theorem old_selected_eq (p : Shape) (ops : Ops α) (t qi key extra : Nat)
    (rowMaximum previousMaximum previousMass : α) (s : State α) (hi : qi < 4)
    (hq : s.indices t 7 = some (qi : Int)) (hk : s.indices t 5 = some (key : Int))
    (hm : s.regs t 0 = some rowMaximum)
    (hr : key ≠ 0 → s.memory (privateCell t 0 qi) = some previousMaximum ∧
      s.memory (privateCell t 1 qi) = some previousMass) (hp : s.pc t = 56) :
    runLane ops (layout p) (geometry p) program t (extra + (2 + oldTailFuel key)) s =
      runLane ops (layout p) (geometry p) program t extra
        (oldSelected ops t qi key rowMaximum previousMaximum previousMass s) := by
  have hsteps : extra + (2 + oldTailFuel key) = (extra + oldTailFuel key) + 2 := by omega
  rw [hsteps, old_entry_eq p ops t (extra + oldTailFuel key) rowMaximum s hm hp]
  exact old_tail_eq p ops t qi key extra previousMaximum previousMass (oldEntry ops t rowMaximum s) hi hq hk hr
    (by simp [oldEntry, setReg, advance])

theorem old_selected_fields (ops : Ops α) (t qi key : Nat) (rowMaximum previousMaximum previousMass : α) (s : State α) :
    (oldSelected ops t qi key rowMaximum previousMaximum previousMass s).pc t = 61 ∧
    (oldSelected ops t qi key rowMaximum previousMaximum previousMass s).regs t 7 =
      some (selectedMaximum key rowMaximum previousMaximum) ∧
    (oldSelected ops t qi key rowMaximum previousMaximum previousMass s).regs t 8 =
      some (selectedMass ops key previousMass) := by
  by_cases hz : key = 0 <;> simp [oldSelected, oldTail, oldEntry, selectedMaximum, selectedMass, setReg, record, advance, hz]

theorem old_selected_frames (ops : Ops α) (t qi key : Nat) (rowMaximum previousMaximum previousMass : α) (s : State α) :
    (oldSelected ops t qi key rowMaximum previousMaximum previousMass s).indices = s.indices ∧
    (oldSelected ops t qi key rowMaximum previousMaximum previousMass s).epochs = s.epochs ∧
    (oldSelected ops t qi key rowMaximum previousMaximum previousMass s).memory = s.memory ∧
    (oldSelected ops t qi key rowMaximum previousMaximum previousMass s).regs t 0 = s.regs t 0 ∧
    (oldSelected ops t qi key rowMaximum previousMaximum previousMass s).regs t 5 = s.regs t 5 := by
  by_cases hz : key = 0 <;> simp [oldSelected, oldTail, oldEntry, setReg, record, advance, hz]

theorem old_tail_good (t qi key : Nat) (previousMaximum previousMass : α) (s : State α)
    (hg : TraceGood s) : TraceGood (oldTail t qi key previousMaximum previousMass s) := by
  by_cases hz : key = 0
  · simpa only [oldTail, if_pos hz, TraceGood] using hg
  · simp only [oldTail, if_neg hz]
    exact record_good _ t (privateCell t 1 qi) false
      (record_good (advance s t 59) t (privateCell t 0 qi) false hg
        (private_access_good t 0 qi false (s.epochs t))) (private_access_good t 1 qi false (s.epochs t))

theorem old_selected_good (ops : Ops α) (t qi key : Nat) (rowMaximum previousMaximum previousMass : α)
    (s : State α) (hg : TraceGood s) : TraceGood (oldSelected ops t qi key rowMaximum previousMaximum previousMass s) :=
  old_tail_good t qi key previousMaximum previousMass (oldEntry ops t rowMaximum s) hg

#print axioms old_selected_eq
#print axioms old_selected_fields
#print axioms old_selected_good
end LarkNativeAttention
