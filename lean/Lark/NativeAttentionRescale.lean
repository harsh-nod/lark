import Lark.NativeAttentionOldState

/-! Exact online rescaling expressions, through output-column initialization. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

structure ScaleValues (α : Type) where
  maximum : α
  oldScale : α
  tileScale : α
  mass : α

def scaleValues (ops : Ops α) (rowMaximum rowMass oldMaximum oldMass : α) : ScaleValues α :=
  let maximum := ops.max oldMaximum rowMaximum
  let oldScale := ops.exp (ops.sub oldMaximum maximum)
  let tileScale := ops.exp (ops.sub rowMaximum maximum)
  ⟨maximum, oldScale, tileScale, ops.add (ops.mul oldScale oldMass) (ops.mul tileScale rowMass)⟩

structure ScaleReady (t : Nat) (scales : ScaleValues α) (oldMass : α) (s : State α) : Prop where
  previousMass : s.regs t 8 = some oldMass
  maximum : s.regs t 9 = some scales.maximum
  oldScale : s.regs t 10 = some scales.oldScale
  tileScale : s.regs t 11 = some scales.tileScale
  mass : s.regs t 12 = some scales.mass

theorem scales_of_regs (t : Nat) (scales : ScaleValues α) (oldMass : α) (s next : State α)
    (hr : ScaleReady t scales oldMass s) (he : next.regs = s.regs) : ScaleReady t scales oldMass next :=
  ⟨(congrArg (fun regs => regs t 8) he).trans hr.previousMass,
   (congrArg (fun regs => regs t 9) he).trans hr.maximum,
   (congrArg (fun regs => regs t 10) he).trans hr.oldScale,
   (congrArg (fun regs => regs t 11) he).trans hr.tileScale,
   (congrArg (fun regs => regs t 12) he).trans hr.mass⟩

def rescaled (ops : Ops α) (t : Nat) (rowMaximum rowMass oldMaximum oldMass : α) (s : State α) : State α :=
  let values := scaleValues ops rowMaximum rowMass oldMaximum oldMass
  let s := setReg s t 9 values.maximum 62
  let s := setReg s t 10 values.oldScale 63
  let s := setReg s t 11 values.tileScale 64
  let s := setReg s t 12 values.mass 65
  setIndex s t 12 0 66

theorem rescale_eq (p : Shape) (ops : Ops α) (t extra : Nat) (rowMaximum rowMass oldMaximum oldMass : α)
    (s : State α) (hm : s.regs t 0 = some rowMaximum) (hl : s.regs t 5 = some rowMass)
    (hom : s.regs t 7 = some oldMaximum) (hol : s.regs t 8 = some oldMass) (hp : s.pc t = 61) :
    runLane ops (layout p) (geometry p) program t (extra + 5) s =
      runLane ops (layout p) (geometry p) program t extra (rescaled ops t rowMaximum rowMass oldMaximum oldMass s) := by
  let values := scaleValues ops rowMaximum rowMass oldMaximum oldMass
  let s1 := setReg s t 9 values.maximum 62
  let s2 := setReg s1 t 10 values.oldScale 63
  let s3 := setReg s2 t 11 values.tileScale 64
  let s4 := setReg s3 t 12 values.mass 65
  have h1 := execute_pure_of ops (layout p) (geometry p) t 9 62 (.bin .max (.reg 7) (.reg 0)) s values.maximum
    (by simp [evalExpr, applyBinary, values, scaleValues, hom, hm]) (by omega)
  have h2 := execute_pure_of ops (layout p) (geometry p) t 10 63 (.un .exp (.bin .sub (.reg 7) (.reg 9))) s1 values.oldScale
    (by simp [evalExpr, applyBinary, applyUnary, values, scaleValues, s1, setReg, advance, hom])
    (by simp [s1, setReg, advance])
  have h3 := execute_pure_of ops (layout p) (geometry p) t 11 64 (.un .exp (.bin .sub (.reg 0) (.reg 9))) s2 values.tileScale
    (by simp [evalExpr, applyBinary, applyUnary, values, scaleValues, s2, s1, setReg, advance, hm])
    (by simp [s2, setReg, advance])
  have h4 := execute_pure_of ops (layout p) (geometry p) t 12 65
    (.bin .add (.bin .mul (.reg 10) (.reg 8)) (.bin .mul (.reg 11) (.reg 5))) s3 values.mass
    (by simp [evalExpr, applyBinary, values, scaleValues, s3, s2, s1, setReg, advance, hol, hl])
    (by simp [s3, setReg, advance])
  have h5 := execute_index_of ops (layout p) (geometry p) t 12 66 (.const 0) s4 0 (by rfl)
    (by simp [s4, setReg, advance])
  have e1 := source_step p ops t 61 (extra + 4) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 62 (extra + 3) _ s1 s2 (by rfl) (by simp [s1, setReg, advance]) h2
  have e3 := source_step p ops t 63 (extra + 2) _ s2 s3 (by rfl) (by simp [s2, setReg, advance]) h3
  have e4 := source_step p ops t 64 (extra + 1) _ s3 s4 (by rfl) (by simp [s3, setReg, advance]) h4
  have e5 := source_step p ops t 65 extra _ s4 (rescaled ops t rowMaximum rowMass oldMaximum oldMass s) (by rfl)
    (by simp [s4, setReg, advance]) h5
  exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

theorem rescaled_fields (ops : Ops α) (t : Nat) (rowMaximum rowMass oldMaximum oldMass : α) (s : State α) :
    (rescaled ops t rowMaximum rowMass oldMaximum oldMass s).pc t = 66 ∧
    (rescaled ops t rowMaximum rowMass oldMaximum oldMass s).indices t 12 = some 0 ∧
    (rescaled ops t rowMaximum rowMass oldMaximum oldMass s).regs t 9 = some (scaleValues ops rowMaximum rowMass oldMaximum oldMass).maximum ∧
    (rescaled ops t rowMaximum rowMass oldMaximum oldMass s).regs t 10 = some (scaleValues ops rowMaximum rowMass oldMaximum oldMass).oldScale ∧
    (rescaled ops t rowMaximum rowMass oldMaximum oldMass s).regs t 11 = some (scaleValues ops rowMaximum rowMass oldMaximum oldMass).tileScale ∧
    (rescaled ops t rowMaximum rowMass oldMaximum oldMass s).regs t 12 = some (scaleValues ops rowMaximum rowMass oldMaximum oldMass).mass := by
  simp [rescaled, setReg, setIndex, advance]

theorem rescaled_index (ops : Ops α) (t r : Nat) (rowMaximum rowMass oldMaximum oldMass : α)
    (s : State α) (hr : r ≠ 12) :
    (rescaled ops t rowMaximum rowMass oldMaximum oldMass s).indices t r = s.indices t r := by
  simp [rescaled, setReg, setIndex, advance, hr]

theorem rescaled_reg (ops : Ops α) (t r : Nat) (rowMaximum rowMass oldMaximum oldMass : α)
    (s : State α) (h9 : r ≠ 9) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) :
    (rescaled ops t rowMaximum rowMass oldMaximum oldMass s).regs t r = s.regs t r := by
  simp [rescaled, setReg, setIndex, advance, h9, h10, h11, h12]

theorem rescaled_ready (ops : Ops α) (t : Nat) (rowMaximum rowMass oldMaximum oldMass : α)
    (s : State α) (hl : s.regs t 8 = some oldMass) :
    ScaleReady t (scaleValues ops rowMaximum rowMass oldMaximum oldMass) oldMass
      (rescaled ops t rowMaximum rowMass oldMaximum oldMass s) := by
  have hf := rescaled_fields ops t rowMaximum rowMass oldMaximum oldMass s
  exact ⟨(rescaled_reg ops t 8 rowMaximum rowMass oldMaximum oldMass s (by decide) (by decide) (by decide) (by decide)).trans hl,
    hf.2.2.1, hf.2.2.2.1, hf.2.2.2.2.1, hf.2.2.2.2.2⟩

theorem rescaled_frames (ops : Ops α) (t : Nat) (rowMaximum rowMass oldMaximum oldMass : α) (s : State α) :
    (rescaled ops t rowMaximum rowMass oldMaximum oldMass s).epochs = s.epochs ∧
    (rescaled ops t rowMaximum rowMass oldMaximum oldMass s).memory = s.memory ∧
    (rescaled ops t rowMaximum rowMass oldMaximum oldMass s).trace = s.trace := by
  exact ⟨rfl, rfl, rfl⟩

#print axioms rescale_eq
#print axioms rescaled_ready
end LarkNativeAttention
