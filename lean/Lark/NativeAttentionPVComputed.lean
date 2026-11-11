import Lark.NativeAttentionOutputFinish

/-! Actual PV initialization and the complete dot product for one output column. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def pvEntry (ops : Ops α) (t : Nat) (s : State α) : State α :=
  setIndex (setReg s t 13 (ops.literal 0 1) 68) t 13 0 69
def pvValue (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α) : α :=
  pvFold ops input t key col weights 0 32 (ops.literal 0 1)
def pvComputed (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α) (s : State α) : State α :=
  pvRows ops input t key col weights 0 32 (ops.literal 0 1) (pvEntry ops t s)

theorem pv_computed_state (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α) (s : State α) :
    pvComputed ops input t key col weights s = pvRows ops input t key col weights 0 32 (ops.literal 0 1) (pvEntry ops t s) := rfl

theorem pv_entry_fields (ops : Ops α) (t : Nat) (s : State α) :
    (pvEntry ops t s).pc t = 69 ∧ (pvEntry ops t s).indices t 13 = some 0 ∧
    (pvEntry ops t s).regs t 13 = some (ops.literal 0 1) := by simp [pvEntry, setReg, setIndex, advance]

theorem pv_entry_native (ops : Ops α) (t : Nat) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (pvEntry ops t s) := indices_set (setReg s t 13 (ops.literal 0 1) 68) t 13 69 0 (by decide) hn

theorem pv_entry_scales (ops : Ops α) (t : Nat) (scales : ScaleValues α) (oldMass : α)
    (s : State α) (hr : ScaleReady t scales oldMass s) : ScaleReady t scales oldMass (pvEntry ops t s) := by
  constructor
  · simpa [pvEntry, setReg, setIndex, advance] using hr.previousMass
  · simpa [pvEntry, setReg, setIndex, advance] using hr.maximum
  · simpa [pvEntry, setReg, setIndex, advance] using hr.oldScale
  · simpa [pvEntry, setReg, setIndex, advance] using hr.tileScale
  · simpa [pvEntry, setReg, setIndex, advance] using hr.mass

theorem pv_computation_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t key col extra : Nat)
    (weights : Nat → α) (s : State α) (hc : col < 256) (hw : ScoreRange t weights 0 32 s)
    (hk : Tiles ops input t key s) (hn : NativeIndices t s) (hcol : s.indices t 12 = some (col : Int)) (hp : s.pc t = 67) :
    runLane ops (layout p) (geometry p) program t (extra + 227) s =
      runLane ops (layout p) (geometry p) program t extra (pvComputed ops input t key col weights s) := by
  let s1 := setReg s t 13 (ops.literal 0 1) 68
  let s2 := pvEntry ops t s
  have h1 := execute_pure_of ops (layout p) (geometry p) t 13 68 (.lit 0 1) s (ops.literal 0 1) (by rfl) (by omega)
  have h2 := execute_index_of ops (layout p) (geometry p) t 13 69 (.const 0) s1 0 (by rfl)
    (by simp [s1, setReg, advance])
  have hf := pv_entry_fields ops t s
  have hcol2 : s2.indices t 12 = some (col : Int) := by simpa [s2, pvEntry, setReg, setIndex, advance] using hcol
  have e1 := source_step p ops t 67 (extra + 226) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 68 (extra + 225) _ s1 s2 (by rfl) (by simp [s1, setReg, advance]) h2
  have e3 := pv_rows_eq p ops input t key col weights 0 32 extra (ops.literal 0 1) s2 (by decide) hc hw hk
    (pv_entry_native ops t s hn) hf.2.1 hcol2 hf.2.2 hf.1
  exact e1.trans (e2.trans e3)

theorem pv_computed_fields (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α) (s : State α) :
    (pvComputed ops input t key col weights s).pc t = 76 ∧
    (pvComputed ops input t key col weights s).regs t 13 = some (pvValue ops input t key col weights) ∧
    (pvComputed ops input t key col weights s).epochs = s.epochs ∧
    (pvComputed ops input t key col weights s).memory = s.memory := by
  have hs := pv_computed_state ops input t key col weights s
  have hf := pv_rows_fields ops input t key col weights 0 32 (ops.literal 0 1) (pvEntry ops t s)
  have hv := pv_rows_value ops input t key col weights 0 32 (ops.literal 0 1) (pvEntry ops t s) (pv_entry_fields ops t s).2.2
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.regs t 13) hs).trans hv,
    (congrArg (fun state : State α => state.epochs) hs).trans hf.2.1,
    (congrArg (fun state : State α => state.memory) hs).trans hf.2.2⟩

theorem pv_computed_index (ops : Ops α) (input : Nat → Nat → α) (t key col r : Nat) (weights : Nat → α)
    (s : State α) (hr : r ≠ 13) : (pvComputed ops input t key col weights s).indices t r = s.indices t r := by
  have hs := pv_computed_state ops input t key col weights s
  have h := pv_rows_index ops input t key col weights 0 32 r (ops.literal 0 1) (pvEntry ops t s) hr
  have he : (pvEntry ops t s).indices t r = s.indices t r := by simp [pvEntry, setReg, setIndex, advance, hr]
  exact (congrArg (fun state : State α => state.indices t r) hs).trans (h.trans he)

theorem pv_computed_native (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (pvComputed ops input t key col weights s) :=
  Eq.mpr (congrArg (NativeIndices t) (pv_computed_state ops input t key col weights s))
    (pv_rows_native ops input t key col weights 0 32 (ops.literal 0 1) _ (pv_entry_native ops t s hn))

theorem pv_computed_scales (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α)
    (scales : ScaleValues α) (oldMass : α) (s : State α) (hr : ScaleReady t scales oldMass s) :
    ScaleReady t scales oldMass (pvComputed ops input t key col weights s) :=
  Eq.mpr (congrArg (ScaleReady t scales oldMass) (pv_computed_state ops input t key col weights s))
    (pv_rows_scales ops input t key col weights 0 32 (ops.literal 0 1) oldMass scales _ (pv_entry_scales ops t scales oldMass s hr))

theorem pv_computed_good (ops : Ops α) (input : Nat → Nat → α) (t key col : Nat) (weights : Nat → α)
    (s : State α) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (pvComputed ops input t key col weights s) :=
  Eq.mpr (congrArg TraceGood (pv_computed_state ops input t key col weights s))
    (pv_rows_good ops input t key col weights 0 32 (ops.literal 0 1) (pvEntry ops t s) (by decide) he hg)

#print axioms pv_computation_eq
#print axioms pv_computed_fields
#print axioms pv_computed_good
end LarkNativeAttention
