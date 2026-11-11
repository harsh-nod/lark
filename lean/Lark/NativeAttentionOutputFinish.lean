import Lark.NativeAttentionOutputValue

/-! Seven actual source instructions finish one output-column update. Explicit
half conversions and the source's old-mass multiplication order are retained. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def outputFinish (ops : Ops α) (t qi col : Nat) (scales : ScaleValues α) (oldMass oldStored pv : α)
    (s : State α) : State α :=
  let s := setReg (record s t (globalCell 0 (globalAddress t qi col)) false) t 17 (ops.fromHalf oldStored) 77
  let s := setReg s t 18 (oldContribution ops scales oldMass oldStored) 78
  let s := setReg s t 19 (newContribution ops scales pv) 79
  let s := setReg s t 20 (combinedOutput ops scales oldMass oldStored pv) 80
  let s := storeState s t (globalCell 0 (globalAddress t qi col)) (storedOutput ops scales oldMass oldStored pv) 81
  advance (setIndex s t 12 ((col + 1 : Nat) : Int) 82) t 66

theorem output_finish_eq (p : Shape) (ops : Ops α) (t qi col extra : Nat) (scales : ScaleValues α)
    (oldMass oldStored pv : α) (s : State α) (ht : t < p.groups * 32) (hi : qi < 4) (hc : col < 256)
    (hn : NativeIndices t s) (hq : s.indices t 7 = some (qi : Int)) (hcol : s.indices t 12 = some (col : Int))
    (hr : ScaleReady t scales oldMass s) (hpv : s.regs t 13 = some pv)
    (ho : s.memory (globalCell 0 (globalAddress t qi col)) = some oldStored) (hp : s.pc t = 76) :
    runLane ops (layout p) (geometry p) program t (extra + 7) s =
      runLane ops (layout p) (geometry p) program t extra (outputFinish ops t qi col scales oldMass oldStored pv s) := by
  let s1 := setReg (record s t (globalCell 0 (globalAddress t qi col)) false) t 17 (ops.fromHalf oldStored) 77
  let s2 := setReg s1 t 18 (oldContribution ops scales oldMass oldStored) 78
  let s3 := setReg s2 t 19 (newContribution ops scales pv) 79
  let s4 := setReg s3 t 20 (combinedOutput ops scales oldMass oldStored pv) 80
  let s5 := storeState s4 t (globalCell 0 (globalAddress t qi col)) (storedOutput ops scales oldMass oldStored pv) 81
  let s6 := setIndex s5 t 12 ((col + 1 : Nat) : Int) 82
  have h1 := execute_assign_of ops (layout p) (geometry p) t 17 77
    (.un .fromHalf (.load .global 0 (globalIndex 7 12))) s _ _
    (load_old_output p ops t qi col oldStored s ht hi hc hn hq hcol ho) (by omega)
  have h2 := execute_pure_of ops (layout p) (geometry p) t 18 78
    (.bin .mul (.bin .mul (.reg 8) (.reg 10)) (.reg 17)) s1 (oldContribution ops scales oldMass oldStored)
    (by simp [evalExpr, applyBinary, oldContribution, s1, setReg, advance, record, hr.previousMass, hr.oldScale])
    (by simp [s1, setReg, advance])
  have h3 := execute_pure_of ops (layout p) (geometry p) t 19 79 (.bin .mul (.reg 11) (.reg 13)) s2
    (newContribution ops scales pv)
    (by simp [evalExpr, applyBinary, newContribution, s2, s1, setReg, advance, record, hr.tileScale, hpv])
    (by simp [s2, setReg, advance])
  have h4 := execute_pure_of ops (layout p) (geometry p) t 20 80
    (.bin .mul (.bin .div (.lit 1 1) (.reg 12)) (.bin .add (.reg 18) (.reg 19))) s3
    (combinedOutput ops scales oldMass oldStored pv)
    (by simp [evalExpr, applyBinary, combinedOutput, s3, s2, s1, setReg, advance, record, hr.mass])
    (by simp [s3, setReg, advance])
  have h5 := output_store_eq p ops t qi col (combinedOutput ops scales oldMass oldStored pv) s4 ht hi hc hn hq hcol
    (by simp [s4, setReg, advance]) (by simp [s4, setReg, advance])
  have he6 := eval_counter (geometry p) t 12 col s5 hcol (by omega)
  have h6 := execute_index_of ops (layout p) (geometry p) t 12 82 (.add (.ivar 12) (.const 1)) s5
    ((col + 1 : Nat) : Int) he6 (by simp [s5, storeState, advance])
  have e1 := source_step p ops t 76 (extra + 6) _ s s1 old_output_read_code hp h1
  have e2 := source_step p ops t 77 (extra + 5) _ s1 s2 (by rfl) (by simp [s1, setReg, advance]) h2
  have e3 := source_step p ops t 78 (extra + 4) _ s2 s3 (by rfl) (by simp [s2, setReg, advance]) h3
  have e4 := source_step p ops t 79 (extra + 3) _ s3 s4 (by rfl) (by simp [s3, setReg, advance]) h4
  have e5 := source_step p ops t 80 (extra + 2) _ s4 s5 output_store_code (by simp [s4, setReg, advance]) h5
  have e6 := source_step p ops t 81 (extra + 1) _ s5 s6 (by rfl) (by simp [s5, storeState, advance]) h6
  have e7 := source_step p ops t 82 extra (.jump 66) s6 (outputFinish ops t qi col scales oldMass oldStored pv s)
    (by rfl) (by simp [s6, setIndex, advance]) (by rfl)
  exact e1.trans (e2.trans (e3.trans (e4.trans (e5.trans (e6.trans e7)))))

theorem output_finish_fields (ops : Ops α) (t qi col : Nat) (scales : ScaleValues α) (oldMass oldStored pv : α)
    (s : State α) : (outputFinish ops t qi col scales oldMass oldStored pv s).pc t = 66 ∧
    (outputFinish ops t qi col scales oldMass oldStored pv s).indices t 12 = some ((col + 1 : Nat) : Int) ∧
    (outputFinish ops t qi col scales oldMass oldStored pv s).epochs = s.epochs := by
  simp [outputFinish, storeState, setReg, setIndex, record, advance]

theorem output_finish_index (ops : Ops α) (t qi col r : Nat) (scales : ScaleValues α) (oldMass oldStored pv : α)
    (s : State α) (hr : r ≠ 12) :
    (outputFinish ops t qi col scales oldMass oldStored pv s).indices t r = s.indices t r := by
  simp [outputFinish, storeState, setReg, setIndex, record, advance, hr]

theorem output_finish_reg (ops : Ops α) (t qi col r : Nat) (scales : ScaleValues α) (oldMass oldStored pv : α)
    (s : State α) (h17 : r ≠ 17) (h18 : r ≠ 18) (h19 : r ≠ 19) (h20 : r ≠ 20) :
    (outputFinish ops t qi col scales oldMass oldStored pv s).regs t r = s.regs t r := by
  simp [outputFinish, storeState, setReg, setIndex, record, advance, h17, h18, h19, h20]

theorem output_finish_memory (ops : Ops α) (t qi col : Nat) (scales : ScaleValues α) (oldMass oldStored pv : α)
    (s : State α) (l : Location) : (outputFinish ops t qi col scales oldMass oldStored pv s).memory l =
      if l = globalCell 0 (globalAddress t qi col) then some (storedOutput ops scales oldMass oldStored pv) else s.memory l := rfl

theorem output_finish_good (ops : Ops α) (t qi col : Nat) (scales : ScaleValues α) (oldMass oldStored pv : α)
    (s : State α) (hi : qi < 4) (hc : col < 256) (hg : TraceGood s) :
    TraceGood (outputFinish ops t qi col scales oldMass oldStored pv s) := by
  exact store_good _ t (globalCell 0 (globalAddress t qi col)) (storedOutput ops scales oldMass oldStored pv) 81
    (record_good s t (globalCell 0 (globalAddress t qi col)) false hg (output_access_good t qi col false (s.epochs t) hi hc))
    (output_access_good t qi col true (s.epochs t) hi hc)

#print axioms output_finish_eq
#print axioms output_finish_memory
#print axioms output_finish_good
end LarkNativeAttention
