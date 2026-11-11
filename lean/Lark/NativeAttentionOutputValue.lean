import Lark.NativeAttentionPVRows

/-! The actual old-output load and converted output store, with checked global
addresses and the precise source parenthesization of the online update. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def oldContribution (ops : Ops α) (scales : ScaleValues α) (oldMass oldStored : α) : α :=
  ops.mul (ops.mul oldMass scales.oldScale) (ops.fromHalf oldStored)
def newContribution (ops : Ops α) (scales : ScaleValues α) (pv : α) : α := ops.mul scales.tileScale pv
def combinedOutput (ops : Ops α) (scales : ScaleValues α) (oldMass oldStored pv : α) : α :=
  ops.mul (ops.div (ops.literal 1 1) scales.mass)
    (ops.add (oldContribution ops scales oldMass oldStored) (newContribution ops scales pv))
def storedOutput (ops : Ops α) (scales : ScaleValues α) (oldMass oldStored pv : α) : α :=
  ops.toHalf (combinedOutput ops scales oldMass oldStored pv)

theorem old_output_read_code : program[76]? = some
    (.assign 17 (.un .fromHalf (.load .global 0 (globalIndex 7 12)))) := rfl
theorem output_store_code : program[80]? = some
    (.store .global 0 (globalIndex 7 12) (.un .toHalf (.reg 20))) := rfl

theorem load_old_output (p : Shape) (ops : Ops α) (t qi col : Nat) (oldStored : α) (s : State α)
    (ht : t < p.groups * 32) (hi : qi < 4) (hc : col < 256) (hn : NativeIndices t s)
    (hq : s.indices t 7 = some (qi : Int)) (hcol : s.indices t 12 = some (col : Int))
    (hv : s.memory (globalCell 0 (globalAddress t qi col)) = some oldStored) :
    evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .global 0 (globalIndex 7 12))) s =
      some (ops.fromHalf oldStored, record s t (globalCell 0 (globalAddress t qi col)) false) :=
  eval_from_half_load_of ops (layout p) (geometry p) t 0 (globalIndex 7 12) s (globalAddress t qi col) _ oldStored
    (eval_global_index p t qi col 7 12 s ht hi hc hn hq hcol)
    (output_location p t _ false (global_address_bound p t qi col ht hi hc)) hv

theorem output_store_eq (p : Shape) (ops : Ops α) (t qi col : Nat) (value : α) (s : State α)
    (ht : t < p.groups * 32) (hi : qi < 4) (hc : col < 256) (hn : NativeIndices t s)
    (hq : s.indices t 7 = some (qi : Int)) (hcol : s.indices t 12 = some (col : Int))
    (hv : s.regs t 20 = some value) (hp : s.pc t = 80) :
    execute ops (layout p) (geometry p) t (.store .global 0 (globalIndex 7 12) (.un .toHalf (.reg 20))) s =
      some (storeState s t (globalCell 0 (globalAddress t qi col)) (ops.toHalf value) 81) :=
  execute_store_of ops (layout p) (geometry p) t 81 .global 0 (globalIndex 7 12) (.un .toHalf (.reg 20)) s s
    (globalAddress t qi col) _ _ (eval_global_index p t qi col 7 12 s ht hi hc hn hq hcol)
    (output_location p t _ true (global_address_bound p t qi col ht hi hc))
    (by simp [evalExpr, applyUnary, hv]) (by omega)

#print axioms load_old_output
#print axioms output_store_eq
end LarkNativeAttention
