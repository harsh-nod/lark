import Lark.NativeAttentionQueryWeights

/-! Source-ordered online values and a complete row output update. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

structure QueryValue (α : Type) where
  maximum : α
  mass : α
  stored : Nat → α

def queryScales (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α) : ScaleValues α :=
  outputScales ops key (tileMaximum ops input t qi key) (tileDenominator ops input t qi key) old.maximum old.mass
def nextQueryValue (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α) : QueryValue α :=
  let scales := queryScales ops input t qi key old
  ⟨scales.maximum, scales.mass,
    outputValues ops input t key (rowWeightValues ops input t qi key) scales (selectedMass ops key old.mass) old.stored⟩
def OldQuery (t qi key : Nat) (old : QueryValue α) (s : State α) : Prop :=
  OutputRange t qi old.stored 0 256 s ∧
    (key ≠ 0 → s.memory (privateCell t 0 qi) = some old.maximum ∧ s.memory (privateCell t 1 qi) = some old.mass)
def rowOutput (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α) (s : State α) : State α :=
  outputUpdated ops input t qi key (rowWeightValues ops input t qi key)
    (tileMaximum ops input t qi key) (tileDenominator ops input t qi key) old.maximum old.mass old.stored
    (rowWeights ops input t qi key s)
theorem row_output_state (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α) (s : State α) :
    rowOutput ops input t qi key old s =
      outputUpdated ops input t qi key (rowWeightValues ops input t qi key)
        (tileMaximum ops input t qi key) (tileDenominator ops input t qi key) old.maximum old.mass old.stored
        (rowWeights ops input t qi key s) := rfl

theorem row_output_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key extra : Nat) (old : QueryValue α)
    (s : State α) (ht : t < p.groups * 32) (hi : qi < 4) (hr : Reads p input s) (hn : NativeIndices t s)
    (hk : Tiles ops input t key s) (hq : s.indices t 7 = some (qi : Int)) (hj : s.indices t 5 = some (key : Int))
    (ho : OldQuery t qi key old s) (hp : s.pc t = 22) :
    runLane ops (layout p) (geometry p) program t (extra + (119058 + oldTailFuel key)) s =
      runLane ops (layout p) (geometry p) program t extra (rowOutput ops input t qi key old s) := by
  let next := rowWeights ops input t qi key s
  have fields := row_weights_fields ops input t qi key s
  have globalFrame := fun b i => row_weights_memory_other ops input t qi key s (globalCell b i)
    (by intro c hc; simp [globalCell, sharedCell]) (by intro r hr; simp [globalCell, sharedCell])
  have privateFrame := fun b => row_weights_memory_other ops input t qi key s (privateCell t b qi)
    (by intro c hc; simp [privateCell, sharedCell]) (by intro r hr; simp [privateCell, sharedCell])
  have old' : OldQuery t qi key old next := by
    constructor
    · intro c hc hb
      exact (globalFrame 0 (globalAddress t qi c)).trans (ho.1 c hc hb)
    · intro hj
      exact ⟨(privateFrame 0).trans (ho.2 hj).1, (privateFrame 1).trans (ho.2 hj).2⟩
  have h1 := row_weights_eq p ops input t qi key (extra + (60168 + oldTailFuel key)) s ht hi hr hn hk hq hp
  have h2 := output_update_eq p ops input t qi key extra (rowWeightValues ops input t qi key)
    (tileMaximum ops input t qi key) (tileDenominator ops input t qi key) old.maximum old.mass old.stored next ht hi
    (row_weights_values ops input t qi key s) (row_weights_tiles ops input t qi key s hk)
    (row_weights_native ops input t qi key s hn)
    ((row_weights_index ops input t qi key 7 s (by decide) (by decide) (by decide) (by decide)).trans hq)
    ((row_weights_index ops input t qi key 5 s (by decide) (by decide) (by decide) (by decide)).trans hj)
    fields.2.1 fields.2.2.1 old'.2 old'.1 fields.1
  have steps : extra + (119058 + oldTailFuel key) = (extra + (60168 + oldTailFuel key)) + 58890 := by omega
  exact (congrArg (fun n => runLane ops (layout p) (geometry p) program t n s) steps).trans (h1.trans h2)

theorem row_output_fields (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α) (s : State α) :
    (rowOutput ops input t qi key old s).pc t = 83 ∧ (rowOutput ops input t qi key old s).epochs = s.epochs := by
  have hs := row_output_state ops input t qi key old s
  have hf := output_updated_fields ops input t qi key (rowWeightValues ops input t qi key)
    (tileMaximum ops input t qi key) (tileDenominator ops input t qi key) old.maximum old.mass old.stored (rowWeights ops input t qi key s)
  exact ⟨(congrArg (fun state : State α => state.pc t) hs).trans hf.1,
    (congrArg (fun state : State α => state.epochs) hs).trans (hf.2.trans (row_weights_fields ops input t qi key s).2.2.2)⟩

theorem row_output_value (ops : Ops α) (input : Nat → Nat → α) (t qi key col : Nat) (old : QueryValue α) (s : State α)
    (hc : col < 256) :
    (rowOutput ops input t qi key old s).memory (globalCell 0 (globalAddress t qi col)) =
      some ((nextQueryValue ops input t qi key old).stored col) :=
  (congrArg (fun state : State α => state.memory (globalCell 0 (globalAddress t qi col))) (row_output_state ops input t qi key old s)).trans
    (output_updated_value ops input t qi key col (rowWeightValues ops input t qi key)
      (tileMaximum ops input t qi key) (tileDenominator ops input t qi key) old.maximum old.mass old.stored _ hc)

theorem row_output_scales (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α) (s : State α) :
    ScaleReady t (queryScales ops input t qi key old) (selectedMass ops key old.mass) (rowOutput ops input t qi key old s) :=
  Eq.mpr (congrArg (ScaleReady t (queryScales ops input t qi key old) (selectedMass ops key old.mass))
    (row_output_state ops input t qi key old s))
    (output_updated_scales ops input t qi key (rowWeightValues ops input t qi key)
      (tileMaximum ops input t qi key) (tileDenominator ops input t qi key) old.maximum old.mass old.stored _)

theorem row_output_index (ops : Ops α) (input : Nat → Nat → α) (t qi key r : Nat) (old : QueryValue α) (s : State α)
    (h8 : r ≠ 8) (h9 : r ≠ 9) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) (h13 : r ≠ 13) :
    (rowOutput ops input t qi key old s).indices t r = s.indices t r :=
  (congrArg (fun state : State α => state.indices t r) (row_output_state ops input t qi key old s)).trans
    ((output_updated_index ops input t qi key r (rowWeightValues ops input t qi key)
      (tileMaximum ops input t qi key) (tileDenominator ops input t qi key) old.maximum old.mass old.stored _ h12 h13).trans
      (row_weights_index ops input t qi key r s h8 h9 h10 h11))

theorem row_output_memory_other (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α) (s : State α) (l : Location)
    (hq : ∀ c, c < 256 → l ≠ sharedCell t 0 (sharedAddress t c))
    (hs : ∀ r, r < 32 → l ≠ sharedCell t 3 (scoreAddress t r))
    (ho : ∀ c, c < 256 → l ≠ globalCell 0 (globalAddress t qi c)) :
    (rowOutput ops input t qi key old s).memory l = s.memory l :=
  (congrArg (fun state : State α => state.memory l) (row_output_state ops input t qi key old s)).trans
    ((output_updated_memory_other ops input t qi key (rowWeightValues ops input t qi key)
      (tileMaximum ops input t qi key) (tileDenominator ops input t qi key) old.maximum old.mass old.stored _ l ho).trans
      (row_weights_memory_other ops input t qi key s l hq hs))

theorem row_output_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α)
    (s : State α) (hr : Reads p input s) : Reads p input (rowOutput ops input t qi key old s) :=
  Eq.mpr (congrArg (Reads p input) (row_output_state ops input t qi key old s))
    (output_updated_reads p ops input t qi key (rowWeightValues ops input t qi key)
      (tileMaximum ops input t qi key) (tileDenominator ops input t qi key) old.maximum old.mass old.stored _
      (row_weights_reads p ops input t qi key s hr))

theorem row_output_good (ops : Ops α) (input : Nat → Nat → α) (t qi key : Nat) (old : QueryValue α)
    (s : State α) (hi : qi < 4) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) : TraceGood (rowOutput ops input t qi key old s) := by
  have he' : ((rowWeights ops input t qi key s).epochs t).block % 2 = 1 := by
    rw [(row_weights_fields ops input t qi key s).2.2.2]
    exact he
  exact Eq.mpr (congrArg TraceGood (row_output_state ops input t qi key old s))
    (output_updated_good ops input t qi key (rowWeightValues ops input t qi key)
      (tileMaximum ops input t qi key) (tileDenominator ops input t qi key) old.maximum old.mass old.stored _ hi he'
      (row_weights_good ops input t qi key s he hg))

#print axioms row_output_eq
#print axioms row_output_value
#print axioms row_output_scales
#print axioms row_output_memory_other
#print axioms row_output_good
end LarkNativeAttention
