import Lark.NativeFlashInferRmsNormOutputBlock

/-! Complete actual native block execution from initialized read-only operands,
including both reductions, both barrier resumes and all output stores. Grid
composition and the canonical-real reference remain separate proof obligations.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def nativeBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  outputBlock p ops input row (outState p ops input row (midState p ops input row s))

theorem native_block_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row fuel.block s =
      some (nativeBlock p ops input row s) := by
  have hm := mid_ready p ops input row s entry
  have ho := out_ready p ops input row (midState p ops input row s) hm
  exact (block_first_eq p ops input row 2 s entry).trans
    ((block_second_eq p ops input row 1 (midState p ops input row s) hm).trans
      (output_block_run p ops input row 0 (outState p ops input row (midState p ops input row s)) ho))

theorem native_block_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid < 1024) :
    (nativeBlock p ops input row s).pc (row * 1024 + tid) = 67 :=
  output_block_pc p ops input row tid (outState p ops input row (midState p ops input row s)) ht

theorem native_block_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row col : Nat) (s : State α) (hc : col < 16384) :
    (nativeBlock p ops input row s).memory (globalCell 0 (address row col)) = some (outputResult ops input row col) :=
  output_block_value p ops input row col (outState p ops input row (midState p ops input row s)) hc

theorem output_block_input_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row col : Nat) (s : State α) (ready : OutReady p ops input row s) (hc : col < 16384) :
    (outputBlock p ops input row s).memory (globalCell 1 (address row col)) = some (input 1 (address row col)) :=
  (output_block_input p ops input row (address row col) s).trans (ready.cells col hc)

theorem native_block_input (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row col : Nat) (s : State α) (entry : BlockEntry p input row s) (hc : col < 16384) :
    (nativeBlock p ops input row s).memory (globalCell 1 (address row col)) = some (input 1 (address row col)) :=
  output_block_input_value p ops input row col (outState p ops input row (midState p ops input row s))
    (out_ready p ops input row (midState p ops input row s) (mid_ready p ops input row s entry)) hc

theorem native_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    ∀ a ∈ (nativeBlock p ops input row s).trace, Good a :=
  output_block_good p ops input row (outState p ops input row (midState p ops input row s))
    (out_ready p ops input row (midState p ops input row s) (mid_ready p ops input row s entry))

theorem native_block_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    raceFree (geometry p) (nativeBlock p ops input row s).trace = true :=
  race_free p _ (native_block_good p ops input row s entry)

theorem native_block_from_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    ∃ final,
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row fuel.block
        (initial p input outside) = some final ∧
      (∀ col, col < 16384 → final.memory (globalCell 0 (address row col)) = some (outputResult ops input row col)) ∧
      (∀ col, col < 16384 → final.memory (globalCell 1 (address row col)) = some (input 1 (address row col))) ∧
      (∀ tid, tid < 1024 → final.pc (row * 1024 + tid) = 67) ∧ raceFree (geometry p) final.trace = true := by
  let start := initial p input outside
  have entry := initial_block_entry p input outside row hr
  exact ⟨nativeBlock p ops input row start,native_block_run p ops input row start entry,
    (fun col hc => native_block_value p ops input row col start hc),
    (fun col hc => native_block_input p ops input row col start entry hc),
    (fun tid ht => native_block_pc p ops input row tid start ht),native_block_race_free p ops input row start entry⟩

#print axioms native_block_run
#print axioms native_block_pc
#print axioms native_block_value
#print axioms output_block_input_value
#print axioms native_block_input
#print axioms native_block_good
#print axioms native_block_race_free
#print axioms native_block_from_initial
end LarkNativeFlashInferRmsNorm
