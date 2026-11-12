"""Fresh complete native split-half physical-wave execution and output checks.

The new source-bound theorems cover both real warp fences and all rotary
snapshots/stores. Split-half whole-grid and dense-reference proofs remain open.
"""

import argparse
from pathlib import Path

import check_execution_prefix as prefix

TARGET = "Lark.NativeQKNormRopeSplitWave"


def statement(text, contract):
    body = prefix.source_statement(text, contract).replace("import " + prefix.TARGET, "import " + TARGET)
    if contract.rotary_layout != "split-half":
        return body
    return body + '''
theorem source_split_wave (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) (hb : block < sourceShape.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads sourceShape input s) :
    LarkPartitionCollective.runWarp ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram
      (warpThreads (geometry sourceShape) block warp) fuel.warp s = some (splitWaveState sourceShape ops input block warp s) := by
  simpa only [source_binding.1, sourceNeox] using native_split_wave sourceShape ops input block warp s hb hw hp hr
theorem source_split_wave_value (ops : Ops α) (input : Nat → Nat → α)
    (block warp lane e : Nat) (s : State α) (hl : lane < 64) (he : e < 4) :
    let t := cohortBase block warp + lane
    (splitWaveState sourceShape ops input block warp s).memory (globalCell 0 (outputAddress t e)) =
      some (ops.toHalf (splitWaveResult ops input block warp t e)) :=
  split_wave_value sourceShape ops input block warp lane e s hl he
theorem source_split_wave_readonly (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) (hr : Reads sourceShape input s) :
    Reads sourceShape input (splitWaveState sourceShape ops input block warp s) :=
  split_wave_reads sourceShape ops input block warp s hr
theorem source_split_wave_trace (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) :
    (splitWaveState sourceShape ops input block warp s).trace.length = s.trace.length + 1280 :=
  split_wave_trace_length sourceShape ops input block warp s
theorem source_split_wave_access_classification (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (splitWaveState sourceShape ops input block warp s).trace, Good access :=
  split_wave_good sourceShape ops input block warp s good
theorem source_split_wave_race_free (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (block warp : Nat) :
    raceFree (geometry sourceShape)
      (splitWaveState sourceShape ops input block warp (initial (layout sourceShape) input outside)).trace = true :=
  split_wave_initial_race_free sourceShape ops input outside block warp
theorem source_split_wave_epochs (ops : Ops α) (input : Nat → Nat → α)
    (block warp lane : Nat) (s : State α) (hl : lane < 64) :
    let t := cohortBase block warp + lane
    ((splitWaveState sourceShape ops input block warp s).epochs t).block = (s.epochs t).block ∧
    ((splitWaveState sourceShape ops input block warp s).epochs t).warp = (s.epochs t).warp + 2 :=
  split_wave_epoch sourceShape ops input block warp lane s hl
#print axioms source_split_wave_epochs
#print axioms source_split_wave
#print axioms source_split_wave_value
#print axioms source_split_wave_readonly
#print axioms source_split_wave_trace
#print axioms source_split_wave_access_classification
#print axioms source_split_wave_race_free
'''


def controls(contracts):
    text, contract = contracts["split-half"]
    replacements = {
        "wrong-last-output-register": ("output[out3] = __float2half(o3);", "output[out3] = __float2half(o2);"),
        "wrong-partner-sign": ("p0 = -p0;", "p0 = p0;"),
        "widened-rotary-shuffle": ("__shfl_xor(n0, 16, 32)", "__shfl_xor(n0, 16, 64)"),
        "wrong-partner-component": ("__shfl_xor(n3, 16, 32)", "__shfl_xor(n2, 16, 32)"),
        "wrong-cache-column": ("int ca0 = row * 128 + (column + 0) % 64;", "int ca0 = row * 128 + (column + 1) % 64;"),
        "missing-first-warp-fence": ("  __syncwarp();\n  float p0", "  float p0"),
        "missing-second-warp-fence": ("  __syncwarp();\n  int out0", "  int out0"),
    }
    result = {}
    for name, (old, new) in replacements.items():
        if text.count(old) != 1:
            raise ValueError("Source mutation anchor differs: " + name)
        result[name] = statement(text.replace(old, new), contract)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    prefix.run_stage(parser.parse_args(), target=TARGET, statement_factory=statement,
                     additional_claims={"status": "native-qknorm-rope-split-half-physical-wave-checked",
                                        "split_half_physical_wave_execution_to_halt": True,
                                        "split_half_physical_wave_source_order_outputs": True,
                                        "split_half_physical_wave_access_classification": True,
                                        "split_half_physical_wave_initial_race_freedom": True,
                                        "split_half_accesses_per_wave": 1280,
                                        "split_half_actual_warp_fences": 2,
                                        "whole_block_execution_proved": False,
                                        "whole_grid_execution_proved": False},
                     required_principals={"LarkNativeQKNormRope.native_split_wave",
                                          "LarkNativeQKNormRope.split_wave_value",
                                          "LarkNativeQKNormRope.split_wave_epoch",
                                          "LarkNativeQKNormRope.split_wave_initial_race_free"},
                     control_factory=controls)


if __name__ == "__main__":
    main()
