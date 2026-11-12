"""Fresh complete interleaved launch and source-order correctness checks.

The independent dense-reference equality and split-half rotary execution are
still open. This development check produces zero registered certificates.
"""

import argparse
from pathlib import Path

import check_interleaved_wave as wave

TARGET = "Lark.NativeQKNormRopeInterleavedCorrect"


def statement(text, contract):
    body = wave.statement(text, contract).replace("import " + wave.TARGET, "import " + TARGET)
    if contract.rotary_layout != "interleaved":
        return body
    return body + '''
theorem source_interleaved_block (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (s : State α) (hb : block < sourceShape.rows * 5)
    (hp : ∀ t ∈ blockThreads (geometry sourceShape) block, s.pc t = 0) (hr : Reads sourceShape input s) :
    LarkPartitionCollective.runBlock ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram block fuel.block s =
      some (interleavedBlockState sourceShape ops input block s) := by
  simpa only [source_binding.1, sourceNeox] using native_interleaved_block sourceShape ops input block s hb hp hr
theorem source_interleaved_grid (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hp : ∀ t, t < sourceShape.rows * 1280 → s.pc t = 0) (hr : Reads sourceShape input s) :
    LarkPartitionCollective.runGrid ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram fuel.grid s =
      some (interleavedGridState sourceShape ops input s) := by
  simpa only [source_binding.1, sourceNeox] using native_interleaved_grid sourceShape ops input s hp hr
theorem source_interleaved_source_order_correct (ops : Ops α) :
    LarkPartitionCollective.Correct ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram
      (interleavedSourceSpec sourceShape ops) := by
  simpa only [source_binding.1, sourceNeox] using interleaved_source_correct sourceShape ops
theorem source_interleaved_correct_from_pre (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (hp : StdPre (layout sourceShape) input s) : ∃ final,
    LarkPartitionCollective.runLaunch ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram s = some final ∧
      raceFree (geometry sourceShape) final.trace = true ∧
      extract (layout sourceShape) final = some (interleavedSourceSpec sourceShape ops input) := by
  simpa only [source_binding.1, sourceNeox] using interleaved_source_correct_from_pre sourceShape ops input s hp
theorem source_interleaved_final_output (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (i : Nat) (hi : i < sourceShape.rows * 5120) :
    (interleavedFinalState sourceShape ops input outside).memory (globalCell 0 i) =
      some (interleavedSourceResult ops input (i / 4) (i % 4)) :=
  interleaved_final_output sourceShape ops input outside i hi
theorem source_interleaved_final_readonly (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : Reads sourceShape input (interleavedFinalState sourceShape ops input outside) :=
  interleaved_final_readonly sourceShape ops input outside
theorem source_interleaved_final_trace (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : (interleavedFinalState sourceShape ops input outside).trace.length = sourceShape.rows * 20480 :=
  interleaved_final_trace_length sourceShape ops input outside
#print axioms source_interleaved_block
#print axioms source_interleaved_grid
#print axioms source_interleaved_source_order_correct
#print axioms source_interleaved_correct_from_pre
#print axioms source_interleaved_final_output
#print axioms source_interleaved_final_readonly
#print axioms source_interleaved_final_trace
'''


def controls(contracts):
    result = {name: body.replace("import " + wave.TARGET, "import " + TARGET)
              for name, body in wave.controls(contracts).items()}
    text, contract = contracts["interleaved"]
    body = statement(text, contract)
    changes = {
        "shortened-native-grid": ("def sourceGeometry : Geometry := ⟨5,256,64⟩", "def sourceGeometry : Geometry := ⟨4,256,64⟩"),
        "changed-native-fuel": ("def sourceFuel : Fuel := ⟨256,16,1,1⟩", "def sourceFuel : Fuel := ⟨256,15,1,1⟩"),
        "shortened-output-shape": ("⟨.output, 5120⟩", "⟨.output, 5119⟩"),
    }
    for name, (old, new) in changes.items():
        if body.count(old) != 1:
            raise ValueError("Interface control anchor differs: " + name)
        result[name] = body.replace(old, new)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--output", type=Path, required=True)
    parser.add_argument("--lean-bin", type=Path, required=True)
    wave.prefix.run_stage(parser.parse_args(), target=TARGET, statement_factory=statement,
                         additional_claims={"status": "native-qknorm-rope-interleaved-whole-launch-source-order-checked",
                                            "interleaved_physical_wave_execution_to_halt": True,
                                            "interleaved_physical_wave_source_order_outputs": True,
                                            "interleaved_physical_wave_access_classification": True,
                                            "interleaved_physical_wave_initial_race_freedom": True,
                                            "interleaved_accesses_per_wave": 1024,
                                            "interleaved_whole_block_execution_proved": True,
                                            "interleaved_whole_grid_execution_proved": True,
                                            "interleaved_whole_launch_source_order_correct": True,
                                            "interleaved_complete_output_extraction_proved": True,
                                            "interleaved_per_row_accesses": 20480,
                                            "whole_block_execution_proved": False,
                                            "whole_grid_execution_proved": False,
                                            "unqualified_whole_kernel_flags_require_both_layouts": True},
                         required_principals={"LarkNativeQKNormRope.native_interleaved_block",
                                              "LarkNativeQKNormRope.native_interleaved_launch",
                                              "LarkNativeQKNormRope.interleaved_source_correct",
                                              "LarkNativeQKNormRope.interleaved_source_correct_from_pre",
                                              "LarkNativeQKNormRope.interleaved_final_extract"},
                         control_factory=controls)


if __name__ == "__main__":
    main()
