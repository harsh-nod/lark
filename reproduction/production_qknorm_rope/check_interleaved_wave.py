"""Fresh complete native interleaved-wave execution and output checks.

The split-half path remains at its normalization prefix. Complete block/grid
execution, dense reference equality and registered certificates remain open.
"""

import argparse
from pathlib import Path

import check_execution_prefix as prefix

TARGET = "Lark.NativeQKNormRopeInterleavedWave"


def statement(text, contract):
    body = prefix.source_statement(text, contract).replace("import " + prefix.TARGET, "import " + TARGET)
    if contract.rotary_layout != "interleaved":
        return body
    return body + '''
theorem source_interleaved_wave (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) (hb : block < sourceShape.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads sourceShape input s) :
    LarkPartitionCollective.runWarp ops (layout sourceShape) (geometry sourceShape) fuel sourceProgram
      (warpThreads (geometry sourceShape) block warp) fuel.warp s = some (interleavedWaveState sourceShape ops input block warp s) := by
  simpa only [source_binding.1, sourceNeox] using native_interleaved_wave sourceShape ops input block warp s hb hw hp hr
theorem source_interleaved_wave_value (ops : Ops α) (input : Nat → Nat → α)
    (block warp lane e : Nat) (s : State α) (hl : lane < 64) (he : e < 4) :
    let t := cohortBase block warp + lane
    (interleavedWaveState sourceShape ops input block warp s).memory (globalCell 0 (outputAddress t e)) =
      some (ops.toHalf (interleavedOutput ops input
        (fun r => normalizedValue ops input t (weightBuffer t) (normalScale ops (waveValues ops input block warp 5 lane)) r) t e)) :=
  interleaved_wave_value sourceShape ops input block warp lane e s hl he
theorem source_interleaved_wave_readonly (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) (hr : Reads sourceShape input s) :
    Reads sourceShape input (interleavedWaveState sourceShape ops input block warp s) :=
  interleaved_wave_reads sourceShape ops input block warp s hr
theorem source_interleaved_wave_trace (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) :
    (interleavedWaveState sourceShape ops input block warp s).trace.length = s.trace.length + 1024 :=
  interleaved_wave_trace_length sourceShape ops input block warp s
theorem source_interleaved_wave_access_classification (ops : Ops α) (input : Nat → Nat → α)
    (block warp : Nat) (s : State α) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (interleavedWaveState sourceShape ops input block warp s).trace, Good access :=
  interleaved_wave_good sourceShape ops input block warp s good
theorem source_interleaved_wave_race_free (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (block warp : Nat) :
    raceFree (geometry sourceShape)
      (interleavedWaveState sourceShape ops input block warp (initial (layout sourceShape) input outside)).trace = true :=
  interleaved_wave_initial_race_free sourceShape ops input outside block warp
#print axioms source_interleaved_wave
#print axioms source_interleaved_wave_value
#print axioms source_interleaved_wave_readonly
#print axioms source_interleaved_wave_trace
#print axioms source_interleaved_wave_access_classification
#print axioms source_interleaved_wave_race_free
'''


def controls(contracts):
    text, contract = contracts["interleaved"]
    replacements = {
        "wrong-last-output-register": ("output[out3] = __float2half(o3);", "output[out3] = __float2half(o2);"),
        "wrong-rotation-sign": ("float o0 = xc0 - ys0;", "float o0 = xc0 + ys0;"),
        "wrong-imaginary-operand-order": ("float o1 = xs0 + yc0;", "float o1 = yc0 + xs0;"),
        "wrong-cache-pair": ("int ca1 = row * 128 + lane * 2 + 1;", "int ca1 = row * 128 + lane * 2 + 0;"),
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
                     additional_claims={"status": "native-qknorm-rope-interleaved-physical-wave-checked",
                                        "interleaved_physical_wave_execution_to_halt": True,
                                        "interleaved_physical_wave_source_order_outputs": True,
                                        "interleaved_physical_wave_access_classification": True,
                                        "interleaved_physical_wave_initial_race_freedom": True,
                                        "interleaved_accesses_per_wave": 1024,
                                        "whole_block_execution_proved": False,
                                        "whole_grid_execution_proved": False},
                     required_principals={"LarkNativeQKNormRope.native_interleaved_wave",
                                          "LarkNativeQKNormRope.interleaved_wave_value",
                                          "LarkNativeQKNormRope.interleaved_wave_initial_race_free"},
                     control_factory=controls)


if __name__ == "__main__":
    main()
