import Lark.NativeQKNormRopeInterleavedWaves

/-! Complete native interleaved block execution under the pinned geometry and
fuel, with all 1024 output scalars and the actual 4096-access block trace. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def interleavedBlockState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (s : State α) : State α := interleavedWaves p ops input block (List.range 4) s

theorem interleaved_block_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (s : State α) (hb : block < p.rows * 5) (hp : ∀ t ∈ blockThreads (geometry p) block, s.pc t = 0)
    (hr : Reads p input s) :
    (List.range (((geometry p).block + (geometry p).warp - 1) / (geometry p).warp)).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program false)
        (warpThreads (geometry p) block w) fuel.warp s) s = some (interleavedBlockState p ops input block s) := by
  have count : ((geometry p).block + (geometry p).warp - 1) / (geometry p).warp = 4 := by
    change (256 + 64 - 1) / 64 = 4
    decide
  rw [count]
  apply interleaved_waves_run p ops input block (List.range 4) s hb List.nodup_range
    (by intro w hw; exact List.mem_range.mp hw) ?_ hr
  intro w hw t ht
  exact hp t (cohort_in_native_block p block w t (List.mem_range.mp hw) ht)

theorem interleaved_block_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block t : Nat)
    (s : State α) (ht : t ∈ blockThreads (geometry p) block) : (interleavedBlockState p ops input block s).pc t = 87 := by
  obtain ⟨w, hw, hm⟩ := native_block_coverage p block t ht
  exact interleaved_waves_pc p ops input block (List.range 4) s List.nodup_range
    (by intro v hv; exact List.mem_range.mp hv) w t (List.mem_range.mpr hw) hm

theorem interleaved_block_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat) (s : State α) :
    LarkCollective.converged (program false) (blockThreads (geometry p) block)
      (interleavedBlockState p ops input block s) = some .halt := by
  rw [native_block_cohort]
  apply (cohort_final_halt false block 0 256 _ (by decide) ?_).2
  intro lane hl
  apply interleaved_block_pc
  rw [native_block_cohort]
  exact (cohort_mem block 0 256 _).mpr ⟨lane, hl, rfl⟩

theorem native_interleaved_block (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (s : State α) (hb : block < p.rows * 5) (hp : ∀ t ∈ blockThreads (geometry p) block, s.pc t = 0)
    (hr : Reads p input s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program false) block fuel.block s =
      some (interleavedBlockState p ops input block s) := by
  change LarkPartitionCollective.runBlock _ _ _ _ _ _ (0 + 1) s = _
  rw [LarkPartitionCollective.runBlock, interleaved_block_fold_run p ops input block s hb hp hr]
  simp only [bind, pure, Option.some_bind, interleaved_block_cut, reduceCtorEq, ↓reduceIte, or_true]

theorem interleaved_block_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block t e : Nat)
    (s : State α) (ht : t ∈ blockThreads (geometry p) block) (he : e < 4) :
    (interleavedBlockState p ops input block s).memory (globalCell 0 (outputAddress t e)) =
      some (interleavedSourceResult ops input t e) := by
  obtain ⟨w, hw, hm⟩ := native_block_coverage p block t ht
  exact interleaved_waves_value p ops input block (List.range 4) s List.nodup_range
    (by intro v hv; exact List.mem_range.mp hv) w t e (List.mem_range.mpr hw) hm he

theorem interleaved_block_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (interleavedBlockState p ops input block s) :=
  interleaved_waves_reads p ops input block (List.range 4) s hr

theorem interleaved_block_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (s : State α) : (interleavedBlockState p ops input block s).epochs = s.epochs :=
  interleaved_waves_epochs p ops input block (List.range 4) s

theorem interleaved_block_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block t : Nat)
    (s : State α) (ht : t ∉ blockThreads (geometry p) block) :
    (interleavedBlockState p ops input block s).pc t = s.pc t ∧
    (interleavedBlockState p ops input block s).indices t = s.indices t ∧
    (interleavedBlockState p ops input block s).regs t = s.regs t := by
  apply interleaved_waves_other
  intro w hw hm
  exact ht (cohort_in_native_block p block w t (List.mem_range.mp hw) hm)

theorem interleaved_block_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (s : State α) (loc : Location) (hn : loc.buffer ≠ 0 ∨ physicalBlock (loc.offset / 4) ≠ block) :
    (interleavedBlockState p ops input block s).memory loc = s.memory loc := by
  apply interleaved_waves_memory_frame
  intro w hw t ht
  rcases hn with hb | ho
  · exact Or.inl hb
  · apply Or.inr
    intro eq
    exact ho ((congrArg physicalBlock eq).trans ((cohort_owner block w t (List.mem_range.mp hw)).mp ht).1)

theorem interleaved_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (s : State α) (good : ∀ access ∈ s.trace, Good access) :
    ∀ access ∈ (interleavedBlockState p ops input block s).trace, Good access :=
  interleaved_waves_good p ops input block (List.range 4) s good

theorem interleaved_block_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block : Nat)
    (s : State α) : (interleavedBlockState p ops input block s).trace.length = s.trace.length + 4096 := by
  simpa only [List.length_range] using interleaved_waves_trace_length p ops input block (List.range 4) s

#print axioms interleaved_block_fold_run
#print axioms interleaved_block_pc
#print axioms interleaved_block_cut
#print axioms native_interleaved_block
#print axioms interleaved_block_value
#print axioms interleaved_block_reads
#print axioms interleaved_block_epochs
#print axioms interleaved_block_other
#print axioms interleaved_block_memory_frame
#print axioms interleaved_block_good
#print axioms interleaved_block_trace_length
end LarkNativeQKNormRope
