import Lark.NativeFlashInferRmsNormOutputWaves

/-! Complete actual output block phase, all16384 output values, retained read-only
inputs/shared cells, and actual access classification at the source halt.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem block_cohort (p : Shape) (row : Nat) : blockThreads (geometry p) row = cohortThreads row 0 1024 := by
  simp [blockThreads,geometry,cohortThreads,cohortBase]

theorem block_nodup (p : Shape) (row : Nat) : (blockThreads (geometry p) row).Nodup := by
  rewrite [block_cohort]
  exact cohort_nodup row 0 1024

theorem block_owner (p : Shape) (row t : Nat) (ht : t ∈ blockThreads (geometry p) row) : t / 1024 = row := by
  obtain ⟨tid,ht,rfl⟩ := (block_mem p row t).mp ht
  omega

def outputBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  outputFold ops input row (blockThreads (geometry p) row) s

def outputResult (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) : α :=
  ops.toHalf (outputWeighted ops input row col (outputInverse ops (blockSum ops input row)))

theorem output_block_entry (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : OutReady p ops input row s) :
    OutputFoldEntry p ops input row (blockThreads (geometry p) row) s := by
  exact {
    valid := ready.valid
    reads := out_ready_reads p ops input row s ready
    total := ready.total
    indices := by intro t ht; obtain ⟨tid,htid,rfl⟩ := (block_mem p row t).mp ht; exact ready.indices tid htid
    pc := by intro t ht; obtain ⟨tid,htid,rfl⟩ := (block_mem p row t).mp ht; exact ready.pc tid htid
    epoch := by intro t ht; obtain ⟨tid,htid,rfl⟩ := (block_mem p row t).mp ht; exact ready.epoch tid htid
    good := ready.good }

theorem output_block_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : OutReady p ops input row s) :
    (List.range (((geometry p).block + (geometry p).warp - 1) / (geometry p).warp)).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
        (warpThreads (geometry p) row w) fuel.warp s) s = some (outputBlock p ops input row s) := by
  have hcount : ((geometry p).block + (geometry p).warp - 1) / (geometry p).warp = 16 := by
    change (1024 + 64 - 1) / 64 = 16
    decide
  have entry := output_block_entry p ops input row s ready
  have hf := output_waves_run p ops input row (List.range 16) s List.nodup_range
    (fun w hw => List.mem_range.mp hw) (by simpa only [all_output_threads p row] using entry)
  have he : outputWaves ops input row (List.range 16) s = outputBlock p ops input row s := by
    rewrite [output_waves_eq_fold,all_output_threads p row]
    rfl
  rewrite [hcount]
  exact hf.trans (congrArg some he)

theorem output_block_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid < 1024) :
    (outputBlock p ops input row s).pc (row * 1024 + tid) = 67 :=
  output_fold_pc ops input row (blockThreads (geometry p) row) s (block_nodup p row)
    (row * 1024 + tid) ((block_mem p row _).mpr ⟨tid,ht,rfl⟩)

theorem block_halt_of_pc (p : Shape) (row : Nat) (s : State α)
    (hp : ∀ tid, tid < 1024 → s.pc (row * 1024 + tid) = 67) :
    LarkCollective.converged program (blockThreads (geometry p) row) s = some .halt := by
  rewrite [block_cohort]
  apply (cohort_halt row 0 1024 s (by decide) ?_).2
  intro tid ht
  simpa only [cohortBase,Nat.zero_mul,Nat.add_zero] using hp tid ht

theorem output_block_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    LarkCollective.converged program (blockThreads (geometry p) row) (outputBlock p ops input row s) = some .halt :=
  block_halt_of_pc p row (outputBlock p ops input row s) (fun tid ht => output_block_pc p ops input row tid s ht)

theorem output_block_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row extra : Nat) (s : State α) (ready : OutReady p ops input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel program row (extra + 1) s =
      some (outputBlock p ops input row s) := by
  rewrite [LarkPartitionCollective.runBlock,output_block_fold_run p ops input row s ready]
  simp only [bind,pure,Option.some_bind,output_block_cut,reduceCtorEq,↓reduceIte,or_true]

theorem output_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : OutReady p ops input row s) :
    ∀ a ∈ (outputBlock p ops input row s).trace, Good a :=
  output_fold_good p ops input row (blockThreads (geometry p) row) s (block_nodup p row) (block_owner p row)
    (output_block_entry p ops input row s ready)

theorem output_block_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row col : Nat) (s : State α) (hc : col < 16384) :
    (outputBlock p ops input row s).memory (globalCell 0 (address row col)) = some (outputResult ops input row col) := by
  obtain ⟨tid,ht,iteration,hi,component,hcomponent,hcol⟩ := coverage col hc
  let t := row * 1024 + tid
  have hm : t % 1024 = tid := (row_thread_coords row tid ht).2
  have hj : iteration * 8 + component < 16 := by omega
  have hwrites : OutputWrites row (t % 1024) (globalCell 0 (address row col)) := by
    refine ⟨iteration * 8 + component,hj,?_⟩
    simp only [hm,flatAddress,slot_rank tid iteration component hcomponent,hcol]
  apply output_fold_value p ops input row (blockThreads (geometry p) row) s (block_nodup p row) (block_owner p row)
    t ((block_mem p row t).mpr ⟨tid,ht,rfl⟩) _ _ hwrites
  intro u
  have h := output_lane_completed ops input row (t % 1024) t (blockSum ops input row) u
  have hvalue := h (iteration * 8 + component) hj
  simpa only [hm,flatAddress,slot_rank tid iteration component hcomponent,hcol,outputResult] using hvalue

theorem output_block_memory_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (l : Location) (hl : ∀ tid, tid < 1024 → ¬ OutputWrites row tid l) :
    (outputBlock p ops input row s).memory l = s.memory l :=
  output_fold_memory_frame ops input row (blockThreads (geometry p) row) s l
    (fun t ht => hl (t % 1024) (Nat.mod_lt _ (by decide)))

theorem output_block_input (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row offset : Nat) (s : State α) :
    (outputBlock p ops input row s).memory (globalCell 1 offset) = s.memory (globalCell 1 offset) :=
  output_block_memory_frame p ops input row s _ (by intro tid ht; rintro ⟨j,hj,he⟩; cases he)

theorem output_block_shared (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row owner buffer offset : Nat) (s : State α) :
    (outputBlock p ops input row s).memory ⟨.shared,owner,buffer,offset⟩ = s.memory ⟨.shared,owner,buffer,offset⟩ :=
  output_fold_shared ops input row (blockThreads (geometry p) row) s owner buffer offset

theorem output_block_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (outputBlock p ops input row s).epochs = s.epochs :=
  output_fold_epochs ops input row (blockThreads (geometry p) row) s

theorem output_block_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (outputBlock p ops input row s).trace.length = s.trace.length + 50176 := by
  simpa only [blockThreads,geometry,List.length_map,List.length_range] using
    output_fold_trace_length ops input row (blockThreads (geometry p) row) s

#print axioms block_cohort
#print axioms block_nodup
#print axioms block_owner
#print axioms output_block_entry
#print axioms output_block_fold_run
#print axioms output_block_pc
#print axioms block_halt_of_pc
#print axioms output_block_cut
#print axioms output_block_run
#print axioms output_block_good
#print axioms output_block_value
#print axioms output_block_memory_frame
#print axioms output_block_input
#print axioms output_block_shared
#print axioms output_block_epochs
#print axioms output_block_trace_length
end LarkNativeFlashInferRmsNorm
