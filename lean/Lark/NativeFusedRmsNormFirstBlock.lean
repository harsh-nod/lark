import Lark.NativeFusedRmsNormWaveFold

/-! Complete first native block phase: all sixteen waves, all initialized
mutable values, all thirty-two distinct partials and actual block convergence.
This stops before the first barrier resume; normalization remains later work.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem row_thread_coords (row tid : Nat) (ht : tid < 1024) :
    (row * 1024 + tid) / 1024 = row ∧ (row * 1024 + tid) % 1024 = tid := by omega

theorem block_mem (p : Shape) (row t : Nat) :
    t ∈ blockThreads (geometry p) row ↔ ∃ tid, tid < 1024 ∧ t = row * 1024 + tid := by
  simp only [blockThreads, geometry, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨tid, ht, he⟩; exact ⟨tid, ht, he.symm⟩
  · rintro ⟨tid, ht, he⟩; exact ⟨tid, ht, he.symm⟩

structure BlockEntry (p : Shape) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop where
  valid : row < p.rows
  pc : ∀ tid, tid < 1024 → s.pc (row * 1024 + tid) = 0
  pending : ∀ tid, tid < 1024 → Pending input row tid 0 s
  weights : ∀ col, col < 16384 → s.memory (globalCell 2 col) = some (input 2 col)
  epoch : ∀ tid, tid < 1024 → (s.epochs (row * 1024 + tid)).block = 0
  good : ∀ a ∈ s.trace, Good a

theorem initial_block_entry (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α)
    (row : Nat) (hr : row < p.rows) : BlockEntry p input row (initial p input outside) :=
  ⟨hr, by intro tid ht; rfl,
    fun tid ht => initial_pending p input outside row tid hr ht,
    fun col hc => initial_weight p input outside col hc,
    by intro tid ht; rfl, by intro a ha; cases ha⟩

theorem wave_entry_of_block_entry (p : Shape) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hb : ∀ w ∈ ws, w < 16)
    (entry : BlockEntry p input row s) : WaveEntry input row ws s := by
  exact {
    pc := by
      intro w hw t ht
      obtain ⟨lane, hl, rfl⟩ := (cohort_mem row w 64 t).mp ht
      have hw := hb w hw
      simpa only [cohortBase, Nat.add_assoc] using entry.pc (w * 64 + lane) (by omega)
    pending := by
      intro w hw t ht
      obtain ⟨lane, hl, rfl⟩ := (cohort_mem row w 64 t).mp ht
      have hw := hb w hw
      have hc := cohort_arithmetic row w lane hw hl
      simpa only [hc.1, hc.2.1] using entry.pending (w * 64 + lane) (by omega)
    epoch := by
      intro w hw t ht
      obtain ⟨lane, hl, rfl⟩ := (cohort_mem row w 64 t).mp ht
      have hw := hb w hw
      simpa only [cohortBase, Nat.add_assoc] using entry.epoch (w * 64 + lane) (by omega)
    good := entry.good }

def blockPartial (ops : Ops α) (input : Nat → Nat → α) (row logicalWarp : Nat) : α :=
  waveValues ops input row (logicalWarp / 2) 5 ((logicalWarp % 2) * 32)

def rowAdded (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) : α :=
  ops.add (ops.fromHalf (input 0 (address row col))) (ops.fromHalf (input 1 (address row col)))

def firstBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  waveFold p ops input row (List.range 16) s

theorem first_block_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    (firstBlock p ops input row s).epochs = s.epochs := wave_fold_epochs p ops input row (List.range 16) s

theorem first_block_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : BlockEntry p input row s) (ht : tid < 1024) :
    FirstDone ops input (row * 1024 + tid) (firstBlock p ops input row s) := by
  have hw : tid / 64 < 16 := by omega
  have hl : tid % 64 < 64 := Nat.mod_lt _ (by decide)
  have he : row * 1024 + tid = cohortBase row (tid / 64) + tid % 64 := by unfold cohortBase; omega
  exact wave_fold_member p ops input row (List.range 16) s entry.valid List.nodup_range
    (fun _w hw => List.mem_range.mp hw)
    (wave_entry_of_block_entry p input row _ s (fun _w hw => List.mem_range.mp hw) entry)
    (tid / 64) (row * 1024 + tid) (List.mem_range.mpr hw) ((cohort_mem row (tid / 64) 64 _).mpr ⟨tid % 64, hl, he⟩)

theorem first_block_partial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row logicalWarp : Nat) (s : State α) (hw : logicalWarp < 32) :
    (firstBlock p ops input row s).memory ⟨.shared, row, 0, logicalWarp⟩ =
      some (blockPartial ops input row logicalWarp) := by
  have h := wave_fold_partial p ops input row (List.range 16) s List.nodup_range
    (fun _w hw => List.mem_range.mp hw) (logicalWarp / 2) (logicalWarp % 2)
    (List.mem_range.mpr (by omega)) (Nat.mod_lt _ (by decide))
  simpa only [show logicalWarp / 2 * 2 + logicalWarp % 2 = logicalWarp by omega, blockPartial] using h

theorem first_block_cells (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row col : Nat) (s : State α) (entry : BlockEntry p input row s) (hc : col < 16384) :
    (firstBlock p ops input row s).memory (globalCell 1 (address row col)) = some (ops.toHalf (rowAdded ops input row col)) ∧
    (firstBlock p ops input row s).memory ⟨.shared, row, 1, col⟩ = some (rowAdded ops input row col) := by
  obtain ⟨tid, ht, iteration, hi, component, hcomp, hcol⟩ := coverage p col hc
  have done := first_block_member p ops input row tid s entry ht
  have h := done.completed (iteration * 8 + component) (by omega)
  have coords := row_thread_coords row tid ht
  have hs : slot tid (iteration * 8 + component) = col := (slot_rank tid iteration component hcomp).trans hcol
  simpa only [coords.1, coords.2, flatAdded, flatAddress, hs, rowAdded, unroundedCell] using h

theorem first_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    ∀ a ∈ (firstBlock p ops input row s).trace, Good a :=
  wave_fold_good p ops input row (List.range 16) s entry.valid List.nodup_range
    (fun _w hw => List.mem_range.mp hw)
    (wave_entry_of_block_entry p input row _ s (fun _w hw => List.mem_range.mp hw) entry)

theorem first_block_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    LarkCollective.converged program (blockThreads (geometry p) row) (firstBlock p ops input row s) = some .block := by
  have hthreads : blockThreads (geometry p) row = cohortThreads row 0 1024 := by
    simp [blockThreads, geometry, cohortThreads, cohortBase]
  rewrite [hthreads]
  apply (cohort_first_barrier row 0 1024 _ (by decide) ?_).2
  intro tid ht
  simpa only [cohortBase, Nat.zero_mul, Nat.add_zero] using (first_block_member p ops input row tid s entry ht).pc

/-- The exact first native-wave fold in `runBlock`, preserving all prior stores. -/
theorem first_block_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : BlockEntry p input row s) :
    (List.range (((geometry p).block + (geometry p).warp - 1) / (geometry p).warp)).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
        (warpThreads (geometry p) row w) fuel.warp s) s = some (firstBlock p ops input row s) := by
  have hcount : ((geometry p).block + (geometry p).warp - 1) / (geometry p).warp = 16 := by
    change (1024 + 64 - 1) / 64 = 16
    decide
  rewrite [hcount]
  exact wave_fold_run p ops input row (List.range 16) s entry.valid List.nodup_range
    (fun _w hw => List.mem_range.mp hw)
    (wave_entry_of_block_entry p input row _ s (fun _w hw => List.mem_range.mp hw) entry)

theorem first_block_initial_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    (List.range 16).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
        (warpThreads (geometry p) row w) fuel.warp s) (initial p input outside) =
      some (firstBlock p ops input row (initial p input outside)) := by
  simpa only [geometry, Nat.reduceAdd, Nat.reduceSub, Nat.reduceDiv] using
    first_block_fold_run p ops input row _ (initial_block_entry p input outside row hr)

theorem first_block_initial_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row < p.rows) :
    raceFree (geometry p) (firstBlock p ops input row (initial p input outside)).trace = true :=
  race_free p _ (first_block_good p ops input row _ (initial_block_entry p input outside row hr))

#print axioms initial_block_entry
#print axioms wave_entry_of_block_entry
#print axioms first_block_member
#print axioms first_block_partial
#print axioms first_block_cells
#print axioms first_block_good
#print axioms first_block_cut
#print axioms first_block_fold_run
#print axioms first_block_initial_run
#print axioms first_block_initial_race_free
end LarkNativeFusedRmsNorm
