import Lark.NativeSglangRmsNormPrefixFold

/-! Bind the private-cache lane fold to an actual physical wave64 scheduler prefix.
The wave reaches PC44 with two complete logical32 partitions. This leaves the
shuffle and its continuation explicit; no whole-wave completion is asserted.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def cohortBase (row warp : Nat) : Nat := row * 1024 + warp * 64
def cohortThreads (row warp active : Nat) : List Nat :=
  (List.range active).map (fun lane => cohortBase row warp + lane)

theorem cohort_mem (row warp active t : Nat) :
    t ∈ cohortThreads row warp active ↔ ∃ lane, lane < active ∧ t = cohortBase row warp + lane := by
  simp only [cohortThreads, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨lane, hl, he⟩; exact ⟨lane, hl, he.symm⟩
  · rintro ⟨lane, hl, he⟩; exact ⟨lane, hl, he.symm⟩

theorem cohort_nodup (row warp active : Nat) : (cohortThreads row warp active).Nodup := by
  unfold cohortThreads
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (R := fun a b : Nat => a ≠ b) (by intro a b hab; omega) List.nodup_range

theorem cohort_arithmetic (row warp lane : Nat) (hw : warp < 16) (hl : lane < 64) :
    (cohortBase row warp + lane) / 1024 = row ∧
    (cohortBase row warp + lane) % 1024 = warp * 64 + lane ∧
    ((cohortBase row warp + lane) % 1024) % 64 = lane := by
  unfold cohortBase
  omega

theorem cohort_coords (p : Shape) (row warp lane : Nat) (hw : warp < 16) (hl : lane < 64) :
    LarkPartitionCollective.nativeBase (geometry p) (cohortBase row warp + lane) = cohortBase row warp ∧
    LarkPartitionCollective.nativeLane (geometry p) (cohortBase row warp + lane) = lane := by
  have h := cohort_arithmetic row warp lane hw hl
  simp only [LarkPartitionCollective.nativeBase, LarkPartitionCollective.nativeLane, geometry,
    h.1, h.2.1, h.2.2]
  have hd : (warp * 64 + lane) / 64 = warp := by omega
  have hm : (warp * 64 + lane) % 64 = lane := by omega
  simp only [hd, hm, cohortBase, and_self]

theorem cohort_bound (p : Shape) (row warp active : Nat) (hr : row < p.rows) (hw : warp < 16)
    (ha : active ≤ 64) : ∀ t ∈ cohortThreads row warp active, t < p.rows * 1024 := by
  intro t ht
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
  unfold cohortBase
  omega

theorem cohort_head (row warp active : Nat) (ha : 0 < active) :
    (cohortThreads row warp active).head? = some (cohortBase row warp) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : active ≠ 0)
  rewrite [cohortThreads, List.range_eq_range', List.range'_succ]
  rfl

theorem cohort_native_threads (p : Shape) (row warp : Nat) (hw : warp < 16) :
    warpThreads (geometry p) row warp = cohortThreads row warp 64 := by
  have all : ∀ w : Fin 16,
      (List.range 1024).filter (fun t => t / 64 == w.val) =
        (List.range 64).map (fun lane => w.val * 64 + lane) := by decide
  simp only [warpThreads, geometry, all ⟨warp, hw⟩, List.map_map, cohortThreads, cohortBase]
  apply List.map_inj_left.mpr
  intro lane hl
  dsimp only [Function.comp_apply]
  omega

theorem cohort_complete32 (p : Shape) (row warp active : Nat)
    (hw : warp < 16) (ha : active = 32 ∨ active = 64) :
    LarkPartitionCollective.completePartitions (geometry p) (cohortThreads row warp active) 32 = true := by
  apply List.all_eq_true.mpr
  intro t ht
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
  have h64 : lane < 64 := by omega
  rewrite [(cohort_coords p row warp lane hw h64).1, (cohort_coords p row warp lane hw h64).2]
  apply List.all_eq_true.mpr
  intro peer hp
  have hp := List.mem_range.mp hp
  apply List.contains_iff_mem.mpr
  exact (cohort_mem row warp active _).mpr ⟨lane / 32 * 32 + peer, by omega, by omega⟩

theorem cohort_next (repaired : Bool) (row warp active pc : Nat) (s : State α) (ha : 0 < active)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc)
    (hs : ∀ t, s.pc t = pc → LarkPartitionCollective.isShuffle (program repaired) s t = true) :
    LarkPartitionCollective.nextCohort (program repaired) (cohortThreads row warp active) s =
      some (cohortThreads row warp active) := by
  have hp0 : s.pc (cohortBase row warp) = pc := by simpa only [Nat.add_zero] using hp 0 ha
  have hf : (cohortThreads row warp active).filter (LarkPartitionCollective.isShuffle (program repaired) s) =
      cohortThreads row warp active := by
    apply List.filter_eq_self.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
    exact hs _ (hp lane hl)
  unfold LarkPartitionCollective.nextCohort
  rewrite [hf, cohort_head row warp active ha]
  simp only [bind, pure, Option.some_bind]
  congr 1
  apply List.filter_eq_self.mpr
  intro t ht
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
  simp [hp lane hl, hp0]

def continueCohort (p : Shape) (repaired : Bool) (ops : Ops α) (ts : List Nat) (n : Nat) (s : State α) : Option (State α) := do
  match LarkPartitionCollective.nextCohort (program repaired) ts s with
  | some cohort =>
    let next ← LarkPartitionCollective.runShuffle (geometry p) (program repaired) cohort s
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired) ts n next
  | none =>
    let cut ← LarkCollective.converged (program repaired) ts s
    if cut = .warp then LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired) ts n (resume ts .warp s)
    else some s

theorem run_warp_continue (p : Shape) (repaired : Bool) (ops : Ops α) (ts : List Nat) (n : Nat) (s : State α) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired) ts (n + 1) s =
      (ts.foldlM (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane u) s).bind
        (continueCohort p repaired ops ts n) := rfl

theorem native_prefix_step (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n : Nat) (s : State α) (hr : row < p.rows) (hw : warp < 16)
    (hp : ∀ t ∈ cohortThreads row warp 64, s.pc t = 0)
    (reads : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (warpThreads (geometry p) row warp) (n + 1) s =
      continueCohort p repaired ops (cohortThreads row warp 64) n
        (prefixFold ops input (cohortThreads row warp 64) s) := by
  rewrite [cohort_native_threads p row warp hw, run_warp_continue,
    prefix_fold_run p repaired ops input _ s (cohort_nodup row warp 64)
      (cohort_bound p row warp 64 hr hw (by decide)) hp reads]
  rfl

theorem native_prefix_initial (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp n : Nat) (hr : row < p.rows) (hw : warp < 16) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (warpThreads (geometry p) row warp) (n + 1) (initial p input outside) =
      continueCohort p repaired ops (cohortThreads row warp 64) n
        (prefixFold ops input (cohortThreads row warp 64) (initial p input outside)) :=
  native_prefix_step p repaired ops input row warp n _ hr hw (by intro t ht; rfl)
    (initial_reads p input outside)

theorem native_prefix_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (_hr : row < p.rows) (_hw : warp < 16)
    (lane : Nat) (hl : lane < 64) :
    PrefixReady p ops input (cohortBase row warp + lane)
      (prefixFold ops input (cohortThreads row warp 64) (initial p input outside)) :=
  initial_prefix_fold_member p ops input outside _ (cohort_nodup row warp 64)
    _ ((cohort_mem row warp 64 _).mpr ⟨lane, hl, rfl⟩)

theorem native_prefix_next (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row < p.rows) (hw : warp < 16) :
    LarkPartitionCollective.nextCohort (program repaired) (cohortThreads row warp 64)
      (prefixFold ops input (cohortThreads row warp 64) (initial p input outside)) =
      some (cohortThreads row warp 64) := by
  apply cohort_next repaired row warp 64 44 _ (by decide)
  · intro lane hl; exact (native_prefix_ready p ops input outside row warp hr hw lane hl).pc
  · intro t ht
    simp only [LarkPartitionCollective.isShuffle, ht]
    cases repaired <;> rfl

theorem native_prefix_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) :
    (prefixFold ops input (cohortThreads row warp 64) (initial p input outside)).trace.length = 5120 := by
  simpa only [cohortThreads, List.length_map, List.length_range, initial,
    LarkNonlinear.initial, List.length_nil, Nat.zero_add] using
    prefix_fold_trace_length ops input (cohortThreads row warp 64) (initial p input outside)

theorem native_prefix_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (_hr : row < p.rows) (_hw : warp < 16) :
    raceFree (geometry p)
      (prefixFold ops input (cohortThreads row warp 64) (initial p input outside)).trace = true :=
  initial_prefix_fold_race_free p ops input outside _

#print axioms cohort_coords
#print axioms cohort_native_threads
#print axioms cohort_complete32
#print axioms cohort_next
#print axioms native_prefix_step
#print axioms native_prefix_initial
#print axioms native_prefix_ready
#print axioms native_prefix_next
#print axioms native_prefix_trace_length
#print axioms native_prefix_race_free
end LarkNativeSglangRmsNorm
