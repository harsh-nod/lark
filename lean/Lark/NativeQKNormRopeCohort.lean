import Lark.NativeQKNormRopePrepareFold

/-! Actual physical wave64 cohorts in the native 256-thread launch. -/
namespace LarkNativeQKNormRope
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def cohortBase (block warp : Nat) : Nat := block * 256 + warp * 64
def cohortThreads (block warp active : Nat) : List Nat :=
  (List.range active).map (fun lane => cohortBase block warp + lane)

theorem cohort_mem (block warp active t : Nat) :
    t ∈ cohortThreads block warp active ↔ ∃ lane, lane < active ∧ t = cohortBase block warp + lane := by
  simp only [cohortThreads, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨lane, hl, he⟩; exact ⟨lane, hl, he.symm⟩
  · rintro ⟨lane, hl, he⟩; exact ⟨lane, hl, he.symm⟩

theorem cohort_nodup (block warp active : Nat) : (cohortThreads block warp active).Nodup := by
  unfold cohortThreads
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (R := fun a b : Nat => a ≠ b) (by intro a b hab; omega) List.nodup_range

theorem cohort_arithmetic (block warp lane : Nat) (hw : warp < 4) (hl : lane < 64) :
    (cohortBase block warp + lane) / 256 = block ∧
    (cohortBase block warp + lane) % 256 = warp * 64 + lane ∧
    ((cohortBase block warp + lane) % 256) % 64 = lane := by
  unfold cohortBase
  omega

theorem cohort_coords (p : Shape) (block warp lane : Nat) (hw : warp < 4) (hl : lane < 64) :
    LarkPartitionCollective.nativeBase (geometry p) (cohortBase block warp + lane) = cohortBase block warp ∧
    LarkPartitionCollective.nativeLane (geometry p) (cohortBase block warp + lane) = lane := by
  have h := cohort_arithmetic block warp lane hw hl
  simp only [LarkPartitionCollective.nativeBase, LarkPartitionCollective.nativeLane, geometry,
    h.1, h.2.1, h.2.2]
  have hd : (warp * 64 + lane) / 64 = warp := by omega
  have hm : (warp * 64 + lane) % 64 = lane := by omega
  simp only [hd, hm, cohortBase, and_self]

theorem cohort_bound (p : Shape) (block warp active : Nat) (hb : block < p.rows * 5)
    (hw : warp < 4) (ha : active ≤ 64) : ∀ t ∈ cohortThreads block warp active, t < p.rows * 1280 := by
  intro t ht
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
  unfold cohortBase
  omega

theorem cohort_head (block warp active : Nat) (ha : 0 < active) :
    (cohortThreads block warp active).head? = some (cohortBase block warp) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : active ≠ 0)
  rewrite [cohortThreads, List.range_eq_range', List.range'_succ]
  rfl

theorem cohort_native_threads (p : Shape) (block warp : Nat) (hw : warp < 4) :
    warpThreads (geometry p) block warp = cohortThreads block warp 64 := by
  have all : ∀ w : Fin 4,
      (List.range 256).filter (fun t => t / 64 == w.val) =
        (List.range 64).map (fun lane => w.val * 64 + lane) := by decide
  simp only [warpThreads, geometry, all ⟨warp, hw⟩, List.map_map, cohortThreads, cohortBase]
  apply List.map_inj_left.mpr
  intro lane hl
  dsimp only [Function.comp_apply]
  omega

theorem cohort_complete32 (p : Shape) (block warp active : Nat) (hw : warp < 4)
    (ha : active = 32 ∨ active = 64) :
    LarkPartitionCollective.completePartitions (geometry p) (cohortThreads block warp active) 32 = true := by
  apply List.all_eq_true.mpr
  intro t ht
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
  have hc := cohort_coords p block warp lane hw (by omega)
  rw [hc.1, hc.2]
  apply List.all_eq_true.mpr
  intro peer hp
  have hp := List.mem_range.mp hp
  apply List.contains_iff_mem.mpr
  exact (cohort_mem block warp active _).mpr ⟨lane / 32 * 32 + peer, by omega, by omega⟩

theorem cohort_next (neox : Bool) (block warp active pc : Nat) (s : State α) (ha : 0 < active)
    (hp : ∀ lane, lane < active → s.pc (cohortBase block warp + lane) = pc)
    (hs : ∀ t, s.pc t = pc → LarkPartitionCollective.isShuffle (program neox) s t = true) :
    LarkPartitionCollective.nextCohort (program neox) (cohortThreads block warp active) s =
      some (cohortThreads block warp active) := by
  have hp0 : s.pc (cohortBase block warp) = pc := by simpa only [Nat.add_zero] using hp 0 ha
  have hf : (cohortThreads block warp active).filter (LarkPartitionCollective.isShuffle (program neox) s) =
      cohortThreads block warp active := by
    apply List.filter_eq_self.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
    exact hs _ (hp lane hl)
  unfold LarkPartitionCollective.nextCohort
  rw [hf, cohort_head block warp active ha]
  simp only [bind, pure, Option.some_bind]
  congr 1
  apply List.filter_eq_self.mpr
  intro t ht
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
  simp [hp lane hl, hp0]

def continueCohort (p : Shape) (neox : Bool) (ops : Ops α) (ts : List Nat)
    (n : Nat) (s : State α) : Option (State α) := do
  match LarkPartitionCollective.nextCohort (program neox) ts s with
  | some cohort =>
    let next ← LarkPartitionCollective.runShuffle (geometry p) (program neox) cohort s
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program neox) ts n next
  | none =>
    let cut ← LarkCollective.converged (program neox) ts s
    if cut = .warp then
      LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program neox) ts n (resume ts .warp s)
    else some s

theorem run_warp_continue (p : Shape) (neox : Bool) (ops : Ops α) (ts : List Nat) (n : Nat) (s : State α) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program neox) ts (n + 1) s =
      (ts.foldlM (fun s t => LarkCollective.runLane ops (layout p) (geometry p) (program neox) t fuel.lane s) s).bind
        (continueCohort p neox ops ts n) := rfl

theorem native_prepare_step (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (block warp n : Nat) (s : State α) (hb : block < p.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program neox)
      (warpThreads (geometry p) block warp) (n + 1) s =
      continueCohort p neox ops (cohortThreads block warp 64) n
        (prepareFold ops input (cohortThreads block warp 64) s) := by
  rw [cohort_native_threads p block warp hw, run_warp_continue,
    prepare_fold_run p neox ops input _ s (cohort_nodup block warp 64)
      (cohort_bound p block warp 64 hb hw (by decide)) hp hr]
  rfl

theorem native_prepare_initial (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (block warp n : Nat) (hb : block < p.rows * 5) (hw : warp < 4) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program neox)
      (warpThreads (geometry p) block warp) (n + 1) (initial (layout p) input outside) =
      continueCohort p neox ops (cohortThreads block warp 64) n
        (prepareFold ops input (cohortThreads block warp 64) (initial (layout p) input outside)) :=
  native_prepare_step p neox ops input block warp n _ hb hw (by intro t ht; rfl) (initial_reads p input outside)

theorem native_prepare_ready (ops : Ops α) (input : Nat → Nat → α) (block warp lane : Nat)
    (s : State α) (hl : lane < 64) : PrepareReady ops input (cohortBase block warp + lane)
      (prepareFold ops input (cohortThreads block warp 64) s) :=
  prepare_fold_member ops input _ s (cohort_nodup block warp 64) _
    ((cohort_mem block warp 64 _).mpr ⟨lane, hl, rfl⟩)

theorem native_prepare_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (block warp : Nat) :
    raceFree (geometry p)
      (prepareFold ops input (cohortThreads block warp 64) (initial (layout p) input outside)).trace = true :=
  race_free p _ (prepare_fold_good ops input _ _ (by intro a ha; cases ha))

#print axioms cohort_mem
#print axioms cohort_nodup
#print axioms cohort_arithmetic
#print axioms cohort_coords
#print axioms cohort_bound
#print axioms cohort_head
#print axioms cohort_native_threads
#print axioms cohort_complete32
#print axioms cohort_next
#print axioms run_warp_continue
#print axioms native_prepare_step
#print axioms native_prepare_initial
#print axioms native_prepare_ready
#print axioms native_prepare_race_free
end LarkNativeQKNormRope
