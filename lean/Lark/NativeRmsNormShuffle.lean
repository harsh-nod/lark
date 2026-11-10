import Lark.NativeRmsNormPrefix

/-! Snapshot transport for the native wave64 and the active logical-16 cohort.
The geometry and source program are unchanged; a shuffle grants no memory fence.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def cohortBase (row warp : Nat) : Nat := row * 1024 + warp * 64
def cohortThreads (row warp width : Nat) : List Nat :=
  (List.range width).map (fun lane => cohortBase row warp + lane)

theorem cohort_mem (row warp width t : Nat) :
    t ∈ cohortThreads row warp width ↔ ∃ lane, lane < width ∧ t = cohortBase row warp + lane := by
  simp only [cohortThreads, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨lane, hl, he⟩
    exact ⟨lane, hl, he.symm⟩
  · rintro ⟨lane, hl, he⟩
    exact ⟨lane, hl, he.symm⟩

theorem cohort_coords (p : Shape) (row warp lane : Nat) (hw : warp < 16) (hl : lane < 64) :
    LarkPartitionCollective.nativeBase (geometry p) (cohortBase row warp + lane) = cohortBase row warp ∧
    LarkPartitionCollective.nativeLane (geometry p) (cohortBase row warp + lane) = lane := by
  have hmod : (row * 1024 + warp * 64 + lane) % 1024 = warp * 64 + lane := by omega
  have hdiv : (row * 1024 + warp * 64 + lane) / 1024 = row := by omega
  have hwdiv : (warp * 64 + lane) / 64 = warp := by omega
  have hlmod : (warp * 64 + lane) % 64 = lane := by omega
  simp only [LarkPartitionCollective.nativeBase, LarkPartitionCollective.nativeLane, geometry, cohortBase,
    hmod, hdiv, hwdiv, hlmod]
  trivial

theorem cohort_complete (p : Shape) (row warp width : Nat)
    (hw : warp < 16) (hwidth : 0 < width) (hb : width ≤ 64) :
    LarkPartitionCollective.completePartitions (geometry p) (cohortThreads row warp width) width = true := by
  apply List.all_eq_true.mpr
  intro t ht
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
  rcases cohort_coords p row warp lane hw (by omega) with ⟨hbase, hlane⟩
  rewrite [hbase, hlane, Nat.div_eq_of_lt hl]
  simp only [Nat.zero_mul, Nat.add_zero]
  apply List.all_eq_true.mpr
  intro peer hp
  apply List.contains_iff_mem.mpr
  exact (cohort_mem row warp width _).mpr ⟨peer, List.mem_range.mp hp, rfl⟩

theorem cohort_nodup (row warp width : Nat) : (cohortThreads row warp width).Nodup := by
  unfold cohortThreads
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (R := fun a b : Nat => a ≠ b) (by intro a b hab; omega) List.nodup_range

theorem cohort_head (row warp width : Nat) (hw : 0 < width) :
    (cohortThreads row warp width).head? = some (cohortBase row warp) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : width ≠ 0)
  rewrite [cohortThreads, List.range_eq_range', List.range'_succ]
  rfl

theorem cohort_uniform (p : Shape) (row warp width pc : Nat) (s : State α)
    (hw : warp < 16) (hb : width ≤ 64)
    (hp : ∀ lane, lane < width → s.pc (cohortBase row warp + lane) = pc) :
    (cohortThreads row warp width).all (fun t =>
      s.pc t == s.pc (cohortBase row warp) &&
      LarkPartitionCollective.nativeBase (geometry p) t ==
        LarkPartitionCollective.nativeBase (geometry p) (cohortBase row warp)) = true := by
  apply List.all_eq_true.mpr
  intro t ht
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
  have hpos : 0 < width := by omega
  have hp0 : s.pc (cohortBase row warp) = pc := by simpa only [Nat.add_zero] using hp 0 hpos
  have hb0 : LarkPartitionCollective.nativeBase (geometry p) (cohortBase row warp) = cohortBase row warp := by
    simpa only [Nat.add_zero] using (cohort_coords p row warp 0 hw (by decide)).1
  rewrite [hp lane hl, hp0, (cohort_coords p row warp lane hw (by omega)).1, hb0]
  simp

/-- A direct decomposition of the actual complete-partition scheduler. -/
theorem cohort_values (p : Shape) (row warp width pc : Nat) (s : State α)
    (hw : warp < 16) (hpos : 0 < width) (hb : width ≤ 64)
    (hs : [1, 2, 4, 8, 16, 32, 64].contains width = true)
    (hp : ∀ lane, lane < width → s.pc (cohortBase row warp + lane) = pc)
    (kind : ShuffleKind) (dest src : Nat) (selector : Index)
    (code : program[pc]? = some (.shuffle kind dest src selector width)) :
    LarkPartitionCollective.shuffleValues (geometry p) program (cohortThreads row warp width) s =
      ((cohortThreads row warp width).mapM (Gather.readValue (geometry p)
        (cohortThreads row warp width) s kind src selector width)).bind (fun vs => some (dest, vs)) := by
  have hn : cohortThreads row warp width ≠ [] := by
    have hm := (cohort_mem row warp width (cohortBase row warp)).mpr ⟨0, hpos, by omega⟩
    intro he
    simp [he] at hm
  have hguard : ¬ ((geometry p).warp ≠ 64 ∨ (geometry p).block % 64 ≠ 0 ∨
      cohortThreads row warp width = [] ∨ ¬ (cohortThreads row warp width).Nodup ∨
      64 < (cohortThreads row warp width).length) := by
    have hlen : (cohortThreads row warp width).length = width := by simp [cohortThreads]
    simp only [geometry, ne_eq, Nat.reduceMod, not_true_eq_false, hlen,
      hn, cohort_nodup, Nat.not_lt.mpr hb, or_self, not_false_eq_true]
  unfold LarkPartitionCollective.shuffleValues
  rewrite [if_neg hguard, cohort_head row warp width hpos]
  simp only [bind, pure, Option.bind]
  rewrite [cohort_uniform p row warp width pc s hw hb hp]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hp0 : s.pc (cohortBase row warp) = pc := by simpa only [Nat.add_zero] using hp 0 hpos
  rewrite [hp0, code]
  simp only [Option.bind, hs, cohort_complete p row warp width hw hpos hb,
    Bool.not_true, Bool.false_eq_true, or_self, ↓reduceIte]

def downPeer (width distance lane : Nat) : Nat :=
  if lane + distance < width then lane + distance else lane

theorem downPeer_bound (width distance lane : Nat) (hl : lane < width) :
    downPeer width distance lane < width := by
  unfold downPeer
  split <;> omega

theorem cohort_read (p : Shape) (row warp width distance lane : Nat) (s : State α)
    (values : Nat → α) (hw : warp < 16) (hpos : 0 < width) (hb : width ≤ 64)
    (hs : [1, 2, 4, 8, 16, 32, 64].contains width = true)
    (hd : distance < width) (hl : lane < width)
    (hr : ∀ l, l < width → s.regs (cohortBase row warp + l) 0 = some (values l)) :
    Gather.readValue (geometry p) (cohortThreads row warp width) s .down 0
      (.const (distance : Int)) width (cohortBase row warp + lane) =
      some (cohortBase row warp + lane, values (downPeer width distance lane)) := by
  have he : evalIndex (geometry p) (cohortBase row warp + lane) s (.const (distance : Int)) =
      some (distance : Int) := LarkReduction.int32_cast distance (by omega)
  have hc := cohort_coords p row warp lane hw (by omega)
  have hsource := LarkDownReduction.source_down width lane distance hpos hl hd hb hs
  have hpeer := downPeer_bound width distance lane hl
  have hmem : (cohortThreads row warp width).contains
      (cohortBase row warp + downPeer width distance lane) = true :=
    List.contains_iff_mem.mpr ((cohort_mem row warp width _).mpr ⟨_, hpeer, rfl⟩)
  unfold Gather.readValue
  rewrite [he]
  simp only [bind, pure, Option.bind, show ¬ (distance : Int) < 0 by omega, ↓reduceIte, Int.toNat_ofNat]
  change (do
    let selected ← sourceLane .down width (LarkPartitionCollective.nativeLane (geometry p)
      (cohortBase row warp + lane)) distance
    if !((cohortThreads row warp width).contains
      (LarkPartitionCollective.nativeBase (geometry p) (cohortBase row warp + lane) + selected)) then none
    else do
      let v ← s.regs (LarkPartitionCollective.nativeBase (geometry p)
        (cohortBase row warp + lane) + selected) 0
      pure (cohortBase row warp + lane, v)) = _
  rewrite [hc.2, hc.1, hsource]
  change (do
    if !((cohortThreads row warp width).contains
      (cohortBase row warp + downPeer width distance lane)) then none
    else do
      let v ← s.regs (cohortBase row warp + downPeer width distance lane) 0
      pure (cohortBase row warp + lane, v)) = _
  simp only [hmem, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr _ hpeer,
    bind, pure, Option.bind]

theorem snapshot_mapM (xs : List Nat) (f : Nat → Option α) (v : Nat → α)
    (h : ∀ t ∈ xs, f t = some (v t)) : xs.mapM f = some (xs.map v) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.mapM_cons, h a (by simp), Option.some_bind,
        ih (by intro t ht; exact h t (by simp [ht])), List.map_cons]
      rfl

def cohortSnapshot (p : Shape) (row warp width distance : Nat) (values : Nat → α) : List (Nat × α) :=
  (cohortThreads row warp width).map fun t =>
    (t, values (downPeer width distance (LarkPartitionCollective.nativeLane (geometry p) t)))

theorem cohort_down_values (p : Shape) (row warp width distance pc : Nat) (s : State α)
    (values : Nat → α) (hw : warp < 16) (hpos : 0 < width) (hb : width ≤ 64)
    (hs : [1, 2, 4, 8, 16, 32, 64].contains width = true) (hd : distance < width)
    (hp : ∀ lane, lane < width → s.pc (cohortBase row warp + lane) = pc)
    (hr : ∀ lane, lane < width → s.regs (cohortBase row warp + lane) 0 = some (values lane))
    (code : program[pc]? = some (.shuffle .down 1 0 (.const (distance : Int)) width)) :
    LarkPartitionCollective.shuffleValues (geometry p) program (cohortThreads row warp width) s =
      some (1, cohortSnapshot p row warp width distance values) := by
  rewrite [cohort_values p row warp width pc s hw hpos hb hs hp .down 1 0 _ code]
  have hm := snapshot_mapM (cohortThreads row warp width)
    (Gather.readValue (geometry p) (cohortThreads row warp width) s .down 0 (.const (distance : Int)) width)
    (fun t => (t, values (downPeer width distance (LarkPartitionCollective.nativeLane (geometry p) t))))
    (by
      intro t ht
      obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
      dsimp only
      rewrite [(cohort_coords p row warp lane hw (by omega)).2]
      exact cohort_read p row warp width distance lane s values hw hpos hb hs hd hl hr)
  rewrite [hm]
  rfl

theorem cohort_down_shuffle (p : Shape) (row warp width distance pc : Nat) (s : State α)
    (values : Nat → α) (hw : warp < 16) (hpos : 0 < width) (hb : width ≤ 64)
    (hs : [1, 2, 4, 8, 16, 32, 64].contains width = true) (hd : distance < width)
    (hp : ∀ lane, lane < width → s.pc (cohortBase row warp + lane) = pc)
    (hr : ∀ lane, lane < width → s.regs (cohortBase row warp + lane) 0 = some (values lane))
    (code : program[pc]? = some (.shuffle .down 1 0 (.const (distance : Int)) width)) :
    LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row warp width) s =
      some (shuffleUpdates 1 (cohortSnapshot p row warp width distance values) s) := by
  unfold LarkPartitionCollective.runShuffle
  rewrite [cohort_down_values p row warp width distance pc s values hw hpos hb hs hd hp hr code]
  rfl

theorem snapshot_lookup (ts : List Nat) (values : Nat → α) (t : Nat) (ht : t ∈ ts) :
    List.lookup t (ts.map (fun u => (u, values u))) = some (values t) := by
  induction ts with
  | nil => simp at ht
  | cons a ts ih =>
      by_cases he : t = a
      · subst t; simp
      · have hm : t ∈ ts := by simpa [he] using ht
        have hb : (t == a) = false := by simp [he]
        simpa only [List.map_cons, List.lookup_cons, hb] using ih hm

theorem snapshot_lookup_other (ts : List Nat) (values : Nat → α) (t : Nat) (ht : t ∉ ts) :
    List.lookup t (ts.map (fun u => (u, values u))) = none := by
  induction ts with
  | nil => rfl
  | cons a ts ih =>
      have hne : t ≠ a := by intro he; subst t; simp at ht
      have hn : t ∉ ts := by intro hm; exact ht (by simp [hm])
      simpa only [List.map_cons, List.lookup_cons, show (t == a) = false by simp [hne]] using ih hn

theorem snapshot_any (ts : List Nat) (values : Nat → α) (t : Nat) :
    (ts.map (fun u => (u, values u))).any (fun pair => pair.1 == t) = decide (t ∈ ts) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    obtain ⟨pair, hm, he⟩ := List.any_eq_true.mp h
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hm
    have he : u = t := by simpa only [beq_iff_eq] using he
    exact he ▸ hu
  · intro ht
    exact List.any_eq_true.mpr ⟨(t, values t), List.mem_map.mpr ⟨t, ht, rfl⟩, by simp⟩

theorem cohort_shuffled_fields (p : Shape) (row warp width distance lane : Nat)
    (values : Nat → α) (s : State α) (hw : warp < 16) (hb : width ≤ 64) (hl : lane < width) :
    let next := shuffleUpdates 1 (cohortSnapshot p row warp width distance values) s
    let t := cohortBase row warp + lane
    next.pc t = s.pc t + 1 ∧ next.regs t 0 = s.regs t 0 ∧
      next.regs t 1 = some (values (downPeer width distance lane)) := by
  have ht := (cohort_mem row warp width _).mpr ⟨lane, hl, rfl⟩
  dsimp only
  simp only [shuffleUpdates, cohortSnapshot, snapshot_any, ht, decide_true, ↓reduceIte]
  rewrite [snapshot_lookup _ _ _ ht, (cohort_coords p row warp lane hw (by omega)).2]
  trivial

theorem cohort_shuffled_other (p : Shape) (row warp width distance t : Nat)
    (values : Nat → α) (s : State α) (ht : t ∉ cohortThreads row warp width) :
    let next := shuffleUpdates 1 (cohortSnapshot p row warp width distance values) s
    next.pc t = s.pc t ∧ next.regs t = s.regs t := by
  dsimp only
  constructor
  · simp [shuffleUpdates, cohortSnapshot, snapshot_any, ht]
  · funext reg
    by_cases hr : reg = 1
    · subst reg
      simp only [shuffleUpdates, cohortSnapshot, ↓reduceIte, snapshot_lookup_other _ _ _ ht]
    · simp [shuffleUpdates, hr]

theorem cohort_next (row warp width pc : Nat) (s : State α) (hpos : 0 < width)
    (hp : ∀ lane, lane < width → s.pc (cohortBase row warp + lane) = pc)
    (kind : ShuffleKind) (dest src : Nat) (selector : Index)
    (code : program[pc]? = some (.shuffle kind dest src selector width)) :
    LarkPartitionCollective.nextCohort program (cohortThreads row warp width) s =
      some (cohortThreads row warp width) := by
  have hfilter : (cohortThreads row warp width).filter
      (LarkPartitionCollective.isShuffle program s) = cohortThreads row warp width := by
    apply List.filter_eq_self.mpr
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
    simp [LarkPartitionCollective.isShuffle, hp lane hl, code]
  have hp0 : s.pc (cohortBase row warp) = pc := by simpa only [Nat.add_zero] using hp 0 hpos
  unfold LarkPartitionCollective.nextCohort
  rewrite [hfilter, cohort_head row warp width hpos]
  simp only [bind, pure, Option.bind]
  congr 1
  apply List.filter_eq_self.mpr
  intro t ht
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp width t).mp ht
  simp [hp lane hl, hp0]

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

#print axioms cohort_complete
#print axioms cohort_values
#print axioms cohort_read
#print axioms cohort_down_shuffle
#print axioms cohort_shuffled_fields
#print axioms cohort_shuffled_other
#print axioms cohort_next
#print axioms cohort_native_threads
end LarkNativeRmsNorm
