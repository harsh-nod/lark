import Lark.NativeSoftmaxMaxCohort

/-! Actual snapshot transport for complete logical32 downward partitions inside a
physical wave64. The two groups remain separate and arithmetic is arbitrary.
No commutativity, cross-partition transport or synchronization fence is assumed.
-/
namespace LarkNativeSoftmax
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def downPeer32 (lane distance : Nat) : Nat := if lane % 32 + distance < 32 then lane + distance else lane

theorem down_source32 (lane distance : Nat) (hl : lane < 64) (hm : distance < 32) :
    sourceLane .down 32 lane distance = some (downPeer32 lane distance) := by
  have table : ∀ l : Fin 64, ∀ m : Fin 32,
      sourceLane .down 32 l.val m.val = some (downPeer32 l.val m.val) := by decide
  exact table ⟨lane, hl⟩ ⟨distance, hm⟩

theorem down_peer_bound (active lane distance : Nat) (ha : active = 32 ∨ active = 64)
    (hl : lane < active) (hm : distance < 32) : downPeer32 lane distance < active := by
  have lower : ∀ l : Fin 32, ∀ m : Fin 32, downPeer32 l.val m.val < 32 := by decide
  have native : ∀ l : Fin 64, ∀ m : Fin 32, downPeer32 l.val m.val < 64 := by decide
  rcases ha with rfl | rfl
  · exact lower ⟨lane, hl⟩ ⟨distance, hm⟩
  · exact native ⟨lane, hl⟩ ⟨distance, hm⟩

theorem down_peer_partition (lane distance : Nat) (hl : lane < 64) (hm : distance < 32) :
    downPeer32 lane distance / 32 = lane / 32 := by
  have table : ∀ l : Fin 64, ∀ m : Fin 32, downPeer32 l.val m.val / 32 = l.val / 32 := by decide
  exact table ⟨lane, hl⟩ ⟨distance, hm⟩

theorem cohort_uniform (p : Shape) (row warp active pc : Nat) (s : State α)
    (hw : warp < 16) (ha : active ≤ 64) (hpos : 0 < active)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc) :
    (cohortThreads row warp active).all (fun t =>
      s.pc t == s.pc (cohortBase row warp) &&
      LarkPartitionCollective.nativeBase (geometry p) t ==
        LarkPartitionCollective.nativeBase (geometry p) (cohortBase row warp)) = true := by
  apply List.all_eq_true.mpr
  intro t ht
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
  have hp0 : s.pc (cohortBase row warp) = pc := by simpa only [Nat.add_zero] using hp 0 hpos
  have hb0 : LarkPartitionCollective.nativeBase (geometry p) (cohortBase row warp) = cohortBase row warp := by
    simpa only [Nat.add_zero] using (cohort_coords p row warp 0 hw (by decide)).1
  rewrite [hp lane hl, hp0, (cohort_coords p row warp lane hw (by omega)).1, hb0]
  simp

theorem cohort_values32 (p : Shape) (guarded : Bool) (row warp active pc distance : Nat) (s : State α)
    (hw : warp < 16) (ha : active = 32 ∨ active = 64)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc)
    (code : (program guarded)[pc]? = some (.shuffle .down 2 0 (.const (distance : Int)) 32)) :
    LarkPartitionCollective.shuffleValues (geometry p) (program guarded) (cohortThreads row warp active) s =
      ((cohortThreads row warp active).mapM (Gather.readValue (geometry p)
        (cohortThreads row warp active) s .down 0 (.const (distance : Int)) 32)).bind (fun vs => some (2, vs)) := by
  have hpos : 0 < active := by omega
  have hb : active ≤ 64 := by omega
  have hn : cohortThreads row warp active ≠ [] := by
    have hm := (cohort_mem row warp active (cohortBase row warp)).mpr ⟨0, hpos, by omega⟩
    intro he; simp [he] at hm
  have hguard : ¬ ((geometry p).warp ≠ 64 ∨ (geometry p).block % 64 ≠ 0 ∨
      cohortThreads row warp active = [] ∨ ¬ (cohortThreads row warp active).Nodup ∨
      64 < (cohortThreads row warp active).length) := by
    have hlen : (cohortThreads row warp active).length = active := by simp [cohortThreads]
    simp only [geometry, ne_eq, Nat.reduceMod, not_true_eq_false, hlen,
      hn, cohort_nodup, Nat.not_lt.mpr hb, or_self, not_false_eq_true]
  unfold LarkPartitionCollective.shuffleValues
  rewrite [if_neg hguard, cohort_head row warp active hpos]
  simp only [bind, pure, Option.bind]
  rewrite [cohort_uniform p row warp active pc s hw hb hpos hp]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hp0 : s.pc (cohortBase row warp) = pc := by simpa only [Nat.add_zero] using hp 0 hpos
  rewrite [hp0, code]
  simp only [Option.bind, show [1,2,4,8,16,32,64].contains 32 = true by decide,
    cohort_complete32 p row warp active hw ha, Bool.not_true, Bool.false_eq_true, or_self, ↓reduceIte]

theorem cohort_read32 (p : Shape) (row warp active distance lane : Nat) (s : State α)
    (values : Nat → α) (hw : warp < 16) (ha : active = 32 ∨ active = 64)
    (hm : distance < 32) (hl : lane < active)
    (hr : ∀ l, l < active → s.regs (cohortBase row warp + l) 0 = some (values l)) :
    Gather.readValue (geometry p) (cohortThreads row warp active) s .down 0
      (.const (distance : Int)) 32 (cohortBase row warp + lane) =
      some (cohortBase row warp + lane, values (downPeer32 lane distance)) := by
  have he : evalIndex (geometry p) (cohortBase row warp + lane) s (.const (distance : Int)) =
      some (distance : Int) := LarkReduction.int32_cast distance (by omega)
  have hc := cohort_coords p row warp lane hw (by omega)
  have hsource := down_source32 lane distance (by omega) hm
  have hpeer := down_peer_bound active lane distance ha hl hm
  have hmem : (cohortThreads row warp active).contains (cohortBase row warp + downPeer32 lane distance) = true :=
    List.contains_iff_mem.mpr ((cohort_mem row warp active _).mpr ⟨_, hpeer, rfl⟩)
  unfold Gather.readValue
  rewrite [he]
  simp only [bind, pure, Option.bind, show ¬ (distance : Int) < 0 by omega, ↓reduceIte, Int.toNat_ofNat]
  change (do
    let selected ← sourceLane .down 32 (LarkPartitionCollective.nativeLane (geometry p)
      (cohortBase row warp + lane)) distance
    if !((cohortThreads row warp active).contains
      (LarkPartitionCollective.nativeBase (geometry p) (cohortBase row warp + lane) + selected)) then none
    else do
      let v ← s.regs (LarkPartitionCollective.nativeBase (geometry p) (cohortBase row warp + lane) + selected) 0
      pure (cohortBase row warp + lane, v)) = _
  rewrite [hc.2, hc.1, hsource]
  simp only [hmem, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr _ hpeer, bind, pure, Option.bind]

theorem snapshot_mapM (xs : List Nat) (f : Nat → Option α) (v : Nat → α)
    (h : ∀ t ∈ xs, f t = some (v t)) : xs.mapM f = some (xs.map v) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      simp only [List.mapM_cons, h a (by simp), Option.some_bind,
        ih (by intro t ht; exact h t (by simp [ht])), List.map_cons]
      rfl

def downSnapshot (p : Shape) (row warp active distance : Nat) (values : Nat → α) : List (Nat × α) :=
  (cohortThreads row warp active).map fun t =>
    (t, values (downPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) distance))

theorem cohort_down_values (p : Shape) (guarded : Bool) (row warp active distance pc : Nat) (s : State α)
    (values : Nat → α) (hw : warp < 16) (ha : active = 32 ∨ active = 64) (hm : distance < 32)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc)
    (hr : ∀ lane, lane < active → s.regs (cohortBase row warp + lane) 0 = some (values lane))
    (code : (program guarded)[pc]? = some (.shuffle .down 2 0 (.const (distance : Int)) 32)) :
    LarkPartitionCollective.shuffleValues (geometry p) (program guarded) (cohortThreads row warp active) s =
      some (2, downSnapshot p row warp active distance values) := by
  rewrite [cohort_values32 p guarded row warp active pc distance s hw ha hp code]
  have hmapping := snapshot_mapM (cohortThreads row warp active)
    (Gather.readValue (geometry p) (cohortThreads row warp active) s .down 0 (.const (distance : Int)) 32)
    (fun t => (t, values (downPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) distance)))
    (by
      intro t ht
      obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
      dsimp only
      rewrite [(cohort_coords p row warp lane hw (by omega)).2]
      exact cohort_read32 p row warp active distance lane s values hw ha hm hl hr)
  rewrite [hmapping]
  rfl

theorem cohort_down_shuffle (p : Shape) (guarded : Bool) (row warp active distance pc : Nat) (s : State α)
    (values : Nat → α) (hw : warp < 16) (ha : active = 32 ∨ active = 64) (hm : distance < 32)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc)
    (hr : ∀ lane, lane < active → s.regs (cohortBase row warp + lane) 0 = some (values lane))
    (code : (program guarded)[pc]? = some (.shuffle .down 2 0 (.const (distance : Int)) 32)) :
    LarkPartitionCollective.runShuffle (geometry p) (program guarded) (cohortThreads row warp active) s =
      some (shuffleUpdates 2 (downSnapshot p row warp active distance values) s) := by
  unfold LarkPartitionCollective.runShuffle
  rewrite [cohort_down_values p guarded row warp active distance pc s values hw ha hm hp hr code]
  rfl

#print axioms down_source32
#print axioms down_peer_bound
#print axioms down_peer_partition
#print axioms cohort_uniform
#print axioms cohort_values32
#print axioms cohort_read32
#print axioms snapshot_mapM
#print axioms cohort_down_values
#print axioms cohort_down_shuffle
end LarkNativeSoftmax
