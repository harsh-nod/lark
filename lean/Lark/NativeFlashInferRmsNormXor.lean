import Lark.NativeFlashInferRmsNormCohort

/-! Actual snapshot transport for complete logical32 XOR partitions inside a
physical wave64. The two groups remain separate and arithmetic is arbitrary.
No commutativity, cross-partition transport or synchronization fence is assumed.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def xorPeer32 (lane mask : Nat) : Nat := lane / 32 * 32 + Nat.xor (lane % 32) mask

theorem xor_source32 (lane mask : Nat) (hl : lane < 64) (hm : mask < 32) :
    sourceLane .xor 32 lane mask = some (xorPeer32 lane mask) := by
  have table : ∀ l : Fin 64, ∀ m : Fin 32,
      sourceLane .xor 32 l.val m.val = some (xorPeer32 l.val m.val) := by decide
  exact table ⟨lane, hl⟩ ⟨mask, hm⟩

theorem xor_peer_bound (active lane mask : Nat) (ha : active = 32 ∨ active = 64)
    (hl : lane < active) (hm : mask < 32) : xorPeer32 lane mask < active := by
  have lower : ∀ l : Fin 32, ∀ m : Fin 32, xorPeer32 l.val m.val < 32 := by decide
  have native : ∀ l : Fin 64, ∀ m : Fin 32, xorPeer32 l.val m.val < 64 := by decide
  rcases ha with rfl | rfl
  · exact lower ⟨lane, hl⟩ ⟨mask, hm⟩
  · exact native ⟨lane, hl⟩ ⟨mask, hm⟩

theorem xor_peer_partition (lane mask : Nat) (hl : lane < 64) (hm : mask < 32) :
    xorPeer32 lane mask / 32 = lane / 32 := by
  have table : ∀ l : Fin 64, ∀ m : Fin 32, xorPeer32 l.val m.val / 32 = l.val / 32 := by decide
  exact table ⟨lane, hl⟩ ⟨mask, hm⟩

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

theorem cohort_values32 (p : Shape) (row warp active pc mask : Nat) (s : State α)
    (hw : warp < 16) (ha : active = 32 ∨ active = 64)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc)
    (code : program[pc]? = some (.shuffle .xor 1 0 (.const (mask : Int)) 32)) :
    LarkPartitionCollective.shuffleValues (geometry p) program (cohortThreads row warp active) s =
      ((cohortThreads row warp active).mapM (Gather.readValue (geometry p)
        (cohortThreads row warp active) s .xor 0 (.const (mask : Int)) 32)).bind (fun vs => some (1, vs)) := by
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

theorem cohort_read32 (p : Shape) (row warp active mask lane : Nat) (s : State α)
    (values : Nat → α) (hw : warp < 16) (ha : active = 32 ∨ active = 64)
    (hm : mask < 32) (hl : lane < active)
    (hr : ∀ l, l < active → s.regs (cohortBase row warp + l) 0 = some (values l)) :
    Gather.readValue (geometry p) (cohortThreads row warp active) s .xor 0
      (.const (mask : Int)) 32 (cohortBase row warp + lane) =
      some (cohortBase row warp + lane, values (xorPeer32 lane mask)) := by
  have he : evalIndex (geometry p) (cohortBase row warp + lane) s (.const (mask : Int)) =
      some (mask : Int) := LarkReduction.int32_cast mask (by omega)
  have hc := cohort_coords p row warp lane hw (by omega)
  have hsource := xor_source32 lane mask (by omega) hm
  have hpeer := xor_peer_bound active lane mask ha hl hm
  have hmem : (cohortThreads row warp active).contains (cohortBase row warp + xorPeer32 lane mask) = true :=
    List.contains_iff_mem.mpr ((cohort_mem row warp active _).mpr ⟨_, hpeer, rfl⟩)
  unfold Gather.readValue
  rewrite [he]
  simp only [bind, pure, Option.bind, show ¬ (mask : Int) < 0 by omega, ↓reduceIte, Int.toNat_ofNat]
  change (do
    let selected ← sourceLane .xor 32 (LarkPartitionCollective.nativeLane (geometry p)
      (cohortBase row warp + lane)) mask
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

def xorSnapshot (p : Shape) (row warp active mask : Nat) (values : Nat → α) : List (Nat × α) :=
  (cohortThreads row warp active).map fun t =>
    (t, values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) mask))

theorem cohort_xor_values (p : Shape) (row warp active mask pc : Nat) (s : State α)
    (values : Nat → α) (hw : warp < 16) (ha : active = 32 ∨ active = 64) (hm : mask < 32)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc)
    (hr : ∀ lane, lane < active → s.regs (cohortBase row warp + lane) 0 = some (values lane))
    (code : program[pc]? = some (.shuffle .xor 1 0 (.const (mask : Int)) 32)) :
    LarkPartitionCollective.shuffleValues (geometry p) program (cohortThreads row warp active) s =
      some (1, xorSnapshot p row warp active mask values) := by
  rewrite [cohort_values32 p row warp active pc mask s hw ha hp code]
  have hmapping := snapshot_mapM (cohortThreads row warp active)
    (Gather.readValue (geometry p) (cohortThreads row warp active) s .xor 0 (.const (mask : Int)) 32)
    (fun t => (t, values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) mask)))
    (by
      intro t ht
      obtain ⟨lane, hl, rfl⟩ := (cohort_mem row warp active t).mp ht
      dsimp only
      rewrite [(cohort_coords p row warp lane hw (by omega)).2]
      exact cohort_read32 p row warp active mask lane s values hw ha hm hl hr)
  rewrite [hmapping]
  rfl

theorem cohort_xor_shuffle (p : Shape) (row warp active mask pc : Nat) (s : State α)
    (values : Nat → α) (hw : warp < 16) (ha : active = 32 ∨ active = 64) (hm : mask < 32)
    (hp : ∀ lane, lane < active → s.pc (cohortBase row warp + lane) = pc)
    (hr : ∀ lane, lane < active → s.regs (cohortBase row warp + lane) 0 = some (values lane))
    (code : program[pc]? = some (.shuffle .xor 1 0 (.const (mask : Int)) 32)) :
    LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row warp active) s =
      some (shuffleUpdates 1 (xorSnapshot p row warp active mask values) s) := by
  unfold LarkPartitionCollective.runShuffle
  rewrite [cohort_xor_values p row warp active mask pc s values hw ha hm hp hr code]
  rfl

theorem native_first_shuffle (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) (hr : row < p.rows) (hw : warp < 16) :
    LarkPartitionCollective.runShuffle (geometry p) program (cohortThreads row warp 64)
      (prefixFold ops input (cohortThreads row warp 64) (initial p input outside)) =
      some (shuffleUpdates 1 (xorSnapshot p row warp 64 16
        (fun lane => threadSum ops input row (warp * 64 + lane)))
        (prefixFold ops input (cohortThreads row warp 64) (initial p input outside))) := by
  apply cohort_xor_shuffle p row warp 64 16 19 _ _ hw (Or.inr rfl) (by decide)
  · intro lane hl; exact (native_prefix_ready p ops input outside row warp hr hw lane hl).pc
  · intro lane hl
    have h := (native_prefix_ready p ops input outside row warp hr hw lane hl).accumulator
    have coords := cohort_arithmetic row warp lane hw hl
    simpa only [coords.1, coords.2.1] using h
  · decide

theorem native_prefix_snapshot (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp n : Nat) (hr : row < p.rows) (hw : warp < 16) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
      (warpThreads (geometry p) row warp) (n + 1) (initial p input outside) =
      LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel program
        (cohortThreads row warp 64) n
        (shuffleUpdates 1 (xorSnapshot p row warp 64 16
          (fun lane => threadSum ops input row (warp * 64 + lane)))
          (prefixFold ops input (cohortThreads row warp 64) (initial p input outside))) := by
  rewrite [native_prefix_initial p ops input outside row warp n hr hw]
  unfold continueCohort
  simp only [native_prefix_next p ops input outside row warp hr hw,
    native_first_shuffle p ops input outside row warp hr hw, Option.some_bind]
  rfl

#print axioms xor_source32
#print axioms xor_peer_bound
#print axioms xor_peer_partition
#print axioms cohort_values32
#print axioms cohort_read32
#print axioms cohort_xor_values
#print axioms cohort_xor_shuffle
#print axioms native_first_shuffle
#print axioms native_prefix_snapshot
end LarkNativeFlashInferRmsNorm
