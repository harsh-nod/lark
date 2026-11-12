import Lark.NativeQKNormRopeCohort

/-! Actual snapshot transport for both logical32 groups in physical wave64.
The source/destination registers are parameters for reduction and RoPE reuse. -/
namespace LarkNativeQKNormRope
open LarkNonlinear LarkCollective
open LarkReduction (int32_cast)
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

theorem xor_peer_same_head (block warp lane mask : Nat) (hl : lane < 64) (hm : mask < 32) :
    (cohortBase block warp + xorPeer32 lane mask) / 32 = (cohortBase block warp + lane) / 32 := by
  have hp := xor_peer_partition lane mask hl hm
  have hb := xor_peer_bound 64 lane mask (Or.inr rfl) hl hm
  unfold cohortBase
  omega

theorem cohort_uniform (p : Shape) (block warp active pc : Nat) (s : State α)
    (hw : warp < 4) (ha : active ≤ 64) (hpos : 0 < active)
    (hp : ∀ lane, lane < active → s.pc (cohortBase block warp + lane) = pc) :
    (cohortThreads block warp active).all (fun t =>
      s.pc t == s.pc (cohortBase block warp) &&
      LarkPartitionCollective.nativeBase (geometry p) t ==
        LarkPartitionCollective.nativeBase (geometry p) (cohortBase block warp)) = true := by
  apply List.all_eq_true.mpr
  intro t ht
  obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
  have hp0 : s.pc (cohortBase block warp) = pc := by simpa only [Nat.add_zero] using hp 0 hpos
  have hb0 : LarkPartitionCollective.nativeBase (geometry p) (cohortBase block warp) = cohortBase block warp := by
    simpa only [Nat.add_zero] using (cohort_coords p block warp 0 hw (by decide)).1
  rw [hp lane hl, hp0, (cohort_coords p block warp lane hw (by omega)).1, hb0]
  simp

theorem cohort_values32 (p : Shape) (neox : Bool) (block warp active pc mask dest src : Nat)
    (s : State α) (hw : warp < 4) (ha : active = 32 ∨ active = 64)
    (hp : ∀ lane, lane < active → s.pc (cohortBase block warp + lane) = pc)
    (code : (program neox)[pc]? = some (.shuffle .xor dest src (.const (mask : Int)) 32)) :
    LarkPartitionCollective.shuffleValues (geometry p) (program neox) (cohortThreads block warp active) s =
      ((cohortThreads block warp active).mapM (Gather.readValue (geometry p)
        (cohortThreads block warp active) s .xor src (.const (mask : Int)) 32)).bind (fun vs => some (dest, vs)) := by
  have hpos : 0 < active := by omega
  have hb : active ≤ 64 := by omega
  have hn : cohortThreads block warp active ≠ [] := by
    have hm := (cohort_mem block warp active (cohortBase block warp)).mpr ⟨0, hpos, by omega⟩
    intro he; simp [he] at hm
  have hguard : ¬ ((geometry p).warp ≠ 64 ∨ (geometry p).block % 64 ≠ 0 ∨
      cohortThreads block warp active = [] ∨ ¬ (cohortThreads block warp active).Nodup ∨
      64 < (cohortThreads block warp active).length) := by
    have hlen : (cohortThreads block warp active).length = active := by simp [cohortThreads]
    simp only [geometry, ne_eq, Nat.reduceMod, not_true_eq_false, hlen,
      hn, cohort_nodup, Nat.not_lt.mpr hb, or_self, not_false_eq_true]
  unfold LarkPartitionCollective.shuffleValues
  rw [if_neg hguard, cohort_head block warp active hpos]
  simp only [bind, pure, Option.bind]
  rw [cohort_uniform p block warp active pc s hw hb hpos hp]
  simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  have hp0 : s.pc (cohortBase block warp) = pc := by simpa only [Nat.add_zero] using hp 0 hpos
  rw [hp0, code]
  simp only [Option.bind, show [1,2,4,8,16,32,64].contains 32 = true by decide,
    cohort_complete32 p block warp active hw ha, Bool.not_true, Bool.false_eq_true, or_self, ↓reduceIte]

theorem cohort_read32 (p : Shape) (block warp active mask lane src : Nat) (s : State α)
    (values : Nat → α) (hw : warp < 4) (ha : active = 32 ∨ active = 64)
    (hm : mask < 32) (hl : lane < active)
    (hr : ∀ l, l < active → s.regs (cohortBase block warp + l) src = some (values l)) :
    Gather.readValue (geometry p) (cohortThreads block warp active) s .xor src
      (.const (mask : Int)) 32 (cohortBase block warp + lane) =
      some (cohortBase block warp + lane, values (xorPeer32 lane mask)) := by
  have he : evalIndex (geometry p) (cohortBase block warp + lane) s (.const (mask : Int)) =
      some (mask : Int) := int32_cast mask (by omega)
  have hc := cohort_coords p block warp lane hw (by omega)
  have hs := xor_source32 lane mask (by omega) hm
  have hpeer := xor_peer_bound active lane mask ha hl hm
  have hmem : (cohortThreads block warp active).contains (cohortBase block warp + xorPeer32 lane mask) = true :=
    List.contains_iff_mem.mpr ((cohort_mem block warp active _).mpr ⟨_, hpeer, rfl⟩)
  unfold Gather.readValue
  rw [he]
  simp only [bind, pure, Option.bind, show ¬ (mask : Int) < 0 by omega, ↓reduceIte, Int.toNat_ofNat]
  change (do
    let selected ← sourceLane .xor 32 (LarkPartitionCollective.nativeLane (geometry p)
      (cohortBase block warp + lane)) mask
    if !((cohortThreads block warp active).contains
      (LarkPartitionCollective.nativeBase (geometry p) (cohortBase block warp + lane) + selected)) then none
    else do
      let v ← s.regs (LarkPartitionCollective.nativeBase (geometry p) (cohortBase block warp + lane) + selected) src
      pure (cohortBase block warp + lane, v)) = _
  rw [hc.2, hc.1, hs]
  simp only [hmem, Bool.not_true, Bool.false_eq_true, ↓reduceIte, hr _ hpeer, bind, pure, Option.bind]

theorem snapshot_mapM (xs : List Nat) (f : Nat → Option α) (v : Nat → α)
    (h : ∀ t ∈ xs, f t = some (v t)) : xs.mapM f = some (xs.map v) := by
  induction xs with
  | nil => rfl
  | cons t ts ih =>
      simp only [List.mapM_cons, h t (by simp), Option.some_bind,
        ih (by intro u hu; exact h u (by simp [hu])), List.map_cons]
      rfl

def xorSnapshot (p : Shape) (block warp active mask : Nat) (values : Nat → α) : List (Nat × α) :=
  (cohortThreads block warp active).map fun t =>
    (t, values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) mask))

theorem cohort_xor_values (p : Shape) (neox : Bool) (block warp active mask pc dest src : Nat)
    (s : State α) (values : Nat → α) (hw : warp < 4) (ha : active = 32 ∨ active = 64) (hm : mask < 32)
    (hp : ∀ lane, lane < active → s.pc (cohortBase block warp + lane) = pc)
    (hr : ∀ lane, lane < active → s.regs (cohortBase block warp + lane) src = some (values lane))
    (code : (program neox)[pc]? = some (.shuffle .xor dest src (.const (mask : Int)) 32)) :
    LarkPartitionCollective.shuffleValues (geometry p) (program neox) (cohortThreads block warp active) s =
      some (dest, xorSnapshot p block warp active mask values) := by
  rw [cohort_values32 p neox block warp active pc mask dest src s hw ha hp code]
  have hmapping := snapshot_mapM (cohortThreads block warp active)
    (Gather.readValue (geometry p) (cohortThreads block warp active) s .xor src (.const (mask : Int)) 32)
    (fun t => (t, values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) mask)))
    (by
      intro t ht
      obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp active t).mp ht
      dsimp only
      rw [(cohort_coords p block warp lane hw (by omega)).2]
      exact cohort_read32 p block warp active mask lane src s values hw ha hm hl hr)
  rw [hmapping]
  rfl

theorem cohort_xor_shuffle (p : Shape) (neox : Bool) (block warp active mask pc dest src : Nat)
    (s : State α) (values : Nat → α) (hw : warp < 4) (ha : active = 32 ∨ active = 64) (hm : mask < 32)
    (hp : ∀ lane, lane < active → s.pc (cohortBase block warp + lane) = pc)
    (hr : ∀ lane, lane < active → s.regs (cohortBase block warp + lane) src = some (values lane))
    (code : (program neox)[pc]? = some (.shuffle .xor dest src (.const (mask : Int)) 32)) :
    LarkPartitionCollective.runShuffle (geometry p) (program neox) (cohortThreads block warp active) s =
      some (shuffleUpdates dest (xorSnapshot p block warp active mask values) s) := by
  unfold LarkPartitionCollective.runShuffle
  rw [cohort_xor_values p neox block warp active mask pc dest src s values hw ha hm hp hr code]
  rfl

#print axioms xor_source32
#print axioms xor_peer_bound
#print axioms xor_peer_partition
#print axioms xor_peer_same_head
#print axioms cohort_uniform
#print axioms cohort_values32
#print axioms cohort_read32
#print axioms snapshot_mapM
#print axioms cohort_xor_values
#print axioms cohort_xor_shuffle
end LarkNativeQKNormRope
