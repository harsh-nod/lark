import Lark.NativeSglangRmsNormXorState

/-! Logical32 XOR snapshots with explicit source/destination register IDs.
The second source reduction uses register7/register8 rather than 0/1.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cohort_reg_values32 (p : Shape) (repaired : Bool) (row warp active pc mask dest src : Nat)
    (s : State α) (hw : warp<16) (ha : active=32 ∨ active=64)
    (hp : ∀ lane,lane<active → s.pc (cohortBase row warp+lane)=pc)
    (code : (program repaired)[pc]?=some (.shuffle .xor dest src (.const (mask : Int)) 32)) :
    LarkPartitionCollective.shuffleValues (geometry p) (program repaired) (cohortThreads row warp active) s=
      ((cohortThreads row warp active).mapM (Gather.readValue (geometry p)
        (cohortThreads row warp active) s .xor src (.const (mask : Int)) 32)).bind (fun vs => some (dest,vs)) := by
  have hpos : 0<active := by omega
  have hb : active≤64 := by omega
  have hn : cohortThreads row warp active≠[] := by
    have hm := (cohort_mem row warp active (cohortBase row warp)).mpr ⟨0,hpos,by omega⟩
    intro he; simp [he] at hm
  have hguard : ¬((geometry p).warp≠64 ∨ (geometry p).block%64≠0 ∨
      cohortThreads row warp active=[] ∨ ¬(cohortThreads row warp active).Nodup ∨
      64<(cohortThreads row warp active).length) := by
    have hlen : (cohortThreads row warp active).length=active := by simp [cohortThreads]
    simp only [geometry,ne_eq,Nat.reduceMod,not_true_eq_false,hlen,hn,cohort_nodup,
      Nat.not_lt.mpr hb,or_self,not_false_eq_true]
  unfold LarkPartitionCollective.shuffleValues
  rw [if_neg hguard,cohort_head row warp active hpos]
  simp only [bind,pure,Option.bind]
  rw [cohort_uniform p row warp active pc s hw hb hpos hp]
  simp only [Bool.not_true,Bool.false_eq_true,↓reduceIte]
  have hp0 : s.pc (cohortBase row warp)=pc := by simpa only [Nat.add_zero] using hp 0 hpos
  rw [hp0,code]
  simp only [Option.bind,show [1,2,4,8,16,32,64].contains 32=true by decide,
    cohort_complete32 p row warp active hw ha,Bool.not_true,Bool.false_eq_true,or_self,↓reduceIte]

theorem cohort_reg_read32 (p : Shape) (row warp active mask lane src : Nat) (s : State α)
    (values : Nat → α) (hw : warp<16) (ha : active=32 ∨ active=64) (hm : mask<32) (hl : lane<active)
    (hr : ∀ l,l<active → s.regs (cohortBase row warp+l) src=some (values l)) :
    Gather.readValue (geometry p) (cohortThreads row warp active) s .xor src
      (.const (mask : Int)) 32 (cohortBase row warp+lane)=
      some (cohortBase row warp+lane,values (xorPeer32 lane mask)) := by
  have he : evalIndex (geometry p) (cohortBase row warp+lane) s (.const (mask : Int))=some (mask : Int) :=
    LarkReduction.int32_cast mask (by omega)
  have hc := cohort_coords p row warp lane hw (by omega)
  have hsource := xor_source32 lane mask (by omega) hm
  have hpeer := xor_peer_bound active lane mask ha hl hm
  have hmem : (cohortThreads row warp active).contains (cohortBase row warp+xorPeer32 lane mask)=true :=
    List.contains_iff_mem.mpr ((cohort_mem row warp active _).mpr ⟨_,hpeer,rfl⟩)
  unfold Gather.readValue
  rw [he]
  simp only [bind,pure,Option.bind,show ¬(mask : Int)<0 by omega,↓reduceIte,Int.toNat_ofNat]
  change (do
    let selected ← sourceLane .xor 32 (LarkPartitionCollective.nativeLane (geometry p) (cohortBase row warp+lane)) mask
    if !((cohortThreads row warp active).contains
      (LarkPartitionCollective.nativeBase (geometry p) (cohortBase row warp+lane)+selected)) then none
    else do
      let v ← s.regs (LarkPartitionCollective.nativeBase (geometry p) (cohortBase row warp+lane)+selected) src
      pure (cohortBase row warp+lane,v))=_
  rw [hc.2,hc.1,hsource]
  simp only [hmem,Bool.not_true,Bool.false_eq_true,↓reduceIte,hr _ hpeer,bind,pure,Option.bind]

theorem cohort_reg_xor_values (p : Shape) (repaired : Bool) (row warp active mask pc dest src : Nat)
    (s : State α) (values : Nat → α) (hw : warp<16) (ha : active=32 ∨ active=64) (hm : mask<32)
    (hp : ∀ lane,lane<active → s.pc (cohortBase row warp+lane)=pc)
    (hr : ∀ lane,lane<active → s.regs (cohortBase row warp+lane) src=some (values lane))
    (code : (program repaired)[pc]?=some (.shuffle .xor dest src (.const (mask : Int)) 32)) :
    LarkPartitionCollective.shuffleValues (geometry p) (program repaired) (cohortThreads row warp active) s=
      some (dest,xorSnapshot p row warp active mask values) := by
  rw [cohort_reg_values32 p repaired row warp active pc mask dest src s hw ha hp code]
  have hmapping := snapshot_mapM (cohortThreads row warp active)
    (Gather.readValue (geometry p) (cohortThreads row warp active) s .xor src (.const (mask : Int)) 32)
    (fun t => (t,values (xorPeer32 (LarkPartitionCollective.nativeLane (geometry p) t) mask))) (by
      intro t ht
      obtain ⟨lane,hl,rfl⟩ := (cohort_mem row warp active t).mp ht
      dsimp only
      rw [(cohort_coords p row warp lane hw (by omega)).2]
      exact cohort_reg_read32 p row warp active mask lane src s values hw ha hm hl hr)
  rw [hmapping]
  rfl

theorem cohort_reg_xor_shuffle (p : Shape) (repaired : Bool) (row warp active mask pc dest src : Nat)
    (s : State α) (values : Nat → α) (hw : warp<16) (ha : active=32 ∨ active=64) (hm : mask<32)
    (hp : ∀ lane,lane<active → s.pc (cohortBase row warp+lane)=pc)
    (hr : ∀ lane,lane<active → s.regs (cohortBase row warp+lane) src=some (values lane))
    (code : (program repaired)[pc]?=some (.shuffle .xor dest src (.const (mask : Int)) 32)) :
    LarkPartitionCollective.runShuffle (geometry p) (program repaired) (cohortThreads row warp active) s=
      some (shuffleUpdates dest (xorSnapshot p row warp active mask values) s) := by
  unfold LarkPartitionCollective.runShuffle
  rw [cohort_reg_xor_values p repaired row warp active mask pc dest src s values hw ha hm hp hr code]
  rfl

theorem reg_xor_shuffled_fields (p : Shape) (row warp active mask lane dest src : Nat)
    (values : Nat → α) (s : State α) (hw : warp<16) (ha : active≤64) (hl : lane<active) (hsd : src≠dest) :
    let next := shuffleUpdates dest (xorSnapshot p row warp active mask values) s
    let t := cohortBase row warp+lane
    next.pc t=s.pc t+1 ∧ next.regs t src=s.regs t src ∧ next.regs t dest=some (values (xorPeer32 lane mask)) := by
  have ht := (cohort_mem row warp active _).mpr ⟨lane,hl,rfl⟩
  dsimp only
  constructor
  · simp only [shuffleUpdates,xorSnapshot,snapshot_any,ht,decide_true,↓reduceIte]
  constructor
  · simp only [shuffleUpdates,if_neg hsd]
  · simp only [shuffleUpdates,↓reduceIte,xorSnapshot]
    rw [snapshot_lookup _ _ _ ht,(cohort_coords p row warp lane hw (by omega)).2]

theorem reg_xor_shuffled_other (p : Shape) (row warp active mask dest t : Nat)
    (values : Nat → α) (s : State α) (ht : t∉cohortThreads row warp active) :
    let next := shuffleUpdates dest (xorSnapshot p row warp active mask values) s
    next.pc t=s.pc t ∧ next.regs t=s.regs t := by
  dsimp only
  constructor
  · simp only [shuffleUpdates,xorSnapshot,snapshot_any,ht,decide_false,Bool.false_eq_true,↓reduceIte]
  · funext r
    simp only [shuffleUpdates,xorSnapshot]
    split
    · rw [snapshot_lookup_other _ _ _ ht]
    · rfl

theorem reg_xor_shuffled_preserves (p : Shape) (row warp active mask dest : Nat)
    (values : Nat → α) (s : State α) :
    let next := shuffleUpdates dest (xorSnapshot p row warp active mask values) s
    next.memory=s.memory ∧ next.indices=s.indices ∧ next.epochs=s.epochs ∧ next.trace=s.trace := ⟨rfl,rfl,rfl,rfl⟩

#print axioms cohort_reg_values32
#print axioms cohort_reg_read32
#print axioms cohort_reg_xor_values
#print axioms cohort_reg_xor_shuffle
#print axioms reg_xor_shuffled_fields
#print axioms reg_xor_shuffled_other
#print axioms reg_xor_shuffled_preserves
end LarkNativeSglangRmsNorm
