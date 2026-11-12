import Lark.NativeQKNormRopeCohort

/-! Native physical ownership and complete wave/block/grid coverage. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def physicalBlock (t : Nat) : Nat := t / 256
def physicalWarp (t : Nat) : Nat := t % 256 / 64
def physicalLane (t : Nat) : Nat := t % 64

theorem physical_warp_bound (t : Nat) : physicalWarp t < 4 := by unfold physicalWarp; omega
theorem physical_lane_bound (t : Nat) : physicalLane t < 64 := Nat.mod_lt _ (by decide)
theorem physical_block_bound (p : Shape) (t : Nat) (ht : t < p.rows * 1280) : physicalBlock t < p.rows * 5 := by
  unfold physicalBlock
  omega

theorem physical_reconstruct (t : Nat) : cohortBase (physicalBlock t) (physicalWarp t) + physicalLane t = t := by
  unfold cohortBase physicalBlock physicalWarp physicalLane
  omega

theorem physical_coords (block warp lane : Nat) (hw : warp < 4) (hl : lane < 64) :
    physicalBlock (cohortBase block warp + lane) = block ∧
    physicalWarp (cohortBase block warp + lane) = warp ∧
    physicalLane (cohortBase block warp + lane) = lane := by
  unfold cohortBase physicalBlock physicalWarp physicalLane
  omega

theorem cohort_owner (block warp t : Nat) (hw : warp < 4) :
    t ∈ cohortThreads block warp 64 ↔ physicalBlock t = block ∧ physicalWarp t = warp := by
  constructor
  · intro ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    exact ⟨(physical_coords block warp lane hw hl).1, (physical_coords block warp lane hw hl).2.1⟩
  · intro ht
    apply (cohort_mem block warp 64 t).mpr
    exact ⟨physicalLane t, physical_lane_bound t, by simpa only [ht.1, ht.2] using (physical_reconstruct t).symm⟩

theorem cohort_foreign_warp (block warp other t : Nat) (hw : warp < 4) (ho : other < 4)
    (hne : other ≠ warp) (ht : t ∈ cohortThreads block other 64) : t ∉ cohortThreads block warp 64 := by
  intro hm
  have a := (cohort_owner block other t ho).mp ht
  have b := (cohort_owner block warp t hw).mp hm
  exact hne (a.2.symm.trans b.2)

theorem cohort_foreign_block (block warp t : Nat) (hw : warp < 4)
    (hne : physicalBlock t ≠ block) : t ∉ cohortThreads block warp 64 := by
  intro ht
  exact hne ((cohort_owner block warp t hw).mp ht).1

theorem native_block_mem (p : Shape) (block t : Nat) :
    t ∈ blockThreads (geometry p) block ↔ physicalBlock t = block := by
  constructor
  · intro ht
    obtain ⟨tid, htid, he⟩ := List.mem_map.mp ht
    have htid : tid < 256 := List.mem_range.mp htid
    change block * 256 + tid = t at he
    unfold physicalBlock
    omega
  · intro ht
    apply List.mem_map.mpr
    refine ⟨t % 256, List.mem_range.mpr (Nat.mod_lt t (by decide)), ?_⟩
    change block * 256 + t % 256 = t
    unfold physicalBlock at ht
    omega

theorem native_block_cohort (p : Shape) (block : Nat) :
    blockThreads (geometry p) block = cohortThreads block 0 256 := by
  simp [blockThreads, geometry, cohortThreads, cohortBase]

theorem native_block_coverage (p : Shape) (block t : Nat) (ht : t ∈ blockThreads (geometry p) block) :
    ∃ warp < 4, t ∈ cohortThreads block warp 64 := by
  refine ⟨physicalWarp t, physical_warp_bound t, ?_⟩
  exact (cohort_owner block (physicalWarp t) t (physical_warp_bound t)).mpr ⟨(native_block_mem p block t).mp ht, rfl⟩

theorem cohort_in_native_block (p : Shape) (block warp t : Nat) (hw : warp < 4)
    (ht : t ∈ cohortThreads block warp 64) : t ∈ blockThreads (geometry p) block :=
  (native_block_mem p block t).mpr ((cohort_owner block warp t hw).mp ht).1

#print axioms physical_warp_bound
#print axioms physical_lane_bound
#print axioms physical_block_bound
#print axioms physical_reconstruct
#print axioms physical_coords
#print axioms cohort_owner
#print axioms cohort_foreign_warp
#print axioms cohort_foreign_block
#print axioms native_block_mem
#print axioms native_block_cohort
#print axioms native_block_coverage
#print axioms cohort_in_native_block
end LarkNativeQKNormRope
