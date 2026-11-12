import Lark.NativeSglangRmsNormBlockPrefix

/-! Private caches and guarded shared partials survive every other physical
wave in the block. The resumed first barrier exposes all thirty-two partials
to the following source reduction; no arithmetic reassociation is assumed.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold

structure FixedWaveData (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w : Nat) (s : State α) : Prop where
  pc : ∀ lane, lane<64 → s.pc (cohortBase row w+lane)=56
  indices : ∀ lane, lane<64 → NativeIndices (cohortBase row w+lane) s
  inputs : ∀ lane, lane<64 → InputPrefix input row (w*64+lane) 16 (cohortBase row w+lane) s
  weights : ∀ lane, lane<64 → WeightPrefix input (w*64+lane) 16 (cohortBase row w+lane) s
  accumulator : ∀ lane, lane<64 → s.regs (cohortBase row w+lane) 0=
    some (reductionValues ops (waveBaseValues ops input row w) 5 lane)
  shared : ∀ lane, lane<64 → lane%32=0 → s.memory ⟨.shared,row,0,w*2+lane/32⟩=
    some (reductionValues ops (waveBaseValues ops input row w) 5 lane)

theorem wave_other_private_memory (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row v t buffer offset : Nat) (s : State α)
    (outside : t∉cohortThreads row v 64) :
    (wavePartial p repaired ops input row v s).memory (privateCell t buffer offset)=s.memory (privateCell t buffer offset) := by
  apply wave_partial_memory
  · intro u hu
    have hne : t≠u := by intro he; subst u; exact outside hu
    exact Or.inr (Or.inl hne)
  · intro u _ he
    have hs := congrArg Location.space he
    cases hs

theorem wave_other_shared_memory (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row w v lane : Nat) (s : State α)
    (hv : v<16) (hl : lane<64) (hne : w≠v) :
    (wavePartial p repaired ops input row v s).memory ⟨.shared,row,0,w*2+lane/32⟩=
      s.memory ⟨.shared,row,0,w*2+lane/32⟩ := by
  apply wave_partial_memory
  · intro u _
    exact Or.inl (by simp)
  · intro u hu he
    obtain ⟨other,ho,rfl⟩ := (cohort_mem row v 64 u).mp hu
    have hc := cohort_arithmetic row v other hv ho
    have hs := congrArg Location.offset he
    change w*2+lane/32=((cohortBase row v+other)%1024)/32 at hs
    omega

theorem fixed_wave_data (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w : Nat) (s : State α) (hw : w<16) (reads : Reads p input s) :
    FixedWaveData p ops input row w (wavePartial p true ops input row w s) := by
  constructor
  · intro lane hl; exact (wave_partial_fields p true ops input row w lane s hw hl).1
  · intro lane hl; exact wave_partial_native_indices p true ops input row w lane s hl reads
  · intro lane hl; exact (wave_partial_caches p true ops input row w lane s hw hl reads).1
  · intro lane hl; exact (wave_partial_caches p true ops input row w lane s hw hl reads).2
  · intro lane hl; exact (wave_partial_fields p true ops input row w lane s hw hl).2
  · intro lane hl leader; exact fixed_wave_partial_shared_value p ops input row w lane s hw hl leader

theorem fixed_wave_data_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w v : Nat) (s : State α) (hv : v<16) (hne : w≠v) (ready : FixedWaveData p ops input row w s) :
    FixedWaveData p ops input row w (wavePartial p true ops input row v s) := by
  have outside : ∀ lane, lane<64 → cohortBase row w+lane∉cohortThreads row v 64 := by
    intro lane hl
    exact distinct_cohorts row w v _ hne ((cohort_mem row w 64 _).mpr ⟨lane,hl,rfl⟩)
  constructor
  · intro lane hl
    exact (wave_partial_other p true ops input row v _ s (outside lane hl)).1.trans (ready.pc lane hl)
  · intro lane hl
    unfold NativeIndices
    rw [(wave_partial_other p true ops input row v _ s (outside lane hl)).2.1]
    exact ready.indices lane hl
  · intro lane hl k hk
    rw [wave_other_private_memory p true ops input row v _ 0 k s (outside lane hl)]
    exact ready.inputs lane hl k hk
  · intro lane hl k hk
    rw [wave_other_private_memory p true ops input row v _ 1 k s (outside lane hl)]
    exact ready.weights lane hl k hk
  · intro lane hl
    exact (congrFun (wave_partial_other p true ops input row v _ s (outside lane hl)).2.2 0).trans
      (ready.accumulator lane hl)
  · intro lane hl leader
    rw [wave_other_shared_memory p true ops input row w v lane s hv hl hne]
    exact ready.shared lane hl leader

theorem first_block_fold_frames_data (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w : Nat) (ws : List Nat) (s : State α)
    (bounds : ∀ v∈ws,v<16) (outside : w∉ws) (ready : FixedWaveData p ops input row w s) :
    FixedWaveData p ops input row w (firstBlockFold p true ops input row ws s) := by
  induction ws generalizing s with
  | nil => simpa only [firstBlockFold,List.foldl_nil] using ready
  | cons v ws ih =>
      rw [first_block_fold_cons]
      apply ih (wavePartial p true ops input row v s)
      · intro u hu; exact bounds u (by simp [hu])
      · intro hm; exact outside (by simp [hm])
      · apply fixed_wave_data_other p ops input row w v s (bounds v (by simp)) _ ready
        intro he; subst v; exact outside (by simp)

theorem first_block_fold_member_data (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup)
    (bounds : ∀ v∈ws,v<16) (reads : Reads p input s) (w : Nat) (hw : w∈ws) :
    FixedWaveData p ops input row w (firstBlockFold p true ops input row ws s) := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons v ws ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rw [first_block_fold_cons]
      rcases List.mem_cons.mp hw with he | hm
      · subst w
        exact first_block_fold_frames_data p ops input row v ws _
          (fun u hu => bounds u (by simp [hu])) hnot (fixed_wave_data p ops input row v s (bounds v (by simp)) reads)
      · exact ih (wavePartial p true ops input row v s) hnodup
          (fun u hu => bounds u (by simp [hu])) (wave_partial_reads p true ops input row v s reads) hm

def blockPartialValue (ops : Ops α) (input : Nat → Nat → α) (row logicalWarp : Nat) : α :=
  reductionValues ops (waveBaseValues ops input row (logicalWarp/2)) 5 ((logicalWarp%2)*32)

theorem first_block_shared_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (reads : Reads p input s) (logicalWarp : Nat) (hw : logicalWarp<32) :
    (firstBlockFold p true ops input row (List.range 16) s).memory ⟨.shared,row,0,logicalWarp⟩=
      some (blockPartialValue ops input row logicalWarp) := by
  have ready := first_block_fold_member_data p ops input row (List.range 16) s List.nodup_range
    (fun v hv => List.mem_range.mp hv) reads (logicalWarp/2) (List.mem_range.mpr (by omega))
  have h := ready.shared ((logicalWarp%2)*32) (by omega) (by omega)
  have he : logicalWarp/2*2+((logicalWarp%2)*32)/32=logicalWarp := by omega
  simpa only [he,blockPartialValue] using h

def resumedFirstBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) row) .block (firstBlockFold p true ops input row (List.range 16) s)

theorem initial_first_block_step (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row fuel.block (initial p input outside)=
      LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row 2
        (resumedFirstBlock p ops input row (initial p input outside)) :=
  native_first_block_step p true ops input row 2 _ hr (by intro t ht; rfl) (initial_reads p input outside)

theorem resumed_first_block_shared_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (reads : Reads p input s) (logicalWarp : Nat) (hw : logicalWarp<32) :
    (resumedFirstBlock p ops input row s).memory ⟨.shared,row,0,logicalWarp⟩=
      some (blockPartialValue ops input row logicalWarp) := first_block_shared_values p ops input row s reads logicalWarp hw

theorem resumed_first_block_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t∈blockThreads (geometry p) row) :
    (resumedFirstBlock p ops input row s).pc t=57 := by
  have hc := List.contains_iff_mem.mpr ht
  simp only [resumedFirstBlock,resume,hc,↓reduceIte,first_block_all_pc p true ops input row s t ht,firstBarrier]

theorem resumed_first_block_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (ht : t∈blockThreads (geometry p) row) :
    ((resumedFirstBlock p ops input row s).epochs t).block=(s.epochs t).block+1 ∧
    ((resumedFirstBlock p ops input row s).epochs t).warp=(s.epochs t).warp ∧
    ((resumedFirstBlock p ops input row s).epochs t).grid=(s.epochs t).grid := by
  have hc := List.contains_iff_mem.mpr ht
  simp only [resumedFirstBlock,resume,hc,↓reduceIte,first_block_fold_epochs,bumpEpoch,and_self]

theorem resumed_first_block_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (resumedFirstBlock p ops input row s) :=
  first_block_fold_reads p true ops input row (List.range 16) s reads

theorem resumed_first_block_indices (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (s : State α) (reads : Reads p input s) (ht : t∈blockThreads (geometry p) row) :
    NativeIndices t (resumedFirstBlock p ops input row s) := by
  obtain ⟨tid,htid,rfl⟩ := List.mem_map.mp ht
  have htid : tid<1024 := List.mem_range.mp htid
  have he : row*1024+tid=cohortBase row (tid/64)+tid%64 := by unfold cohortBase; omega
  change NativeIndices (row*1024+tid) (resumedFirstBlock p ops input row s)
  rw [he]
  have ready := first_block_fold_member_data p ops input row (List.range 16) s List.nodup_range
    (fun w hw => List.mem_range.mp hw) reads (tid/64) (List.mem_range.mpr (by omega))
  exact ready.indices (tid%64) (by omega)

theorem resumed_first_block_caches (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w lane : Nat) (s : State α) (reads : Reads p input s) (hw : w<16) (hl : lane<64) :
    InputPrefix input row (w*64+lane) 16 (cohortBase row w+lane) (resumedFirstBlock p ops input row s) ∧
    WeightPrefix input (w*64+lane) 16 (cohortBase row w+lane) (resumedFirstBlock p ops input row s) := by
  have ready := first_block_fold_member_data p ops input row (List.range 16) s List.nodup_range
    (fun v hv => List.mem_range.mp hv) reads w (List.mem_range.mpr hw)
  exact ⟨ready.inputs lane hl,ready.weights lane hl⟩

#print axioms wave_other_private_memory
#print axioms wave_other_shared_memory
#print axioms fixed_wave_data
#print axioms fixed_wave_data_other
#print axioms first_block_fold_frames_data
#print axioms first_block_fold_member_data
#print axioms first_block_shared_values
#print axioms initial_first_block_step
#print axioms resumed_first_block_shared_values
#print axioms resumed_first_block_pc
#print axioms resumed_first_block_epochs
#print axioms resumed_first_block_reads
#print axioms resumed_first_block_indices
#print axioms resumed_first_block_caches
end LarkNativeSglangRmsNorm
