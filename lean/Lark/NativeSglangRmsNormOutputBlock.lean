import Lark.NativeSglangRmsNormOutputWaves

/-! Actual final native block iteration: every physical output wave runs to
halt and every thread's16 global outputs survive. Values retain the source's
lane-specific inverse under arbitrary scalar operations.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot skipFold inactiveWaves scalePairs scaleRounds outputCopies outputFold

theorem block_cohort (p : Shape) (row : Nat) : blockThreads (geometry p) row=cohortThreads row 0 1024 := by
  simp [blockThreads,geometry,cohortThreads,cohortBase]

theorem block_nodup (p : Shape) (row : Nat) : (blockThreads (geometry p) row).Nodup := by
  rw [block_cohort]
  exact cohort_nodup row 0 1024

theorem block_member (p : Shape) (row t : Nat) :
    t∈blockThreads (geometry p) row ↔ ∃ tid,tid<1024 ∧ t=row*1024+tid := by
  simp only [blockThreads,geometry,List.mem_map,List.mem_range]
  constructor
  · rintro ⟨tid,ht,he⟩; exact ⟨tid,ht,he.symm⟩
  · rintro ⟨tid,ht,he⟩; exact ⟨tid,ht,he.symm⟩

def outputBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  outputFold ops input (blockThreads (geometry p) row) s

theorem output_block_all_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) :
    ∀ t∈blockThreads (geometry p) row,(outputBlock p ops input row s).pc t=109 :=
  fun t ht => output_fold_member_pc ops input (blockThreads (geometry p) row) s (block_nodup p row) t ht

theorem output_block_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (hr : row<p.rows)
    (ready : ∀ t∈blockThreads (geometry p) row,OutputReady ops input t s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row 1 s=
      some (outputBlock p ops input row s) := by
  have hrun : (List.range 16).foldlM
      (fun u w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
        (warpThreads (geometry p) row w) fuel.warp u) s=some (outputBlock p ops input row s) := by
    rw [output_waves_run p ops input row (List.range 16) s hr List.nodup_range (fun w hw => List.mem_range.mp hw)
      (by rwa [all_output_threads]),output_waves_eq_fold,all_output_threads]
    rfl
  have hn : blockThreads (geometry p) row≠[] := by
    intro he
    have hm := (block_member p row (row*1024)).mpr ⟨0,by decide,by omega⟩
    rw [he] at hm
    cases hm
  have hc := halt_converged (blockThreads (geometry p) row) (outputBlock p ops input row s) hn
    (output_block_all_pc p ops input row s)
  have count : ((geometry p).block+(geometry p).warp-1)/(geometry p).warp=16 := by
    change (1024+64-1)/64=16
    decide
  rw [LarkPartitionCollective.runBlock,count,hrun]
  simp only [bind,Option.some_bind]
  rw [hc]
  rfl

theorem reached_output_block_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (reads : Reads p input s) :
    ∀ t∈blockThreads (geometry p) row,OutputReady ops input t
      (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)) := by
  intro t ht
  obtain ⟨tid,htid,rfl⟩ := (block_member p row t).mp ht
  have he : row*1024+tid=cohortBase row (tid/64)+tid%64 := by unfold cohortBase; omega
  rw [he]
  exact resumed_output_ready p ops input row (tid/64) (tid%64) s reads (by omega) (by omega)

theorem output_block_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (ht : tid<1024) (hi : iteration<2) (hc : component<8)
    (ready : ∀ t∈blockThreads (geometry p) row,OutputReady ops input t s) :
    (outputBlock p ops input row s).memory (globalCell 0 (address row (column tid iteration component)))=
      some (outputScaled ops input row tid iteration component (blockInverseValue ops input row (tid/32))) := by
  let t := row*1024+tid
  have hmem : t∈blockThreads (geometry p) row := (block_member p row t).mpr ⟨tid,ht,rfl⟩
  have r := output_fold_values ops input (blockThreads (geometry p) row) s (block_nodup p row) ready t hmem
  have hrow : t/1024=row := by dsimp only [t]; omega
  have htid : t%1024=tid := by dsimp only [t]; omega
  have value := r (iteration*8+component) (by omega)
  have hd : (iteration*8+component)/8=iteration := by omega
  have hm : (iteration*8+component)%8=component := by omega
  simpa only [hrow,htid,laneInverse,flat_address_rank row tid iteration component hc,hd,hm] using value

theorem output_block_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : (outputBlock p ops input row s).epochs=s.epochs :=
  output_fold_epochs ops input (blockThreads (geometry p) row) s

theorem output_block_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : (outputBlock p ops input row s).trace.length=s.trace.length+82944 := by
  simpa only [blockThreads,geometry,List.length_map,List.length_range] using
    output_fold_trace_length ops input (blockThreads (geometry p) row) s

theorem output_block_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (epochs : ∀ t∈blockThreads (geometry p) row,(s.epochs t).block=2)
    (good : ∀ event∈s.trace,Good event) : ∀ event∈(outputBlock p ops input row s).trace,Good event :=
  output_fold_good ops input (blockThreads (geometry p) row) s epochs good

#print axioms block_cohort
#print axioms block_nodup
#print axioms block_member
#print axioms output_block_all_pc
#print axioms output_block_run
#print axioms reached_output_block_ready
#print axioms output_block_value
#print axioms output_block_epochs
#print axioms output_block_trace_length
#print axioms output_block_good
end LarkNativeSglangRmsNorm
