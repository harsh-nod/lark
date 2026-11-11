import Lark.NativeSoftmaxNormWaveFold

/-! Actual complete final normalization block phase. All16 native waves halt,
all50257 converted division outputs are retained, and the repaired trace is
classified Good. No extra barrier, shuffle, arithmetic law or fuel is assumed. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def NormBlockEntry (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop :=
  ∀ tid, tid<1024 → NormLaneEntry p ops input row tid s

def NormOutputRow (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop :=
  ∀ col, col<50257 → s.memory (globalCell 0 (address row col))=some (normOutputValue ops input row col)

def normBlock (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : State α :=
  normWaveFold guarded ops input row (List.range 16) s

theorem norm_wave_entry_of_block (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (entry : NormBlockEntry p ops input row s) :
    NormWaveEntry p ops input row ws s := by
  intro w hw t ht
  exact entry (t%1024) (Nat.mod_lt _ (by decide))

theorem norm_block_fold_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : NormBlockEntry p ops input row s) :
    (List.range (((geometry p).block+(geometry p).warp-1)/(geometry p).warp)).foldlM
      (fun s w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program guarded)
        (warpThreads (geometry p) row w) fuel.warp s) s=some (normBlock guarded ops input row s) := by
  have hn : ((geometry p).block+(geometry p).warp-1)/(geometry p).warp=16 := by
    change (1024+64-1)/64=16
    decide
  rewrite [hn]
  exact norm_wave_fold_run p guarded ops input row (List.range 16) s List.nodup_range
    (fun w hw => List.mem_range.mp hw) (norm_wave_entry_of_block p ops input row _ s entry)

theorem norm_block_pc (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ht : tid<1024) :
    (normBlock guarded ops input row s).pc (row*1024+tid)=normPc guarded 115 := by
  have h := norm_wave_fold_member_pc guarded ops input row (List.range 16) s List.nodup_range
    (fun w hw => List.mem_range.mp hw) (tid/64) (tid%64) (List.mem_range.mpr (by omega)) (Nat.mod_lt _ (by decide))
  have he : cohortBase row (tid/64)+tid%64=row*1024+tid := by unfold cohortBase; omega
  simpa only [he] using h

theorem norm_block_epochs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : (normBlock guarded ops input row s).epochs=s.epochs :=
  norm_wave_fold_epochs guarded ops input row (List.range 16) s

theorem norm_block_outputs (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : NormOutputRow ops input row (normBlock guarded ops input row s) := by
  intro col hc
  obtain ⟨tid,it,c,ht,hi,hcb,_,he⟩ := column_cover col hc
  have hcoord : (row*1024+tid)%1024=tid := by omega
  have hthread : cohortBase row (tid/64)+tid%64=row*1024+tid := by unfold cohortBase; omega
  have h := norm_wave_fold_output_value guarded ops input row (List.range 16) s List.nodup_range
    (fun w hw => List.mem_range.mp hw) (tid/64) (row*1024+tid) it c
    (List.mem_range.mpr (by omega))
    ((cohort_mem row (tid/64) 64 _).mpr ⟨tid%64,Nat.mod_lt _ (by decide),hthread.symm⟩) hi hcb
    (by simpa only [hcoord,he] using hc)
  simpa only [hcoord,he] using h

theorem norm_block_cut (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    LarkCollective.converged (program guarded) (blockThreads (geometry p) row) (normBlock guarded ops input row s)=some .halt := by
  have hs : blockThreads (geometry p) row=cohortThreads row 0 1024 := by simp [blockThreads,geometry,cohortThreads,cohortBase]
  rewrite [hs]
  apply (norm_cohort_halt guarded row 0 1024 _ (by decide) ?_).2
  intro tid ht
  simpa only [cohortBase,Nat.zero_mul,Nat.add_zero] using norm_block_pc guarded ops input row tid s ht

theorem norm_block_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row extra : Nat) (s : State α) (entry : NormBlockEntry p ops input row s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program guarded) row (extra+1) s=
      some (normBlock guarded ops input row s) := by
  rewrite [LarkPartitionCollective.runBlock,norm_block_fold_run p guarded ops input row s entry]
  simp only [bind,pure,Option.some_bind,norm_block_cut p guarded ops input row s,reduceCtorEq,↓reduceIte,or_true]

theorem norm_block_fixed_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : NormBlockEntry p ops input row s) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normBlock true ops input row s).trace, Good a :=
  norm_wave_fold_fixed_good p ops input row (List.range 16) s List.nodup_range (fun w hw => List.mem_range.mp hw)
    (norm_wave_entry_of_block p ops input row _ s entry) good

theorem norm_block_fixed_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (entry : NormBlockEntry p ops input row s) (good : ∀ a ∈ s.trace, Good a) :
    raceFree (geometry p) (normBlock true ops input row s).trace=true :=
  race_free p _ (norm_block_fixed_good p ops input row s entry good)

theorem norm_block_entry_of_sum (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) (ready : SumReady p ops input row s) (outputs : ExpOutputRow ops input row s) :
    NormBlockEntry p ops input row s := by
  intro tid ht
  exact norm_entry_of_sum p ops input row tid s ht ready outputs

#print axioms norm_wave_entry_of_block
#print axioms norm_block_fold_run
#print axioms norm_block_pc
#print axioms norm_block_epochs
#print axioms norm_block_outputs
#print axioms norm_block_cut
#print axioms norm_block_run
#print axioms norm_block_fixed_good
#print axioms norm_block_fixed_race_free
#print axioms norm_block_entry_of_sum
end LarkNativeSoftmax
