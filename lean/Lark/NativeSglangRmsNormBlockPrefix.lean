import Lark.NativeSglangRmsNormPartialValue

/-! Complete first-phase native block execution: sixteen physical waves
converge at the first barrier. The native block runner then resumes it once.
The second reduction and whole-kernel completion remain explicit continuations.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold

theorem distinct_cohorts (row w v t : Nat) (hne : w≠v)
    (ht : t∈cohortThreads row w 64) : t∉cohortThreads row v 64 := by
  intro hv
  obtain ⟨a,ha,he⟩ := (cohort_mem row w 64 t).mp ht
  obtain ⟨b,hb,hf⟩ := (cohort_mem row v 64 t).mp hv
  unfold cohortBase at he hf
  omega

def firstBlockFold (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) : State α :=
  ws.foldl (fun s w => wavePartial p repaired ops input row w s) s

theorem first_block_fold_cons (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row w : Nat) (ws : List Nat) (s : State α) :
    firstBlockFold p repaired ops input row (w::ws) s=
      firstBlockFold p repaired ops input row ws (wavePartial p repaired ops input row w s) := rfl

theorem first_block_fold_reads (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (firstBlockFold p repaired ops input row ws s) := by
  induction ws generalizing s with
  | nil => exact reads
  | cons w ws ih => exact ih _ (wave_partial_reads p repaired ops input row w s reads)

theorem first_block_fold_epochs (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) :
    (firstBlockFold p repaired ops input row ws s).epochs=s.epochs := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      exact (ih (wavePartial p repaired ops input row w s)).trans
        (wave_partial_indices_epochs p repaired ops input row w s).2

theorem first_block_fold_other (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (t : Nat) (s : State α)
    (outside : ∀ w∈ws,t∉cohortThreads row w 64) :
    (firstBlockFold p repaired ops input row ws s).pc t=s.pc t ∧
    (firstBlockFold p repaired ops input row ws s).indices t=s.indices t ∧
    (firstBlockFold p repaired ops input row ws s).regs t=s.regs t := by
  induction ws generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons w ws ih =>
      have h := ih (wavePartial p repaired ops input row w s) (fun v hv => outside v (by simp [hv]))
      have hw := wave_partial_other p repaired ops input row w t s (outside w (by simp))
      exact ⟨h.1.trans hw.1,h.2.1.trans hw.2.1,h.2.2.trans hw.2.2⟩

theorem first_block_fold_member_pc (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (bounds : ∀ w∈ws,w<16)
    (w lane : Nat) (hw : w∈ws) (hl : lane<64) :
    (firstBlockFold p repaired ops input row ws s).pc (cohortBase row w+lane)=firstBarrier repaired := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons v ws ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp hw with he | hm
      · subst w
        have outside : ∀ u∈ws,cohortBase row v+lane∉cohortThreads row u 64 := by
          intro u hu
          apply distinct_cohorts row v u _ _ ((cohort_mem row v 64 _).mpr ⟨lane,hl,rfl⟩)
          intro he; subst u; exact hnot hu
        have h := first_block_fold_other p repaired ops input row ws _ (wavePartial p repaired ops input row v s) outside
        exact h.1.trans (wave_partial_fields p repaired ops input row v lane s (bounds v (by simp)) hl).1
      · exact ih (wavePartial p repaired ops input row v s) hnodup
          (fun u hu => bounds u (by simp [hu])) hm

theorem first_block_waves_run (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hr : row<p.rows)
    (hn : ws.Nodup) (bounds : ∀ w∈ws,w<16)
    (hp : ∀ w∈ws,∀ t∈cohortThreads row w 64,s.pc t=0) (reads : Reads p input s) :
    ws.foldlM (fun u w => LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (warpThreads (geometry p) row w) fuel.warp u) s = some (firstBlockFold p repaired ops input row ws s) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rw [List.foldlM_cons,native_wave_partial p repaired ops input row w s hr (bounds w (by simp))
        (hp w (by simp)) reads]
      apply ih (wavePartial p repaired ops input row w s) hnodup
      · intro v hv; exact bounds v (by simp [hv])
      · intro v hv t ht
        have hne : v≠w := by intro he; subst v; exact hnot hv
        exact (wave_partial_other p repaired ops input row w t s (distinct_cohorts row v w t hne ht)).1.trans
          (hp v (by simp [hv]) t ht)
      · exact wave_partial_reads p repaired ops input row w s reads

theorem cohort_in_block (p : Shape) (row w t : Nat) (hw : w<16) (ht : t∈cohortThreads row w 64) :
    t∈blockThreads (geometry p) row := by
  obtain ⟨lane,hl,rfl⟩ := (cohort_mem row w 64 t).mp ht
  apply List.mem_map.mpr
  refine ⟨w*64+lane,List.mem_range.mpr (by change w*64+lane<1024; omega),?_⟩
  change row*1024+(w*64+lane)=cohortBase row w+lane
  unfold cohortBase
  omega

theorem first_block_all_pc (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) :
    ∀ t∈blockThreads (geometry p) row,
      (firstBlockFold p repaired ops input row (List.range 16) s).pc t=firstBarrier repaired := by
  intro t ht
  obtain ⟨tid,htid,rfl⟩ := List.mem_map.mp ht
  have htid : tid<1024 := List.mem_range.mp htid
  have he : row*1024+tid=cohortBase row (tid/64)+tid%64 := by unfold cohortBase; omega
  change (firstBlockFold p repaired ops input row (List.range 16) s).pc (row*1024+tid)=_
  rw [he]
  exact first_block_fold_member_pc p repaired ops input row (List.range 16) s List.nodup_range
    (fun w hw => List.mem_range.mp hw) (tid/64) (tid%64) (List.mem_range.mpr (by omega)) (by omega)

theorem native_first_block_step (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row n : Nat) (s : State α) (hr : row<p.rows)
    (hp : ∀ t∈blockThreads (geometry p) row,s.pc t=0) (reads : Reads p input s) :
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program repaired) row (n+1) s =
    LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program repaired) row n
      (resume (blockThreads (geometry p) row) .block (firstBlockFold p repaired ops input row (List.range 16) s)) := by
  have hrun := first_block_waves_run p repaired ops input row (List.range 16) s hr List.nodup_range
    (fun w hw => List.mem_range.mp hw)
    (fun w hw t ht => hp t (cohort_in_block p row w t (List.mem_range.mp hw) ht)) reads
  have hn : blockThreads (geometry p) row≠[] := by
    intro he
    have hm : row*1024∈blockThreads (geometry p) row := by
      apply List.mem_map.mpr
      exact ⟨0,List.mem_range.mpr (by change 0<1024; decide),by simp [geometry]⟩
    rw [he] at hm
    cases hm
  have hc := barrier_converged repaired (blockThreads (geometry p) row)
    (firstBlockFold p repaired ops input row (List.range 16) s) hn (first_block_all_pc p repaired ops input row s)
  have count : ((geometry p).block+(geometry p).warp-1)/(geometry p).warp=16 := by
    change (1024+64-1)/64=16
    decide
  rw [LarkPartitionCollective.runBlock]
  rw [count,hrun]
  simp only [bind,Option.some_bind]
  rw [hc]
  rfl

#print axioms distinct_cohorts
#print axioms first_block_fold_cons
#print axioms first_block_fold_reads
#print axioms first_block_fold_epochs
#print axioms first_block_fold_other
#print axioms first_block_fold_member_pc
#print axioms first_block_waves_run
#print axioms cohort_in_block
#print axioms first_block_all_pc
#print axioms native_first_block_step
end LarkNativeSglangRmsNorm
