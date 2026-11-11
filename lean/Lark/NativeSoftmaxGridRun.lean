import Lark.NativeSoftmaxGridFold

/-! Actual repaired whole-grid execution under the original launch interface
and fuel. Every supported row halts with its converted normalization outputs,
the input is preserved, and the complete accumulated trace is race-free.
Canonical-real/IEEE reference equivalence is not assumed by this execution. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def fixedGrid (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) : State α :=
  fixedBlockFold p ops input (List.range p.rows) s

def fixedInitialGrid (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  fixedGrid p ops input (initial (layout p) input outside)

theorem initial_grid_rows_entry (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α) :
    GridRowsEntry p input (List.range p.rows) (initial (layout p) input outside) := by
  intro row hr
  exact initial_block_entry p input outside row (List.mem_range.mp hr)

theorem fixed_grid_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (entry : GridRowsEntry p input (List.range p.rows) s) :
    (List.range (geometry p).grid).foldlM
      (fun s row => LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row fuel.block s) s=
      some (fixedGrid p ops input s) :=
  fixed_block_fold_run p ops input (List.range p.rows) s List.nodup_range entry

theorem fixed_grid_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (hr : row<p.rows) (ht : tid<1024) :
    (fixedGrid p ops input s).pc (row*1024+tid)=normPc true 115 :=
  fixed_block_fold_member_pc p ops input (List.range p.rows) s List.nodup_range row tid (List.mem_range.mpr hr) ht

theorem fixed_grid_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (entry : GridRowsEntry p input (List.range p.rows) s) (hr : row<p.rows) (ht : tid<1024) :
    ((fixedGrid p ops input s).epochs (row*1024+tid)).block=4 :=
  fixed_block_fold_member_epoch p ops input (List.range p.rows) s List.nodup_range entry row tid (List.mem_range.mpr hr) ht

theorem fixed_grid_outputs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row col : Nat) (s : State α) (hr : row<p.rows) (hc : col<50257) :
    (fixedGrid p ops input s).memory (globalCell 0 (address row col))=some (normOutputValue ops input row col) :=
  fixed_block_fold_output_member p ops input (List.range p.rows) s List.nodup_range row col (List.mem_range.mpr hr) hc

theorem fixed_grid_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (entry : GridRowsEntry p input (List.range p.rows) s) : ∀ a ∈ (fixedGrid p ops input s).trace, Good a :=
  fixed_block_fold_good p ops input (List.range p.rows) s List.nodup_range entry (entry 0 (List.mem_range.mpr p.positive)).good

theorem fixed_grid_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (entry : GridRowsEntry p input (List.range p.rows) s) : Reads p input (fixedGrid p ops input s) :=
  fixed_block_fold_reads p ops input (List.range p.rows) s List.nodup_range entry (entry 0 (List.mem_range.mpr p.positive)).reads

theorem fixed_grid_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) :
    (fixedGrid p ops input s).trace.length=s.trace.length+475752*p.rows := by
  simpa only [List.length_range] using fixed_block_fold_trace_length p ops input (List.range p.rows) s

theorem grid_halt_of_pc (p : Shape) (s : State α)
    (hp : ∀ t, t<p.rows*1024 → s.pc t=normPc true 115) :
    LarkCollective.converged (program true) (List.range (p.rows*1024)) s=some .halt := by
  have hpos : 0<p.rows*1024 := by have h := p.positive; omega
  have hp0 := hp 0 hpos
  have ha : (List.range (p.rows*1024)).all (fun t => s.pc t == s.pc 0)=true := by
    apply List.all_eq_true.mpr
    intro t ht
    simp [hp t (List.mem_range.mp ht),hp0]
  unfold LarkCollective.converged
  rewrite [List.head?_range,if_neg (by omega : p.rows*1024 ≠ 0)]
  simp only [bind,pure,Option.bind,ha,↓reduceIte]
  unfold LarkCollective.parked
  rewrite [hp0,(norm_round_end_codes true).2.2]
  rfl

theorem fixed_grid_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) :
    LarkCollective.converged (program true) (List.range ((geometry p).grid*(geometry p).block)) (fixedGrid p ops input s)=some .halt := by
  apply grid_halt_of_pc p
  intro t ht
  have hr : t/1024<p.rows := by omega
  have he : (t/1024)*1024+t%1024=t := by omega
  simpa only [he] using fixed_grid_pc p ops input (t/1024) (t%1024) s hr (Nat.mod_lt _ (by decide))

theorem fixed_grid_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (entry : GridRowsEntry p input (List.range p.rows) s) :
    LarkPartitionCollective.runGrid ops (layout p) (geometry p) fuel (program true) fuel.grid s=some (fixedGrid p ops input s) := by
  change LarkPartitionCollective.runGrid ops (layout p) (geometry p) fuel (program true) (0+1) s=_
  rewrite [LarkPartitionCollective.runGrid,fixed_grid_fold_run p ops input s entry]
  simp only [bind,pure,Option.some_bind,fixed_grid_cut p ops input s,reduceCtorEq,↓reduceIte]

theorem fixed_launch_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (entry : GridRowsEntry p input (List.range p.rows) s) :
    LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel (program true) s=some (fixedGrid p ops input s) := by
  have hv : ¬ ((geometry p).grid=0 ∨ (geometry p).block=0 ∨ (geometry p).warp ≠ 64 ∨ (geometry p).block%64 ≠ 0) := by
    have hrows : p.rows ≠ 0 := Nat.ne_of_gt p.positive
    simp [geometry,hrows]
  rewrite [LarkPartitionCollective.runLaunch,if_neg hv]
  exact fixed_grid_run p ops input s entry

theorem initial_fixed_launch (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel (program true) (initial (layout p) input outside)=
      some (fixedInitialGrid p ops input outside) :=
  fixed_launch_run p ops input _ (initial_grid_rows_entry p input outside)

theorem initial_fixed_grid_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree (geometry p) (fixedInitialGrid p ops input outside).trace=true :=
  race_free p _ (fixed_grid_good p ops input _ (initial_grid_rows_entry p input outside))

theorem initial_fixed_grid_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row col : Nat) (hr : row<p.rows) (hc : col<50257) :
    (fixedInitialGrid p ops input outside).memory (globalCell 0 (address row col))=some (normOutputValue ops input row col) :=
  fixed_grid_outputs p ops input row col _ hr hc

theorem initial_fixed_grid_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    (fixedInitialGrid p ops input outside).trace.length=475752*p.rows :=
  exp_trace_length_of_nil (initial (layout p) input outside) (fixedInitialGrid p ops input outside) _ rfl (fixed_grid_trace_length p ops input _)

#print axioms initial_grid_rows_entry
#print axioms fixed_grid_fold_run
#print axioms fixed_grid_pc
#print axioms fixed_grid_epoch
#print axioms fixed_grid_outputs
#print axioms fixed_grid_good
#print axioms fixed_grid_reads
#print axioms fixed_grid_trace_length
#print axioms grid_halt_of_pc
#print axioms fixed_grid_cut
#print axioms fixed_grid_run
#print axioms fixed_launch_run
#print axioms initial_fixed_launch
#print axioms initial_fixed_grid_race_free
#print axioms initial_fixed_grid_output
#print axioms initial_fixed_grid_trace_length
end LarkNativeSoftmax
