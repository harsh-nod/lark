"""Source-bound complete block execution and converted-output witnesses."""

EXTRA = r'''
def sourceWholeBlock (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) : State α :=
  wholeBlock p guarded ops input row (sourceInitial p input outside)

theorem source_whole_block_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    sourceBlock p guarded ops row sourceFuel.block (sourceInitial p input outside)=
      some (sourceWholeBlock p guarded ops input outside row) := by
  rewrite [source_block_data,(source_interface_data p).2.2]
  exact whole_block_run p guarded ops input row _ (by
    rewrite [source_initial_data]
    exact initial_block_entry p input outside row hr)

theorem source_whole_block_pc (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (ht : tid<1024) :
    (sourceWholeBlock p guarded ops input outside row).pc (row*1024+tid)=normPc guarded 115 :=
  whole_block_pc p guarded ops input row tid _ ht

theorem source_whole_block_epoch (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    ((sourceWholeBlock p guarded ops input outside row).epochs (row*1024+tid)).block=4 :=
  (congrArg (fun epochs => (epochs (row*1024+tid)).block)
    (whole_block_normalization_epochs p guarded ops input row (sourceInitial p input outside))).trans
      (source_sum_initial_epoch p ops input outside row tid hr ht)

theorem source_whole_block_outputs (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    NormOutputRow ops input row (sourceWholeBlock p guarded ops input outside row) :=
  whole_block_outputs p guarded ops input row _

theorem source_whole_block_output (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row col : Nat) (hc : col<50257) :
    (sourceWholeBlock p guarded ops input outside row).memory (globalCell 0 (address row col))=
      some (normOutputValue ops input row col) := source_whole_block_outputs p guarded ops input outside row col hc

theorem source_whole_block_trace (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    (sourceWholeBlock p guarded ops input outside row).trace.length=(if guarded then 475752 else 489926) := by
  change (wholeBlock p guarded ops input row (sourceInitial p input outside)).trace.length=_
  rewrite [source_initial_data]
  exact initial_whole_block_trace_length p guarded ops input outside row

theorem source_whole_block_fixed_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    ∀ a ∈ (sourceWholeBlock p true ops input outside row).trace, Good a :=
  whole_block_fixed_good p ops input row _ (by
    rewrite [source_initial_data]
    exact initial_block_entry p input outside row hr)

theorem source_whole_block_fixed_rf (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    raceFree (sourceGeometry p) (sourceWholeBlock p true ops input outside row).trace=true := by
  rewrite [(source_interface_data p).2.1]
  exact race_free p _ (source_whole_block_fixed_good p ops input outside row hr)

theorem source_whole_block_output_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row col : Nat) (hr : row<p.rows) (hc : col<50257) :
    (sourceBlock p guarded ops row sourceFuel.block (sourceInitial p input outside)).map
      (fun s => s.memory (globalCell 0 (address row col)))=some (some (normOutputValue ops input row col)) :=
  source_memory_of_run _ (sourceWholeBlock p guarded ops input outside row) _ _
    (source_whole_block_run p guarded ops input outside row hr) (source_whole_block_output p guarded ops input outside row col hc)

theorem source_whole_block_not_none (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    sourceBlock p guarded ops row sourceFuel.block (sourceInitial p input outside) ≠ none := by
  rewrite [source_whole_block_run p guarded ops input outside row hr]
  simp only [ne_eq,reduceCtorEq,not_false_eq_true]

theorem source_normalization_lane_run (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    sourceLane p guarded ops (row*1024+tid) sourceFuel.lane (sourceSumState p ops input outside row)=
      some (normLaneState guarded ops input row tid (sourceSumState p ops input outside row)) := by
  rewrite [source_lane_data,(source_interface_data p).2.2]
  exact norm_lane_run p guarded ops input row tid _
    (norm_entry_of_sum p ops input row tid _ ht (source_sum_initial_ready p ops input outside row hr)
      (source_sum_initial_outputs p ops input outside row))

theorem source_normalization_lane_cost (guarded : Bool) (tid : Nat) (ht : tid<1024) :
    normLaneCost guarded tid=(if guarded then (if tid<81 then 862 else 857) else (if tid<81 then 880 else 878)) :=
  norm_lane_cost_exact guarded tid ht

theorem whole_projection_value_0 : normOutputValue reductionProjectionOps reductionProjectionInput 0 0=50 := by
  unfold normOutputValue
  rewrite [reduction_projection_output_0,reduction_projection_total]
  decide

theorem whole_projection_value_50256 : normOutputValue reductionProjectionOps reductionProjectionInput 0 50256=148 := by
  unfold normOutputValue
  rewrite [reduction_projection_output_50256,reduction_projection_total]
  decide

theorem source_whole_projection_output_0 (guarded : Bool) :
    (sourceBlock expWordOne guarded reductionProjectionOps 0 sourceFuel.block
      (sourceInitial expWordOne reductionProjectionInput (fun _ => none))).map
        (fun s => s.memory (globalCell 0 (address 0 0)))=some (some 50) :=
  (source_whole_block_output_run expWordOne guarded reductionProjectionOps reductionProjectionInput (fun _ => none) 0 0
    (by decide) (by decide)).trans (congrArg (fun n : Nat => some (some n)) whole_projection_value_0)

theorem source_whole_projection_output_50256 (guarded : Bool) :
    (sourceBlock expWordOne guarded reductionProjectionOps 0 sourceFuel.block
      (sourceInitial expWordOne reductionProjectionInput (fun _ => none))).map
        (fun s => s.memory (globalCell 0 (address 0 50256)))=some (some 148) :=
  (source_whole_block_output_run expWordOne guarded reductionProjectionOps reductionProjectionInput (fun _ => none) 0 50256
    (by decide) (by decide)).trans (congrArg (fun n : Nat => some (some n)) whole_projection_value_50256)
'''

import re
EXTRA += "\n" + "\n".join("#print axioms " + name for name in re.findall(r"^theorem (\w+)", EXTRA, re.M)) + "\n"
