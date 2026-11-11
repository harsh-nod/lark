"""Reached conflicting accesses and original one-row source-launch counterexample."""

EXTRA = r'''
theorem source_original_reader_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    originalReader row ∈ (sourceWholeBlock p false ops input outside row).trace := by
  unfold sourceWholeBlock
  rewrite [source_initial_data]
  exact initial_original_reader_member p ops input outside row

theorem source_original_writer_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    originalWriter row ∈ (sourceWholeBlock p false ops input outside row).trace := by
  unfold sourceWholeBlock
  rewrite [source_initial_data]
  exact initial_original_writer_member p ops input outside row

theorem source_original_pair_conflicts (p : Shape) (row : Nat) :
    conflict (sourceGeometry p) (originalReader row) (originalWriter row)=true := by
  rewrite [(source_interface_data p).2.1]
  exact original_pair_conflicts p row

theorem source_original_block_race_false (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    raceFree (sourceGeometry p) (sourceWholeBlock p false ops input outside row).trace=false :=
  conflict_members_race_free_false (sourceGeometry p) _ (originalReader row) (originalWriter row)
    (source_original_reader_member p ops input outside row) (source_original_writer_member p ops input outside row)
    (source_original_pair_conflicts p row)

theorem source_original_block_race_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    (sourceBlock p false ops row sourceFuel.block (sourceInitial p input outside)).map
      (fun s => raceFree (sourceGeometry p) s.trace)=some false := by
  rewrite [source_whole_block_run p false ops input outside row hr]
  exact congrArg some (source_original_block_race_false p ops input outside row)

theorem source_original_racy_block (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    ∃ final, sourceBlock p false ops row sourceFuel.block (sourceInitial p input outside)=some final ∧
      originalReader row∈final.trace ∧ originalWriter row∈final.trace ∧ raceFree (sourceGeometry p) final.trace=false :=
  ⟨sourceWholeBlock p false ops input outside row,source_whole_block_run p false ops input outside row hr,
    source_original_reader_member p ops input outside row,source_original_writer_member p ops input outside row,
    source_original_block_race_false p ops input outside row⟩

theorem source_original_single_row_launch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (hrows : p.rows=1) :
    sourceLaunch p false ops (sourceInitial p input outside)=some (sourceWholeBlock p false ops input outside 0) := by
  unfold sourceWholeBlock
  rewrite [source_launch_data,source_initial_data]
  exact original_single_row_launch p ops input outside hrows

theorem source_original_single_row_racy_launch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (hrows : p.rows=1) :
    (sourceLaunch p false ops (sourceInitial p input outside)).map
      (fun s => raceFree (sourceGeometry p) s.trace)=some false := by
  rewrite [source_original_single_row_launch p ops input outside hrows]
  exact congrArg some (source_original_block_race_false p ops input outside 0)

theorem source_original_single_row_not_correct (p : Shape) (ops : Ops α)
    (spec : (Nat → Nat → α) → List α) (hrows : p.rows=1) :
    ¬ LarkPartitionCollective.Correct ops (sourceLayout p) (sourceGeometry p) sourceFuel sourceOriginal spec := by
  rewrite [(source_interface_data p).1,(source_interface_data p).2.1,(source_interface_data p).2.2,source_program_data.1]
  exact original_single_row_not_correct p ops spec hrows

theorem source_original_exact_witness_members (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    reader∈(sourceWholeBlock p false ops input outside 0).trace ∧
      writerAccess∈(sourceWholeBlock p false ops input outside 0).trace := by
  rewrite [←original_reader_zero,←original_writer_zero]
  exact ⟨source_original_reader_member p ops input outside 0,source_original_writer_member p ops input outside 0⟩

#print axioms source_original_reader_member
#print axioms source_original_writer_member
#print axioms source_original_pair_conflicts
#print axioms source_original_block_race_false
#print axioms source_original_block_race_run
#print axioms source_original_racy_block
#print axioms source_original_single_row_launch
#print axioms source_original_single_row_racy_launch
#print axioms source_original_single_row_not_correct
#print axioms source_original_exact_witness_members
'''
