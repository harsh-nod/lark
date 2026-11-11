"""Source-bound complete repaired native64 grid execution."""

EXTRA = r'''
def sourceLaunch (p : Shape) (guarded : Bool) (ops : Ops α) (s : State α) : Option (State α) :=
  LarkPartitionCollective.runLaunch ops (sourceLayout p) (sourceGeometry p) sourceFuel
    (if guarded then sourceFixed else sourceOriginal) s

def sourceFixedGrid (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  fixedInitialGrid p ops input outside

theorem source_launch_data (p : Shape) (guarded : Bool) (ops : Ops α) (s : State α) :
    sourceLaunch p guarded ops s=
      LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel (program guarded) s := by
  simp only [sourceLaunch,program,source_program_data.1,source_program_data.2,
    (source_interface_data p).1,(source_interface_data p).2.1,(source_interface_data p).2.2]

theorem source_fixed_grid_launch (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    sourceLaunch p true ops (sourceInitial p input outside)=some (sourceFixedGrid p ops input outside) := by
  rewrite [source_launch_data,source_initial_data]
  exact initial_fixed_launch p ops input outside

theorem source_fixed_grid_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    (sourceFixedGrid p ops input outside).pc (row*1024+tid)=115 :=
  fixed_grid_pc p ops input row tid (initial (layout p) input outside) hr ht

theorem source_fixed_grid_epoch (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row<p.rows) (ht : tid<1024) :
    ((sourceFixedGrid p ops input outside).epochs (row*1024+tid)).block=4 :=
  fixed_grid_epoch p ops input row tid (initial (layout p) input outside)
    (initial_grid_rows_entry p input outside) hr ht

theorem source_fixed_grid_trace (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    (sourceFixedGrid p ops input outside).trace.length=475752*p.rows :=
  initial_fixed_grid_trace_length p ops input outside

theorem source_fixed_grid_output (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (offset : Nat) (ho : offset<p.rows*50257) :
    (sourceFixedGrid p ops input outside).memory (globalCell 0 offset)=some (sourceOutputValue ops input offset) :=
  initial_fixed_grid_flat_output p ops input outside offset ho

theorem source_fixed_grid_rf (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree (sourceGeometry p) (sourceFixedGrid p ops input outside).trace=true := by
  rewrite [(source_interface_data p).2.1]
  exact initial_fixed_grid_race_free p ops input outside

theorem source_fixed_grid_extract (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    extract (sourceLayout p) (sourceFixedGrid p ops input outside)=some (sourceOrderedSpec p ops input) := by
  rewrite [(source_interface_data p).1]
  exact initial_fixed_grid_extract p ops input outside

theorem source_fixed_grid_correct (p : Shape) (ops : Ops α) :
    LarkPartitionCollective.Correct ops (sourceLayout p) (sourceGeometry p) sourceFuel sourceFixed (sourceOrderedSpec p ops) := by
  rewrite [(source_interface_data p).1,(source_interface_data p).2.1,(source_interface_data p).2.2,source_program_data.2]
  exact source_order_correct p ops

#print axioms source_launch_data
#print axioms source_fixed_grid_launch
#print axioms source_fixed_grid_pc
#print axioms source_fixed_grid_epoch
#print axioms source_fixed_grid_trace
#print axioms source_fixed_grid_output
#print axioms source_fixed_grid_rf
#print axioms source_fixed_grid_extract
#print axioms source_fixed_grid_correct
'''
