import Lark.NativeSoftmaxNormBlockMembers
import Lark.NativeSoftmaxSumEpoch
import Lark.NativeSoftmaxWitness

/-! A concrete conflicting pair belongs to the original complete block trace
reached from the actual initializer, for every supported row and all Ops and
inputs. This closes actual-access reachability; the synthetic instruction
snippet states need not equal the entire scheduler state. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def originalReader (row : Nat) : Access :=
  ⟨row*1024,globalCell 0 (address row 50256),false,⟨0,4,0⟩⟩

def originalWriter (row : Nat) : Access :=
  ⟨row*1024+80,globalCell 0 (address row 50256),true,⟨0,4,0⟩⟩

theorem original_read_column : normSelectedColumn false (column 0 6 2)=50256 := by
  change min 50256 51200=50256
  exact Nat.min_eq_left (by decide)

theorem original_write_column : column 80 6 1=50256 := by decide

theorem whole_block_original_read_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8) :
    normReadAccess row tid iteration component (sumState p ops input row s).epochs ∈
      (wholeBlock p false ops input row s).trace :=
  norm_block_original_member ops input row tid iteration component (sumState p ops input row s) ht hi hc

theorem whole_block_original_write_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8) (hcol : column tid iteration component<50257) :
    normWriteAccess row tid iteration component (sumState p ops input row s).epochs ∈
      (wholeBlock p false ops input row s).trace :=
  norm_block_valid_member false ops input row tid iteration component (sumState p ops input row s) ht hi hc hcol

theorem initial_original_reader_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    originalReader row ∈ (wholeBlock p false ops input row (initial (layout p) input outside)).trace := by
  have hm := whole_block_original_read_member p ops input row 0 6 2 (initial (layout p) input outside)
    (by decide) (by decide) (by decide)
  have he : (sumState p ops input row (initial (layout p) input outside)).epochs (row*1024)=⟨0,4,0⟩ := by
    simpa only [Nat.add_zero] using initial_sum_full_epoch p ops input outside row 0 (by decide)
  simpa only [normReadAccess,original_read_column,Nat.add_zero,he,originalReader] using hm

theorem initial_original_writer_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    originalWriter row ∈ (wholeBlock p false ops input row (initial (layout p) input outside)).trace := by
  have hm := whole_block_original_write_member p ops input row 80 6 1 (initial (layout p) input outside)
    (by decide) (by decide) (by decide) (by rewrite [original_write_column]; decide)
  have he := initial_sum_full_epoch p ops input outside row 80 (by decide)
  simpa only [normWriteAccess,original_write_column,he,originalWriter] using hm

theorem original_pair_conflicts (p : Shape) (row : Nat) :
    conflict (geometry p) (originalReader row) (originalWriter row)=true := by
  have h0 : (row*1024)/1024=row := by omega
  have h80 : (row*1024+80)/1024=row := by omega
  have m0 : (row*1024)%1024=0 := by omega
  have m80 : (row*1024+80)%1024=80 := by omega
  have hne : row*1024 ≠ row*1024+80 := by omega
  simp [originalReader,originalWriter,conflict,ordered,sameLocation,geometry,globalCell,h0,h80,m0,m80,hne]

theorem conflict_members_race_free_false (g : Geometry) (trace : List Access) (a b : Access)
    (ha : a∈trace) (hb : b∈trace) (hc : conflict g a b=true) : raceFree g trace=false := by
  apply List.all_eq_false.mpr
  refine ⟨a,ha,?_⟩
  intro hall
  have hp := List.all_eq_true.mp hall b hb
  rewrite [hc] at hp
  cases hp

theorem initial_original_block_race_free_false (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) :
    raceFree (geometry p) (wholeBlock p false ops input row (initial (layout p) input outside)).trace=false :=
  conflict_members_race_free_false (geometry p) _ (originalReader row) (originalWriter row)
    (initial_original_reader_member p ops input outside row) (initial_original_writer_member p ops input outside row)
    (original_pair_conflicts p row)

theorem initial_original_racy_block_execution (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row : Nat) (hr : row<p.rows) :
    ∃ final, LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program false) row fuel.block
      (initial (layout p) input outside)=some final ∧ raceFree (geometry p) final.trace=false :=
  ⟨wholeBlock p false ops input row (initial (layout p) input outside),initial_whole_block p false ops input outside row hr,
    initial_original_block_race_free_false p ops input outside row⟩

theorem original_reader_zero : originalReader 0=reader := rfl
theorem original_writer_zero : originalWriter 0=writerAccess := rfl

#print axioms original_read_column
#print axioms original_write_column
#print axioms whole_block_original_read_member
#print axioms whole_block_original_write_member
#print axioms initial_original_reader_member
#print axioms initial_original_writer_member
#print axioms original_pair_conflicts
#print axioms conflict_members_race_free_false
#print axioms initial_original_block_race_free_false
#print axioms initial_original_racy_block_execution
#print axioms original_reader_zero
#print axioms original_writer_zero
end LarkNativeSoftmax
