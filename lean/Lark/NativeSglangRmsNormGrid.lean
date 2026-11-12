import Lark.NativeSglangRmsNormRows

/-! Complete actual guarded native launch under the unchanged grid scheduler.
Every initialized row block completes; all outputs retain the source-ordered
arbitrary-Ops values and the entire recorded launch trace is race-free.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot skipFold inactiveWaves scalePairs scaleRounds outputCopies outputFold

theorem grid_halt_of_pc (p : Shape) (s : State α) (hp : ∀ t,t<p.rows*1024 → s.pc t=109) :
    LarkCollective.converged (program true) (List.range (p.rows*1024)) s=some .halt := by
  have hn : List.range (p.rows*1024)≠[] := by
    intro he
    have hm : 0∈List.range (p.rows*1024) := List.mem_range.mpr (Nat.mul_pos p.positive (by decide))
    rw [he] at hm
    cases hm
  exact halt_converged _ s hn (fun t ht => hp t (List.mem_range.mp ht))

theorem launch_of_rows (p : Shape) (ops : Ops α) (s next : State α)
    (hf : (List.range p.rows).foldlM
      (fun u row => LarkPartitionCollective.runBlock ops (layout p) (geometry p) fuel (program true) row fuel.block u) s=some next)
    (hc : LarkCollective.converged (program true) (List.range (p.rows*1024)) next=some .halt) :
    LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel (program true) s=some next := by
  have guard : ¬((geometry p).grid=0 ∨ (geometry p).block=0 ∨ (geometry p).warp≠64 ∨ (geometry p).block%64≠0) := by
    have positive := p.positive
    simp only [geometry]
    omega
  rw [LarkPartitionCollective.runLaunch,if_neg guard]
  change LarkPartitionCollective.runGrid ops (layout p) (geometry p) fuel (program true) (0+1) s=_
  rw [LarkPartitionCollective.runGrid,show (geometry p).grid=p.rows from rfl,hf]
  simp only [bind,pure,Option.some_bind,show (geometry p).block=1024 from rfl,hc,reduceCtorEq,↓reduceIte]

def finalState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) : State α :=
  nativeRows p ops input (List.range p.rows) (initial p input outside)

theorem final_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (t : Nat) (ht : t<p.rows*1024) : (finalState p ops input outside).pc t=109 := by
  have hr : t/1024<p.rows := by omega
  have hl : t%1024<1024 := Nat.mod_lt _ (by decide)
  have he : t/1024*1024+t%1024=t := by omega
  have h := native_rows_pc p ops input (List.range p.rows) (initial p input outside) List.nodup_range
    (t/1024) (t%1024) (List.mem_range.mpr hr) hl
  exact (congrArg (fun u => (finalState p ops input outside).pc u) he).symm.trans h

theorem final_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (row : Nat) (hr : row<p.rows) : RowValues ops input row (finalState p ops input outside) :=
  native_rows_values p ops input (List.range p.rows) (initial p input outside) List.nodup_range
    (fun r hr => initial_block_entry p input outside r (List.mem_range.mp hr)) row (List.mem_range.mpr hr)

theorem final_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    Reads p input (finalState p ops input outside) :=
  native_rows_reads p ops input (List.range p.rows) (initial p input outside) (initial_reads p input outside)

theorem final_exec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    LarkPartitionCollective.runLaunch ops (layout p) (geometry p) fuel (program true) (initial p input outside)=
      some (finalState p ops input outside) ∧ raceFree (geometry p) (finalState p ops input outside).trace=true := by
  have h := native_rows_exec p ops input (List.range p.rows) (initial p input outside) List.nodup_range
    (fun row hr => initial_block_entry p input outside row (List.mem_range.mp hr)) (by intro event he; cases he)
  exact ⟨launch_of_rows p ops (initial p input outside) (finalState p ops input outside) h.1
    (grid_halt_of_pc p (finalState p ops input outside) (final_pc p ops input outside)),race_free p _ h.2⟩

theorem final_global_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (offset : Nat) (ho : offset<p.rows*16384) :
    (finalState p ops input outside).memory (globalCell 0 offset)=some (sourceResult ops input (offset/16384) (offset%16384)) := by
  have hr : offset/16384<p.rows := by omega
  have hc : offset%16384<16384 := Nat.mod_lt _ (by decide)
  have he : offset/16384*16384+offset%16384=offset := by omega
  simpa only [address,he] using final_values p ops input outside (offset/16384) hr (offset%16384) hc

#print axioms grid_halt_of_pc
#print axioms launch_of_rows
#print axioms final_pc
#print axioms final_values
#print axioms final_reads
#print axioms final_exec
#print axioms final_global_value
end LarkNativeSglangRmsNorm
