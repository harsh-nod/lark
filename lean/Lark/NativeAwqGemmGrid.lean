import Lark.NativeAwqGemmBlockFrames

/-! The original full grid executes every complete block and converges at
the original halt with the unchanged lane, warp, block and grid budgets. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] wholeBlock

theorem different_block_threads (p : Shape) (b c t : Nat) (different : b≠c)
    (ht : t∈blockThreads (geometry p) b) : t∉blockThreads (geometry p) c := by
  intro hc
  exact different ((block_thread_block p b t ht).symm.trans (block_thread_block p c t hc))

def gridFold (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (bs : List Nat) (s : State α) : State α :=
  bs.foldl (fun state b => wholeBlock p ops input b state) s

theorem grid_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (s : State α) (reads : Reads p input s) : Reads p input (gridFold p ops input bs s) := by
  induction bs generalizing s with
  | nil => exact reads
  | cons b bs ih => exact ih _ (whole_block_reads p ops input b s reads)

theorem grid_fold_other_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (t : Nat) (s : State α) (outside : ∀ b∈bs, t∉blockThreads (geometry p) b) :
    (gridFold p ops input bs s).pc t=s.pc t := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    exact (ih (wholeBlock p ops input b s) (fun c hc => outside c (List.mem_cons_of_mem b hc))).trans
      (whole_block_other_pc p ops input b t s (outside b (by simp)))

theorem grid_fold_halt (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (b t : Nat) (s : State α) (hd : bs.Nodup) (hb : b∈bs)
    (ht : t∈blockThreads (geometry p) b) : (gridFold p ops input bs s).pc t=haltPC p := by
  induction bs generalizing s with
  | nil => simp at hb
  | cons c bs ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    rcases List.mem_cons.mp hb with same | member
    · subst b
      have frame := grid_fold_other_pc p ops input bs t (wholeBlock p ops input c s)
        (fun d hd => different_block_threads p c d t (by intro same; subst d; exact disjoint hd) ht)
      exact frame.trans (whole_block_halt p ops input c t s ht)
    · exact ih (wholeBlock p ops input c s) tail member

theorem grid_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (bs : List Nat) (s : State α) (hd : bs.Nodup) (bounds : ∀ b∈bs, b<(geometry p).grid)
    (reads : Reads p input s) (hp : ∀ b∈bs, ∀ t∈blockThreads (geometry p) b, s.pc t=0) :
    bs.foldlM (fun state b => LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b (fuel p).block state) s=
      some (gridFold p ops input bs s) := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    rw [List.foldlM_cons,whole_block_run p ops input b s (bounds b (by simp)) reads (hp b (by simp))]
    change bs.foldlM _ (wholeBlock p ops input b s)=some (gridFold p ops input bs (wholeBlock p ops input b s))
    apply ih _ tail (fun c hc => bounds c (List.mem_cons_of_mem b hc)) (whole_block_reads p ops input b s reads)
    intro c hc t ht
    rw [whole_block_other_pc p ops input b t s
      (different_block_threads p c b t (by intro same; subst c; exact disjoint hc) ht)]
    exact hp c (List.mem_cons_of_mem b hc) t ht

def wholeGrid (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) : State α :=
  gridFold p ops input (List.range (geometry p).grid) s

theorem thread_in_own_block (p : Shape) (t : Nat) : t∈blockThreads (geometry p) (blockId t) := by
  have coordinates := block_lane_coordinates p (blockId t) (laneId t) (lane_bound t)
  have recover : blockId t*64+laneId t=t := by unfold blockId laneId; omega
  rw [recover] at coordinates
  exact coordinates.2.2

theorem whole_grid_halt (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (t : Nat) (ht : t<(geometry p).grid*64) : (wholeGrid p ops input s).pc t=haltPC p :=
  grid_fold_halt p ops input _ (blockId t) t s List.nodup_range
    (List.mem_range.mpr (by unfold blockId; omega)) (thread_in_own_block p t)

theorem whole_grid_converged (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) :
    LarkMFMA.converged (program p) (List.range ((geometry p).grid*(geometry p).block))
      (wholeGrid p ops input s)=some .halt := by
  have gridPositive : 0<(geometry p).grid := Nat.mul_pos (row_tiles_positive p) (column_tiles_positive p)
  have positive : 0<(geometry p).grid*64 := by omega
  have head : (List.range ((geometry p).grid*(geometry p).block)).head?=some 0 := by
    change (List.range ((geometry p).grid*64)).head?=some 0
    rw [List.head?_range,if_neg (by omega : (geometry p).grid*64≠0)]
  have headPC := whole_grid_halt p ops input s 0 positive
  have allPC : (List.range ((geometry p).grid*(geometry p).block)).all
      (fun t => (wholeGrid p ops input s).pc t==(wholeGrid p ops input s).pc 0)=true := by
    apply List.all_eq_true.mpr
    intro t ht
    rw [whole_grid_halt p ops input s t (List.mem_range.mp ht),headPC]
    simp
  simp only [LarkMFMA.converged,head,bind,pure,Option.bind]
  rw [allPC]
  simp only [ite_true,LarkMFMA.parked,headPC,output_halt_site]

theorem whole_grid_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α)
    (reads : Reads p input s) (hp : ∀ t, t<(geometry p).grid*64 → s.pc t=0) :
    LarkMFMA.runGrid ops (layout p) (geometry p) (fuel p) (program p) (fuel p).grid s=
      some (wholeGrid p ops input s) := by
  have blocks := grid_fold_run p ops input (List.range (geometry p).grid) s List.nodup_range
    (fun b hb => List.mem_range.mp hb) reads
    (fun b hb t ht => hp t (block_thread_bound p b t (List.mem_range.mp hb) ht))
  change (List.range (geometry p).grid).foldlM _ s=some (wholeGrid p ops input s) at blocks
  have converged := whole_grid_converged p ops input s
  change LarkMFMA.runGrid ops (layout p) (geometry p) (fuel p) (program p) 1 s=_
  simp [LarkMFMA.runGrid,blocks,converged]

theorem initialized_whole_grid_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    LarkMFMA.runGrid ops (layout p) (geometry p) (fuel p) (program p) (fuel p).grid
      (initial (layout p) input outside)=some (wholeGrid p ops input (initial (layout p) input outside)) :=
  whole_grid_run p ops input _ (initial_reads p input outside) (fun _ _ => rfl)

#print axioms different_block_threads
#print axioms grid_fold_reads
#print axioms grid_fold_other_pc
#print axioms grid_fold_halt
#print axioms grid_fold_run
#print axioms thread_in_own_block
#print axioms whole_grid_halt
#print axioms whole_grid_converged
#print axioms whole_grid_run
#print axioms initialized_whole_grid_run
end LarkNativeAwqGemm
