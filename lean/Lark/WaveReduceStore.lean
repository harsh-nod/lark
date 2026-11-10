import Lark.WaveReduceArithmetic

namespace LarkCollective.WaveSum
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def written (t : Nat) (v : α) (s : State α) : State α :=
  advance { record s t (Transfer.outputCell t) true with
    memory := fun l => if l = Transfer.outputCell t then some v else s.memory l } t 15

def finalPartial (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : Nat → State α
  | 0 => shuffled ops input outside 5
  | k + 1 => written k (value ops input 6 k)
      (RegisterPhase.added 14 k (value ops input 6 k) (finalPartial ops input outside k))

theorem final_pc (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) :
    (finalPartial ops input outside k).pc t =
      if t < k then 15 else if t < 64 then 13 else 0 := by
  induction k with
  | zero => simp [finalPartial, shuffled_pc]
  | succ k ih =>
      simp only [finalPartial, written, RegisterPhase.added, advance, record, ih]
      by_cases he : t = k
      · simp [he]
      · by_cases ht : t < k
        · have hh : t < k + 1 := by omega
          simp [he, ht, hh]
        · have hh : ¬ t < k + 1 := by omega
          simp [he, ht, hh]

theorem final_indices (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) (ht : t < 64) :
    (finalPartial ops input outside k).indices t 0 = some (t : Int) := by
  induction k with
  | zero => exact shuffled_indices ops input outside 5 t ht
  | succ k ih => simpa only [finalPartial, written, RegisterPhase.added, advance, record] using ih

theorem final_regs_zero (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) (ht : t < 64) :
    (finalPartial ops input outside k).regs t 0 =
      some (if t < k then value ops input 6 t else value ops input 5 t) := by
  induction k with
  | zero => simp [finalPartial, shuffled_regs_zero, ht]
  | succ k ih =>
      simp only [finalPartial, written, RegisterPhase.added, advance, record, ih, and_true]
      by_cases he : t = k
      · simp [he]
      · by_cases hh : t < k
        · have hk : t < k + 1 := by omega
          simp [he, hh, hk]
        · have hk : ¬ t < k + 1 := by omega
          simp [he, hh, hk]

theorem final_regs_one (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) (ht : t < 64) :
    (finalPartial ops input outside k).regs t 1 =
      some (value ops input 5 (Nat.xor t (distance 5))) := by
  induction k with
  | zero => exact shuffled_regs_one ops input outside 5 t ht
  | succ k ih => simp [finalPartial, written, RegisterPhase.added, advance, record, ih]

theorem final_output (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (k t : Nat) (ht : t < k) :
    (finalPartial ops input outside k).memory (Transfer.outputCell t) =
      some (value ops input 6 t) := by
  induction k with
  | zero => omega
  | succ k ih =>
      simp only [finalPartial, written, RegisterPhase.added, advance, record]
      by_cases he : t = k
      · simp [he]
      · have hn : Transfer.outputCell t ≠ Transfer.outputCell k := by
          intro hh
          exact he (congrArg Location.offset hh)
        rewrite [if_neg hn]
        exact ih (by omega)

theorem final_owned (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (k : Nat) :
    Owned (finalPartial ops input outside k).trace := by
  induction k with
  | zero => exact phase_owned ops input outside 5
  | succ k ih =>
      intro a ha
      simp only [finalPartial, written, RegisterPhase.added, advance, record, List.mem_cons] at ha
      rcases ha with rfl | ha
      · rfl
      · exact ih a ha

theorem last_lane (ops : Ops α) (t : Nat) (s : State α) (a b : α)
    (ht : t < 64) (hp : s.pc t = 13) (hix : s.indices t 0 = some (t : Int))
    (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b) :
    runLane ops layout geometry program t fuel.lane s =
      some (written t (ops.add a b) (RegisterPhase.added 14 t (ops.add a b) s)) := by
  have first := RegisterPhase.assign_step ops layout geometry 13 t s a b hp ha hb
  have hnot : ¬ (t : Int) < 0 := by omega
  have hrole : (Role.output == Role.input) = false := by decide
  have hloc : location layout geometry t .global 1 (t : Int) true =
      some (Transfer.outputCell t) := by
    simp [location, layout, Transfer.layout, Transfer.outputCell, hnot, ht, hrole]
  have hstore : execute ops layout geometry t (.store .global 1 (.ivar 0) (.reg 0))
      (RegisterPhase.added 14 t (ops.add a b) s) =
      some (written t (ops.add a b) (RegisterPhase.added 14 t (ops.add a b) s)) := by
    simp [execute, evalIndex, hix, hloc, evalExpr, RegisterPhase.added, written, advance, record]
  change runLane ops layout geometry program t (3 + 1) s = _
  rewrite [Transfer.lane_step ops _ _ _ _ _ _ (by simp [parked, program, hp])
    (by simp [program, hp]) first]
  rewrite [Transfer.lane_step ops _ _ _ _ _ _
    (by simp [parked, program, RegisterPhase.added, advance])
    (by simp [program, RegisterPhase.added, advance]) hstore]
  simp [runLane, parked, program, written, advance]

theorem last_fold (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (k : Nat) (hk : k ≤ 64) :
    (List.range k).foldlM (fun s t => runLane ops layout geometry program t fuel.lane s)
      (shuffled ops input outside 5) = some (finalPartial ops input outside k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rewrite [List.range_succ, List.foldlM_append, ih (by omega)]
      simp only [List.foldlM_cons, List.foldlM_nil, bind, pure, Option.bind]
      rewrite [last_lane ops k _ (value ops input 5 k)
        (value ops input 5 (Nat.xor k (distance 5))) (by omega)
        (by simp [final_pc, show k < 64 by omega])
        (final_indices ops input outside k k (by omega))
        (by simp [final_regs_zero, show k < 64 by omega])
        (final_regs_one ops input outside k k (by omega))]
      rfl

theorem converged_final (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    converged program (List.range 64) (finalPartial ops input outside 64) = some .halt := by
  have hhead : (List.range 64).head? = some 0 := by decide
  have hall : (List.range 64).all (fun t => (finalPartial ops input outside 64).pc t ==
      (finalPartial ops input outside 64).pc 0) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    simp [final_pc, List.mem_range.mp ht]
  simp only [converged, hhead, bind, pure, Option.bind, hall, ↓reduceIte]
  simp [parked, final_pc, program]

#print axioms last_fold
#print axioms final_owned
end LarkCollective.WaveSum
