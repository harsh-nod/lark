import Lark.WaveReduce

namespace LarkCollective.WaveSum
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem lookup_map_not_mem (xs : List Nat) (v : Nat → α) (t : Nat) (ht : t ∉ xs) :
    List.lookup t (xs.map (fun u => (u, v u))) = none := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      have hn : t ≠ a := by intro he; subst t; simp at ht
      have hb : (t == a) = false := by simp [hn]
      have htail : t ∉ xs := by intro hm; exact ht (List.mem_cons_of_mem a hm)
      simpa only [List.map_cons, List.lookup_cons, hb] using ih htail

theorem shuffled_indices (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n t : Nat) (ht : t < 64) :
    (shuffled ops input outside n).indices t 0 = some (t : Int) := by
  simp [shuffled, shuffleUpdates, phase_indices, ht]

theorem shuffled_regs_all (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n t r : Nat) :
    (shuffled ops input outside n).regs t r =
      if t < 64 then
        if r = 0 then some (value ops input n t) else
        if r = 1 then some (value ops input n (Nat.xor t (distance n))) else none
      else none := by
  by_cases ht : t < 64
  · by_cases h0 : r = 0
    · subst r
      simp only [ht, ↓reduceIte]
      exact shuffled_regs_zero ops input outside n t ht
    · by_cases h1 : r = 1
      · subst r
        simp only [ht, h0, ↓reduceIte]
        exact shuffled_regs_one ops input outside n t ht
      · simp [shuffled, shuffleUpdates, phaseState, ht, h0, h1]
  · have hn : t ∉ List.range 64 := by simpa using ht
    by_cases h1 : r = 1
    · subst r
      simp only [shuffled, shuffleUpdates, ↓reduceIte]
      rewrite [lookup_map_not_mem _ _ t hn]
      simp [phaseState, ht]
    · simp [shuffled, shuffleUpdates, phaseState, ht, h1]

def addPartial (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n k : Nat) : State α :=
  RegisterPhase.partialState (4 + 2 * n) (value ops input (n + 1))
    (shuffled ops input outside n) k

theorem add_pc (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n k t : Nat) :
    (addPartial ops input outside n k).pc t =
      if t < k then 4 + 2 * n else if t < 64 then 3 + 2 * n else 0 := by
  simp only [addPartial, RegisterPhase.partial_pc, shuffled_pc]

theorem add_regs_zero (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n k t : Nat) (ht : t < 64) :
    (addPartial ops input outside n k).regs t 0 =
      some (if t < k then value ops input (n + 1) t else value ops input n t) := by
  simp only [addPartial, RegisterPhase.partial_regs, and_true, shuffled_regs_zero ops input outside n t ht]
  split <;> rfl

theorem add_regs_one (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n k t : Nat) (ht : t < 64) :
    (addPartial ops input outside n k).regs t 1 =
      some (value ops input n (Nat.xor t (distance n))) := by
  simp [addPartial, RegisterPhase.partial_regs, shuffled_regs_one, ht]

theorem add_complete (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n : Nat) :
    addPartial ops input outside n 64 = phaseState ops input outside (n + 1) := by
  have preserved := RegisterPhase.partial_preserves (4 + 2 * n) (value ops input (n + 1))
    (shuffled ops input outside n) 64
  apply state_ext
  · funext t
    rewrite [add_pc, phase_pc]
    by_cases ht : t < 64 <;> simp only [ht, ↓reduceIte] <;> omega
  · exact preserved.1
  · funext t r
    simp only [addPartial, RegisterPhase.partial_regs, shuffled_regs_all]
    by_cases ht : t < 64
    · by_cases h0 : r = 0
      · simp [phaseState, ht, h0]
      · by_cases h1 : r = 1 <;> simp [phaseState, ht, h0, h1]
    · simp [phaseState, ht]
  · exact preserved.2.1
  · exact preserved.2.2.1
  · exact preserved.2.2.2

theorem add_lane (ops : Ops α) (n t : Nat) (hn : n < 5) (s : State α) (a b : α)
    (hp : s.pc t = 3 + 2 * n) (ha : s.regs t 0 = some a) (hb : s.regs t 1 = some b) :
    runLane ops layout geometry program t fuel.lane s =
      some (RegisterPhase.added (4 + 2 * n) t (ops.add a b) s) := by
  have hpc : 3 + 2 * n + 1 = 2 + 2 * (n + 1) := by omega
  have hcut : parked program (RegisterPhase.added (3 + 2 * n + 1) t (ops.add a b) s) t =
      some .shuffle := by
    simp only [parked, RegisterPhase.added, advance, ↓reduceIte]
    rewrite [hpc, program_shuffle (n + 1) (by omega)]
    rfl
  have step := RegisterPhase.lane_step ops layout geometry program (3 + 2 * n) t 2 s a b
    .shuffle hp ha hb (program_add n (by omega)) hcut
  have he : 3 + 2 * n + 1 = 4 + 2 * n := by omega
  simpa only [fuel, he] using step

theorem add_fold (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n : Nat) (hn : n < 5) (k : Nat) (hk : k ≤ 64) :
    (List.range k).foldlM (fun s t => runLane ops layout geometry program t fuel.lane s)
      (shuffled ops input outside n) = some (addPartial ops input outside n k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rewrite [List.range_succ, List.foldlM_append, ih (by omega)]
      simp only [List.foldlM_cons, List.foldlM_nil, bind, pure, Option.bind]
      rewrite [add_lane ops n k hn _ (value ops input n k)
        (value ops input n (Nat.xor k (distance n)))
        (by simp [add_pc, show k < 64 by omega])
        (by simp [add_regs_zero, show k < 64 by omega])
        (add_regs_one ops input outside n k k (by omega))]
      rfl

#print axioms add_complete
#print axioms add_fold
end LarkCollective.WaveSum
