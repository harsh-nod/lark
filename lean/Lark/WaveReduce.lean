import Lark.ShuffleTransfer
import Lark.CollectiveGather
import Lark.RegisterPhase
import Lark.ScalarLaunch

/-!
Lane masks, input loads and snapshot phases for one full-wave64 XOR reduction.
The complete actual launch theorem is assembled in Lark.WaveSum.
-/
namespace LarkCollective.WaveSum
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

abbrev layout : Layout := Transfer.layout
abbrev geometry : Geometry := Transfer.geometry
def fuel : Fuel := ⟨4, 7, 1, 1⟩
def distance (stage : Nat) : Nat := [32, 16, 8, 4, 2, 1][stage]?.getD 0
def program : List Instr :=
  [.scalar (.index 0 .tid), .scalar (.assign 0 (.load .global 0 (.ivar 0)))] ++
  [32, 16, 8, 4, 2, 1].flatMap (fun mask =>
    [.shuffle .xor 1 0 (.const (mask : Int)) 64,
     .scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))]) ++
  [.scalar (.store .global 1 (.ivar 0) (.reg 0)), .scalar .halt]

theorem program_shuffle (stage : Nat) (hs : stage < 6) :
    program[2 + 2 * stage]? = some (.shuffle .xor 1 0 (.const (distance stage : Int)) 64) := by
  have all : ∀ s : Fin 6,
      program[2 + 2 * s.val]? = some (.shuffle .xor 1 0 (.const (distance s.val : Int)) 64) := by
    decide
  exact all ⟨stage, hs⟩

theorem program_add (stage : Nat) (hs : stage < 6) :
    program[3 + 2 * stage]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) := by
  have all : ∀ s : Fin 6,
      program[3 + 2 * s.val]? = some (.scalar (.assign 0 (.bin .add (.reg 0) (.reg 1)))) := by
    decide
  exact all ⟨stage, hs⟩

theorem selected (stage t : Nat) (hs : stage < 6) (ht : t < 64) :
    sourceLane .xor 64 t (distance stage) = some (Nat.xor t (distance stage)) ∧
      Nat.xor t (distance stage) < 64 := by
  have all : ∀ s : Fin 6, ∀ t : Fin 64,
      sourceLane .xor 64 t.val (distance s.val) = some (Nat.xor t.val (distance s.val)) ∧
        Nat.xor t.val (distance s.val) < 64 := by
    decide
  exact all ⟨stage, hs⟩ ⟨t, ht⟩

def value (ops : Ops α) (input : Nat → Nat → α) : Nat → Nat → α
  | 0, t => input 0 t
  | n + 1, t => ops.add (value ops input n t)
      (value ops input n (Nat.xor t (distance n)))

def phaseState (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n : Nat) : State α :=
  let base := Transfer.loadPartial input outside 64
  { base with
    pc := fun t => if t < 64 then 2 + 2 * n else 0
    regs := fun t r => if t < 64 ∧ r = 0 then some (value ops input n t) else
      if t < 64 ∧ r = 1 ∧ 0 < n then
        some (value ops input (n - 1) (Nat.xor t (distance (n - 1)))) else none }

theorem state_ext (s u : State α)
    (hp : s.pc = u.pc) (hi : s.indices = u.indices) (hr : s.regs = u.regs)
    (hm : s.memory = u.memory) (he : s.epochs = u.epochs) (ht : s.trace = u.trace) : s = u := by
  cases s
  cases u
  cases hp
  cases hi
  cases hr
  cases hm
  cases he
  cases ht
  rfl

theorem phase_zero (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) :
    phaseState ops input outside 0 = Transfer.loadPartial input outside 64 := by
  apply state_ext
  · funext t
    simp [phaseState, Transfer.load_pc]
  · rfl
  · funext t r
    simp [phaseState, value, Transfer.load_regs]
  · rfl
  · rfl
  · rfl

theorem phase_pc (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n t : Nat) :
    (phaseState ops input outside n).pc t = if t < 64 then 2 + 2 * n else 0 := rfl

theorem phase_regs (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n t : Nat) (ht : t < 64) :
    (phaseState ops input outside n).regs t 0 = some (value ops input n t) := by
  simp [phaseState, ht]

theorem phase_indices (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n t : Nat) (ht : t < 64) :
    (phaseState ops input outside n).indices t 0 = some (t : Int) := by
  simp [phaseState, Transfer.load_indices, ht]

theorem phase_owned (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n : Nat) :
    Owned (phaseState ops input outside n).trace := Transfer.load_owned input outside 64

theorem load_lane (ops : Ops α) (t : Nat) (s : State α) (v : α)
    (ht : t < 64) (hp : s.pc t = 0) (hx : s.memory (Transfer.inputCell t) = some v) :
    runLane ops layout geometry program t fuel.lane s = some (Transfer.loaded t v s) := by
  have hn : (0 : Int) ≤ (t : Int) := by omega
  have hb : (t : Int) < 2147483648 := by omega
  have hnot : ¬ (t : Int) < 0 := by omega
  simp only [Transfer.inputCell] at hx
  have h1 : execute ops layout geometry t (.index 0 .tid) s = some (Transfer.indexed t s) := by
    simp [execute, evalIndex, geometry, Transfer.geometry, Nat.mod_eq_of_lt ht, int32, hn, hb,
      hp, Transfer.indexed, advance]
  have hix : evalIndex geometry t (Transfer.indexed t s) (.ivar 0) = some (t : Int) := by
    simp [evalIndex, Transfer.indexed, advance]
  have hloc : location layout geometry t .global 0 (t : Int) false =
      some (Transfer.inputCell t) := by
    simp [location, layout, Transfer.layout, Transfer.inputCell, hnot, ht]
  have h2 : execute ops layout geometry t (.assign 0 (.load .global 0 (.ivar 0)))
      (Transfer.indexed t s) = some (Transfer.loaded t v s) := by
    simp only [execute, evalExpr, hix, bind, pure, Option.bind, hloc]
    simp [Transfer.loaded, Transfer.indexed, advance, record, hx, Transfer.inputCell]
  change runLane ops layout geometry program t (3 + 1) s = _
  rewrite [Transfer.lane_step ops _ _ _ _ _ _ (by simp [parked, program, hp])
    (by simp [program, hp]) h1]
  rewrite [Transfer.lane_step ops _ _ _ _ _ _
    (by simp [parked, program, Transfer.indexed, advance])
    (by simp [program, Transfer.indexed, advance]) h2]
  simp [runLane, parked, program, Transfer.loaded, advance]

theorem load_fold (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (k : Nat) (hk : k ≤ 64) :
    (List.range k).foldlM (fun s t => runLane ops layout geometry program t fuel.lane s)
      (initial layout input outside) = some (Transfer.loadPartial input outside k) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rewrite [List.range_succ, List.foldlM_append, ih (by omega)]
      simp only [List.foldlM_cons, List.foldlM_nil, bind, pure, Option.bind]
      have hx : (Transfer.loadPartial input outside k).memory (Transfer.inputCell k) =
          some (input 0 k) := by
        rewrite [Transfer.load_memory]
        simp [initial, layout, Transfer.layout, Transfer.inputCell, show k < 64 by omega]
      rewrite [load_lane ops k _ _ (by omega) (by simp [Transfer.load_pc]) hx]
      rfl

theorem converged_phase (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n : Nat) (hn : n < 6) :
    converged program (List.range 64) (phaseState ops input outside n) = some .shuffle := by
  have hhead : (List.range 64).head? = some 0 := by decide
  have hall : (List.range 64).all (fun t => (phaseState ops input outside n).pc t ==
      (phaseState ops input outside n).pc 0) = true := by
    apply List.all_eq_true.mpr
    intro t ht
    simp [phase_pc, List.mem_range.mp ht]
  simp only [converged, hhead, bind, pure, Option.bind, hall, ↓reduceIte]
  simp only [parked, phase_pc, show (0 : Nat) < 64 by decide, ↓reduceIte]
  rewrite [program_shuffle n hn]
  rfl

theorem distance_bound (n : Nat) (hn : n < 6) : 0 < distance n ∧ distance n ≤ 32 := by
  have all : ∀ n : Fin 6, 0 < distance n.val ∧ distance n.val ≤ 32 := by decide
  exact all ⟨n, hn⟩

def shuffled (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n : Nat) : State α :=
  shuffleUpdates 1 ((List.range 64).map (fun t =>
    (t, value ops input n (Nat.xor t (distance n))))) (phaseState ops input outside n)

def shuffleEntry (ts : List Nat) (s : State α) (mask : Nat) : Nat → Option (Nat × α) :=
  Gather.readValue geometry ts s .xor 0 (.const (mask : Int)) 64

theorem eval_const_mask (s : State α) (t mask : Nat) (hm : mask ≤ 32) :
    evalIndex geometry t s (.const (mask : Int)) = some (mask : Int) := by
  have hlo : (0 : Int) ≤ (mask : Int) := by omega
  have hhi : (mask : Int) < 2147483648 := by omega
  simp only [evalIndex, int32]
  exact if_pos ⟨hlo, hhi⟩

theorem shuffle_entry_with_eval (ts : List Nat)
    (bound : ∀ t ∈ ts, t < 64) (covers : ∀ t, t < 64 → t ∈ ts)
    (mask : Nat) (argument : Int) (hn : ¬ argument < 0) (chosen : Nat → Nat)
    (selects : ∀ t, t < 64 → sourceLane .xor 64 t argument.toNat = some (chosen t) ∧ chosen t < 64)
    (s : State α) (values : Nat → α)
    (he : ∀ t, evalIndex geometry t s (.const (mask : Int)) = some argument)
    (hr : ∀ t, t < 64 → s.regs t 0 = some (values t)) (t : Nat) (ht : t ∈ ts) :
    shuffleEntry ts s mask t = some (t, values (chosen t)) := by
  unfold shuffleEntry Gather.readValue
  rewrite [he t]
  have hlt : t < 64 := bound t ht
  have hsel := selects t hlt
  simp only [bind, pure, Option.bind, hn, ↓reduceIte,
    geometry, Transfer.geometry, Nat.mod_eq_of_lt hlt, Nat.div_eq_of_lt hlt,
    Nat.zero_mul, Nat.zero_add]
  rewrite [hsel.1]
  have hc : ts.contains (chosen t) = true := by
    exact List.contains_iff_mem.mpr (covers _ hsel.2)
  simp only [bind, pure, Option.bind, hc, Bool.not_true, Bool.false_eq_true, ↓reduceIte,
    hr (chosen t) hsel.2]

theorem shuffle_entry (ts : List Nat)
    (bound : ∀ t ∈ ts, t < 64) (covers : ∀ t, t < 64 → t ∈ ts)
    (mask : Nat) (hm : mask ≤ 32) (chosen : Nat → Nat)
    (selects : ∀ t, t < 64 → sourceLane .xor 64 t mask = some (chosen t) ∧ chosen t < 64)
    (s : State α) (values : Nat → α)
    (hr : ∀ t, t < 64 → s.regs t 0 = some (values t)) (t : Nat) (ht : t ∈ ts) :
    shuffleEntry ts s mask t = some (t, values (chosen t)) := by
  apply shuffle_entry_with_eval ts bound covers mask (mask : Int) (by omega) chosen
    (by simpa only [Int.toNat_ofNat] using selects) s values
    (fun u => eval_const_mask s u mask hm) hr t ht

theorem shuffle_values_raw (ts : List Nat) (hlen : ts.length = 64)
    (hhead : ts.head? = some 0) (bound : ∀ t ∈ ts, t < 64) (covers : ∀ t, t < 64 → t ∈ ts)
    (p : List Instr) (s : State α) (mask : Nat) (hm : mask ≤ 32) (chosen : Nat → Nat)
    (selects : ∀ t, t < 64 → sourceLane .xor 64 t mask = some (chosen t) ∧ chosen t < 64)
    (values : Nat → α)
    (hc : p[s.pc 0]? = some (.shuffle .xor 1 0 (.const (mask : Int)) 64))
    (hr : ∀ t, t < 64 → s.regs t 0 = some (values t)) :
    shuffleValues geometry p ts s =
      some (1, ts.map (fun t => (t, values (chosen t)))) := by
  rewrite [Gather.values_eq geometry p ts s 0 .xor 1 0 (.const (mask : Int)) 64
    (by simp [geometry, Transfer.geometry, hlen]) hhead hc]
  have he := Transfer.mapM_some ts (shuffleEntry ts s mask)
    (fun t => (t, values (chosen t))) (shuffle_entry ts bound covers mask hm chosen selects s values hr)
  dsimp only [shuffleEntry] at he
  rewrite [he]
  rfl


theorem shuffle_values_at (n : Nat) (hn : n < 6) (s : State α) (values : Nat → α)
    (hp : s.pc 0 = 2 + 2 * n)
    (hr : ∀ t, t < 64 → s.regs t 0 = some (values t)) :
    shuffleValues geometry program (List.range 64) s =
      some (1, (List.range 64).map (fun t => (t, values (Nat.xor t (distance n))))) := by
  apply shuffle_values_raw (List.range 64) (by decide) (by decide)
    (fun t ht => List.mem_range.mp ht) (fun t ht => List.mem_range.mpr ht)
    program s (distance n) (distance_bound n hn).2
    (fun t => Nat.xor t (distance n)) (fun t ht => selected n t hn ht) values _ hr
  rewrite [hp]
  exact program_shuffle n hn


theorem shuffle_values (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n : Nat) (hn : n < 6) :
    shuffleValues geometry program (List.range 64) (phaseState ops input outside n) =
      some (1, (List.range 64).map (fun t => (t, value ops input n (Nat.xor t (distance n))))) := by
  exact shuffle_values_at n hn (phaseState ops input outside n) (value ops input n)
    (by simp [phase_pc]) (fun t ht => phase_regs ops input outside n t ht)

theorem shuffle_eq (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n : Nat) (hn : n < 6) :
    runShuffle geometry program (List.range 64) (phaseState ops input outside n) =
      some (shuffled ops input outside n) := by
  simp only [runShuffle, shuffle_values ops input outside n hn,
    bind, pure, Option.bind, shuffled]

theorem shuffled_pc (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n t : Nat) :
    (shuffled ops input outside n).pc t = if t < 64 then 3 + 2 * n else 0 := by
  by_cases ht : t < 64 <;>
    simp [shuffled, shuffleUpdates, Transfer.any_map_range, phase_pc, ht] <;> omega

theorem shuffled_regs_zero (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n t : Nat) (ht : t < 64) :
    (shuffled ops input outside n).regs t 0 = some (value ops input n t) := by
  simp [shuffled, shuffleUpdates, phase_regs, ht]

theorem shuffled_regs_one (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (n t : Nat) (ht : t < 64) :
    (shuffled ops input outside n).regs t 1 =
      some (value ops input n (Nat.xor t (distance n))) := by
  simp only [shuffled, shuffleUpdates, ↓reduceIte]
  rewrite [Transfer.lookup_map _ _ t (List.mem_range.mpr ht)]
  rfl

end LarkCollective.WaveSum
