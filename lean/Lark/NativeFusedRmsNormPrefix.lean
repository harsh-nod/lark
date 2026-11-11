import Lark.NativeFusedRmsNormRound

/-! Actual scalar prefix of the fixed native in-place source. This is the
210-instruction per-lane execution up to the first logical-width-32 shuffle,
not a whole-launch correctness or floating-point equivalence theorem.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def beforeShuffle (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  let row := t / 1024
  let tid := t % 1024
  let zero := ops.literal 0 1
  let s := roundAfter ops input row tid 0 t zero (initialized ops t s)
  roundAfter ops input row tid 1 t (folded ops input row tid 0 0 8 zero) s

def prefixState (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  advance (beforeShuffle ops input t s) t 23

theorem initialized_ready (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (pending : Pending input (t / 1024) (t % 1024) 0 s)
    (good : ∀ a ∈ s.trace, Good a) :
    StartReady ops input (t / 1024) (t % 1024) 0 t (ops.literal 0 1) (initialized ops t s) := by
  obtain ⟨hp, h0, h1, h4, ha⟩ := initialized_fields ops t s
  exact {
    pc := hp, rowIndex := h0, tidIndex := h1, iterationIndex := h4, accumulator := ha
    pending := pending
    completed := by intro j hj; omega
    good := good }

theorem before_shuffle_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (_ht : t < p.rows * 1024)
    (pending : Pending input (t / 1024) (t % 1024) 0 s)
    (good : ∀ a ∈ s.trace, Good a) :
    StartReady ops input (t / 1024) (t % 1024) 2 t
      (threadSum ops input (t / 1024) (t % 1024)) (beforeShuffle ops input t s) := by
  have htid : t % 1024 < 1024 := Nat.mod_lt _ (by decide)
  have he : t = t / 1024 * 1024 + t % 1024 := by omega
  have first := round_ready p ops input (t / 1024) (t % 1024) 0 t (ops.literal 0 1)
    (initialized ops t s) htid (by decide) he (initialized_ready ops input t s pending good)
  exact round_ready p ops input (t / 1024) (t % 1024) 1 t _ _ htid (by decide) he first

theorem prefix_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.rows * 1024) (hp : s.pc t = 0)
    (pending : Pending input (t / 1024) (t % 1024) 0 s)
    (good : ∀ a ∈ s.trace, Good a) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 210) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (prefixState ops input t s) := by
  have hr : t / 1024 < p.rows := by omega
  have htid : t % 1024 < 1024 := Nat.mod_lt _ (by decide)
  have he : t = t / 1024 * 1024 + t % 1024 := by omega
  let s0 := initialized ops t s
  let acc0 := ops.literal 0 1
  let acc1 := folded ops input (t / 1024) (t % 1024) 0 0 8 acc0
  let s1 := roundAfter ops input (t / 1024) (t % 1024) 0 t acc0 s0
  let s2 := roundAfter ops input (t / 1024) (t % 1024) 1 t acc1 s1
  have r0 := initialized_ready ops input t s pending good
  have r1 := round_ready p ops input (t / 1024) (t % 1024) 0 t acc0 s0 htid (by decide) he r0
  have r2 := before_shuffle_ready p ops input t s ht pending good
  rewrite [show extra + 210 = (extra + 203) + 7 by omega,
    initialized_eq p ops t (extra + 203) s ht hp]
  rewrite [show extra + 203 = (extra + 102) + 101 by omega,
    round_eq p ops input (t / 1024) (t % 1024) 0 t (extra + 102) acc0 s0
      hr htid (by decide) he r0]
  rewrite [show extra + 102 = (extra + 1) + 101 by omega,
    round_eq p ops input (t / 1024) (t % 1024) 1 t (extra + 1) acc1 s1
      hr htid (by decide) he r1]
  exact exit_rounds_eq p ops t extra s2 r2.pc r2.iterationIndex

theorem prefix_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prefixState ops input t s).pc t = 23 := by simp [prefixState, advance]

theorem prefix_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (ht : t < p.rows * 1024) (hp : s.pc t = 0)
    (pending : Pending input (t / 1024) (t % 1024) 0 s)
    (good : ∀ a ∈ s.trace, Good a) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s =
      some (prefixState ops input t s) := by
  have parked : LarkCollective.parked program (prefixState ops input t s) t = some .shuffle := by
    simp only [LarkCollective.parked, prefix_pc]
    rfl
  change LarkCollective.runLane ops (layout p) (geometry p) program t (302 + 210) s = _
  rewrite [prefix_eq p ops input t 302 s ht hp pending good]
  simp only [LarkCollective.runLane, parked]

theorem prefix_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (ht : t < p.rows * 1024)
    (pending : Pending input (t / 1024) (t % 1024) 0 s)
    (good : ∀ a ∈ s.trace, Good a) :
    (prefixState ops input t s).regs t 0 = some (threadSum ops input (t / 1024) (t % 1024)) ∧
    Pending input (t / 1024) (t % 1024) 16 (prefixState ops input t s) ∧
    Completed ops input (t / 1024) (t % 1024) t 16 (prefixState ops input t s) := by
  have ready := before_shuffle_ready p ops input t s ht pending good
  exact ⟨ready.accumulator, ready.pending, ready.completed⟩

theorem prefix_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (ht : t < p.rows * 1024)
    (pending : Pending input (t / 1024) (t % 1024) 0 s)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (prefixState ops input t s).trace, Good a :=
  (before_shuffle_ready p ops input t s ht pending good).good

theorem prefix_trace_length (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prefixState ops input t s).trace.length = s.trace.length + 64 := by
  change (beforeShuffle ops input t s).trace.length = _
  simp only [beforeShuffle, round_trace_length, initialized_preserves ops t s |>.2.1]

theorem initial_prefix_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane (initial p input outside) =
      some (prefixState ops input t (initial p input outside)) :=
  prefix_run p ops input t _ ht rfl
    (initial_pending p input outside (t / 1024) (t % 1024) (by omega) (Nat.mod_lt _ (by decide)))
    (by intro a ha; cases ha)

theorem initial_prefix_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    (prefixState ops input t (initial p input outside)).regs t 0 =
      some (threadSum ops input (t / 1024) (t % 1024)) ∧
    Pending input (t / 1024) (t % 1024) 16 (prefixState ops input t (initial p input outside)) ∧
    Completed ops input (t / 1024) (t % 1024) t 16 (prefixState ops input t (initial p input outside)) :=
  prefix_values p ops input t _ ht
    (initial_pending p input outside (t / 1024) (t % 1024) (by omega) (Nat.mod_lt _ (by decide)))
    (by intro a ha; cases ha)

theorem initial_prefix_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    ∀ a ∈ (prefixState ops input t (initial p input outside)).trace, Good a :=
  prefix_good p ops input t _ ht
    (initial_pending p input outside (t / 1024) (t % 1024) (by omega) (Nat.mod_lt _ (by decide)))
    (by intro a ha; cases ha)

theorem initial_prefix_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) (ht : t < p.rows * 1024) :
    raceFree (geometry p) (prefixState ops input t (initial p input outside)).trace = true :=
  race_free p _ (initial_prefix_good p ops input outside t ht)

theorem initial_prefix_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    (prefixState ops input t (initial p input outside)).trace.length = 64 :=
  prefix_trace_length ops input t (initial p input outside)

#print axioms initialized_ready
#print axioms before_shuffle_ready
#print axioms prefix_eq
#print axioms prefix_pc
#print axioms prefix_run
#print axioms prefix_values
#print axioms prefix_good
#print axioms prefix_trace_length
#print axioms initial_prefix_run
#print axioms initial_prefix_values
#print axioms initial_prefix_good
#print axioms initial_prefix_race_free
#print axioms initial_prefix_trace_length
end LarkNativeFusedRmsNorm
