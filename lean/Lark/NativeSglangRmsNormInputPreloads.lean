import Lark.NativeSglangRmsNormCacheRound

/-! The source initializer and both input preload rounds, for arbitrary Ops.
This is a scalar prefix equation through PC16, before weight preloads. A complete
runLane success statement requires the later continuation to its first shuffle.+-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def inputPreloads (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  let row := t / 1024
  let tid := t % 1024
  let s := inputCacheRound input row tid 0 t (initialized t s)
  advance (inputCacheRound input row tid 1 t s) t 16

theorem initial_input_round_ready (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    InputRoundReady p input (t / 1024) (t % 1024) 0 t (initialized t (initial p input outside)) := by
  obtain ⟨hp,h0,h1,_,_,h4⟩ := initialized_fields t (initial p input outside)
  exact {
    pc := hp, rowIndex := h0, tidIndex := h1, iterationIndex := h4
    reads := initial_reads p input outside
    cached := by intro k hk; omega
    good := by intro a ha; cases ha }

theorem initial_input_preloads_eq (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (outside : Location → Option α)
    (t extra : Nat) (ht : t < p.rows * 1024) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t
      (extra + 128) (initial p input outside) =
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
      (inputPreloads input t (initial p input outside)) := by
  let row := t / 1024
  let tid := t % 1024
  let s0 := initialized t (initial p input outside)
  let s1 := inputCacheRound input row tid 0 t s0
  let s2 := inputCacheRound input row tid 1 t s1
  have hr : row < p.rows := by omega
  have htid : tid < 1024 := Nat.mod_lt _ (by decide)
  have r0 := initial_input_round_ready p input outside t
  have r1 := input_cache_round_ready p input row tid 0 t s0 r0
  have r2 := input_cache_round_ready p input row tid 1 t s1 r1
  have pred := LarkReduction.predicate_nlt_of (geometry p) t s2 (.ivar 4) (.const 2)
    2 2 r2.iterationIndex rfl (by decide)
  have he : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 4) (.const 2)) 16) s2 =
      some (advance s2 t 16) := by
    simp only [execute,pred,bind,pure,Option.bind]
    rfl
  rewrite [show extra + 128 = (extra + 123) + 5 by omega,
    initialized_eq p repaired ops t (extra + 123) (initial p input outside) ht rfl]
  rewrite [show extra + 123 = (extra + 62) + 61 by omega,
    input_cache_round_eq p repaired ops input row tid 0 t (extra + 62) s0 hr htid (by decide) r0]
  rewrite [show extra + 62 = (extra + 1) + 61 by omega,
    input_cache_round_eq p repaired ops input row tid 1 t (extra + 1) s1 hr htid (by decide) r1]
  exact scalar_step p repaired ops t 5 extra _ s2 _ (by cases repaired <;> decide) r2.pc he

theorem initial_input_preloads_values (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    InputPrefix input (t / 1024) (t % 1024) 16 t (inputPreloads input t (initial p input outside)) := by
  have r0 := initial_input_round_ready p input outside t
  have r1 := input_cache_round_ready p input (t / 1024) (t % 1024) 0 t _ r0
  have r2 := input_cache_round_ready p input (t / 1024) (t % 1024) 1 t _ r1
  exact r2.cached

theorem initial_input_preloads_reads (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    Reads p input (inputPreloads input t (initial p input outside)) := by
  have r0 := initial_input_round_ready p input outside t
  have r1 := input_cache_round_ready p input (t / 1024) (t % 1024) 0 t _ r0
  have r2 := input_cache_round_ready p input (t / 1024) (t % 1024) 1 t _ r1
  exact r2.reads

theorem initial_input_preloads_good (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    ∀ a ∈ (inputPreloads input t (initial p input outside)).trace, Good a := by
  have r0 := initial_input_round_ready p input outside t
  have r1 := input_cache_round_ready p input (t / 1024) (t % 1024) 0 t _ r0
  have r2 := input_cache_round_ready p input (t / 1024) (t % 1024) 1 t _ r1
  exact r2.good

theorem initial_input_preloads_race_free (p : Shape) (input : Nat → Nat → α)
    (outside : Location → Option α) (t : Nat) :
    raceFree (geometry p) (inputPreloads input t (initial p input outside)).trace = true :=
  race_free p _ (initial_input_preloads_good p input outside t)

theorem input_preloads_pc (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (inputPreloads input t s).pc t = 16 := by simp [inputPreloads,advance]

theorem input_preloads_epochs (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (inputPreloads input t s).epochs = s.epochs := by
  simp only [inputPreloads,advance,input_cache_round_epochs,initialized_preserves]

theorem input_preloads_trace_length (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (inputPreloads input t s).trace.length = s.trace.length + 32 := by
  simp only [inputPreloads,advance,input_cache_round_trace_length,initialized_preserves]

#print axioms initial_input_round_ready
#print axioms initial_input_preloads_eq
#print axioms initial_input_preloads_values
#print axioms initial_input_preloads_reads
#print axioms initial_input_preloads_good
#print axioms initial_input_preloads_race_free
#print axioms input_preloads_pc
#print axioms input_preloads_epochs
#print axioms input_preloads_trace_length
end LarkNativeSglangRmsNorm
