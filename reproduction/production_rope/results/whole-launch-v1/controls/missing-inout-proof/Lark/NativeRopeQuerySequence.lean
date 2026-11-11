import Lark.NativeRopeRoundFrame

/-! All four source-ordered query rounds, retaining every pending original
pair and the gathered cache. Actual lane execution is composed without changing
the source fuel or assuming arithmetic laws. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def querySequence (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) : Nat → State α → State α
  | 0, s => s
  | n + 1, s => queryRound ops input neox row (tid + n * 512) t
      (querySequence ops input neox row tid t n s)

def CacheReads (p : Shape) (input : Nat → Nat → α) (s : State α) : Prop :=
  ∀ offset, offset < p.rows * 128 → s.memory (globalCell 2 offset) = some (input 2 offset)

def QueryInputs (input : Nat → Nat → α) (neox : Bool) (row tid : Nat) (s : State α) : Prop :=
  ∀ j, j < 4 → ∀ imaginary : Bool,
    s.memory (globalCell 0 (address 0 row (tid + j * 512) neox imaginary)) =
      some (input 0 (address 0 row (tid + j * 512) neox imaginary))

theorem query_sequence_ready (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t n : Nat) (s : State α) (hp : s.pc t = 2)
    (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 1 = some (tid : Int)) :
    (querySequence ops input neox row tid t n s).pc t = 2 ∧
    (querySequence ops input neox row tid t n s).indices t 0 = some (row : Int) ∧
    (querySequence ops input neox row tid t n s).indices t 1 = some ((tid + n * 512 : Nat) : Int) := by
  induction n with
  | zero => simpa [querySequence] using And.intro hp (And.intro h0 h1)
  | succ n ih =>
    have h := query_round_ready ops input neox row (tid + n * 512) t
      (querySequence ops input neox row tid t n s) ih.2.1
    simpa [querySequence, Nat.add_mul, Nat.add_assoc] using h

theorem query_sequence_memory_frame (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t n : Nat) (s : State α) (l : Location)
    (outside : ∀ j, j < n → ∀ imaginary : Bool,
      l ≠ globalCell 0 (address 0 row (tid + j * 512) neox imaginary)) :
    (querySequence ops input neox row tid t n s).memory l = s.memory l := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change (queryRound ops input neox row (tid + n * 512) t
      (querySequence ops input neox row tid t n s)).memory l = _
    rw [query_round_memory_frame ops input neox row (tid + n * 512) t _ l
      (outside n (by omega) false) (outside n (by omega) true)]
    exact ih (by intro j hj imaginary; exact outside j (by omega) imaginary)

theorem query_sequence_future_input (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t n j : Nat) (s : State α) (imaginary : Bool) (hj : n ≤ j) :
    (querySequence ops input neox row tid t n s).memory
        (globalCell 0 (address 0 row (tid + j * 512) neox imaginary)) =
      s.memory (globalCell 0 (address 0 row (tid + j * 512) neox imaginary)) := by
  apply query_sequence_memory_frame
  intro k hk other
  intro he
  have hc : address 0 row (tid + j * 512) neox imaginary =
      address 0 row (tid + k * 512) neox other := congrArg Location.offset he
  exact address_different_pairs 0 row _ _ neox imaginary other (by omega) hc

theorem query_sequence_other_buffer (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t n buffer offset : Nat) (s : State α) (hb : buffer ≠ 0) :
    (querySequence ops input neox row tid t n s).memory (globalCell buffer offset) =
      s.memory (globalCell buffer offset) := by
  apply query_sequence_memory_frame
  intro j hj imaginary he
  exact hb (congrArg Location.buffer he)

theorem query_sequence_epochs (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t n : Nat) (s : State α) : (querySequence ops input neox row tid t n s).epochs = s.epochs := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [querySequence, query_round_epochs] using ih

theorem query_sequence_other_pc (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t n u : Nat) (s : State α) (hu : u ≠ t) :
    (querySequence ops input neox row tid t n s).pc u = s.pc u := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [querySequence, query_round_other_pc ops input neox row _ t u _ hu] using ih

theorem query_sequence_trace_length (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t n : Nat) (s : State α) :
    (querySequence ops input neox row tid t n s).trace.length = s.trace.length + n * 6 := by
  induction n with
  | zero => simp [querySequence]
  | succ n ih => simp only [querySequence, query_round_trace_length, ih]; omega

theorem query_sequence_value (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t n j : Nat) (s : State α) (imaginary : Bool) (hj : j < n) :
    (querySequence ops input neox row tid t n s).memory
      (globalCell 0 (address 0 row (tid + j * 512) neox imaginary)) =
      some (rotated ops input 0 row (tid + j * 512) neox imaginary) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases he : j = n
    · subst j
      cases imaginary
      · exact (query_round_values ops input neox row (tid + n * 512) t _).1
      · exact (query_round_values ops input neox row (tid + n * 512) t _).2
    · change (queryRound ops input neox row (tid + n * 512) t
        (querySequence ops input neox row tid t n s)).memory _ = _
      rw [query_round_memory_frame]
      · exact ih (by omega)
      all_goals
        intro hloc
        have hc := congrArg Location.offset hloc
        exact address_different_pairs 0 row _ _ neox imaginary _ (by omega) hc

theorem query_sequence_good (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) (ht : tid < 512) (hthread : t = row * 512 + tid)
    (old : ∀ a ∈ s.trace, Good neox a) :
    ∀ n, n ≤ 4 → ∀ a ∈ (querySequence ops input neox row tid t n s).trace, Good neox a := by
  intro n
  induction n with
  | zero => intro hn; exact old
  | succ n ih =>
    intro hn
    apply query_round_good
    · rw [native_writer 0 row tid n neox false ht (by simp; omega), hthread]
    · rw [native_writer 0 row tid n neox true ht (by simp; omega), hthread]
    · exact ih (by omega)

theorem query_sequence_cycle (p : Shape) (neox : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row tid t : Nat) (s : State α) (hr : row < p.rows) (ht : tid < 512)
    (hp : s.pc t = 2) (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 1 = some (tid : Int))
    (hc : CacheReads p input s) (hq : QueryInputs input neox row tid s) :
    ∀ n, n ≤ 4 → ∀ extra,
      runLane ops (layout p) (geometry p) (program neox) t (extra + n * 23) s =
        runLane ops (layout p) (geometry p) (program neox) t extra
          (querySequence ops input neox row tid t n s) := by
  intro n
  induction n with
  | zero => intro hn extra; simp [querySequence]
  | succ n ih =>
    intro hn extra
    have hn4 : n < 4 := by omega
    have hi : tid + n * 512 < 2048 := by omega
    have ready := query_sequence_ready ops input neox row tid t n s hp h0 h1
    have hbounds := cache_bounds p row (tid + n * 512) hr
    have hcos : (querySequence ops input neox row tid t n s).memory (globalCell 2 (cacheCos row (tid + n * 512))) =
        some (input 2 (cacheCos row (tid + n * 512))) := by
      rw [query_sequence_other_buffer ops input neox row tid t n 2 _ s (by decide)]
      exact hc _ hbounds.1
    have hsin : (querySequence ops input neox row tid t n s).memory (globalCell 2 (cacheSin row (tid + n * 512))) =
        some (input 2 (cacheSin row (tid + n * 512))) := by
      rw [query_sequence_other_buffer ops input neox row tid t n 2 _ s (by decide)]
      exact hc _ hbounds.2
    have hx : (querySequence ops input neox row tid t n s).memory
        (globalCell 0 (address 0 row (tid + n * 512) neox false)) =
        some (input 0 (address 0 row (tid + n * 512) neox false)) := by
      rw [query_sequence_future_input ops input neox row tid t n n s false (by omega)]
      exact hq n hn4 false
    have hy : (querySequence ops input neox row tid t n s).memory
        (globalCell 0 (address 0 row (tid + n * 512) neox true)) =
        some (input 0 (address 0 row (tid + n * 512) neox true)) := by
      rw [query_sequence_future_input ops input neox row tid t n n s true (by omega)]
      exact hq n hn4 true
    rw [show extra + (n + 1) * 23 = (extra + 23) + n * 23 by omega, ih (by omega) (extra + 23)]
    exact query_round_cycle p neox ops input row (tid + n * 512) t extra
      (querySequence ops input neox row tid t n s) hr hi ready.1 ready.2.1 ready.2.2 hcos hsin hx hy

#print axioms query_sequence_ready
#print axioms query_sequence_memory_frame
#print axioms query_sequence_future_input
#print axioms query_sequence_other_buffer
#print axioms query_sequence_epochs
#print axioms query_sequence_other_pc
#print axioms query_sequence_trace_length
#print axioms query_sequence_value
#print axioms query_sequence_good
#print axioms query_sequence_cycle
end LarkNativeRope
