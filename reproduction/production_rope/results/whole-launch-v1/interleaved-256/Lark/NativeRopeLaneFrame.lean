import Lark.NativeRopeLane

/-! Every native lane's ten output cells, outside-memory frame and complete
30-access trace. Ownership comes from the source's pair/thread coordinates. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def Owns (neox : Bool) (t : Nat) (l : Location) : Prop :=
  l.space = .global ∧ l.owner = 0 ∧ (l.buffer = 0 ∨ l.buffer = 1) ∧ writer l.buffer l.offset neox = t

def LaneValues (ops : Ops α) (input : Nat → Nat → α) (neox : Bool) (row tid : Nat) (s : State α) : Prop :=
  (∀ j, j < 4 → ∀ imaginary : Bool,
    s.memory (globalCell 0 (address 0 row (tid + j * 512) neox imaginary)) =
      some (rotated ops input 0 row (tid + j * 512) neox imaginary)) ∧
  (∀ imaginary : Bool, s.memory (globalCell 1 (address 1 row tid neox imaginary)) =
      some (rotated ops input 1 row tid neox imaginary))

theorem native_address_owned (neox : Bool) (buffer row tid iteration t : Nat) (imaginary : Bool)
    (ht : tid < 512) (hb : buffer = 0 ∨ buffer = 1)
    (hi : iteration < (if buffer = 0 then 4 else 1)) (hthread : t = row * 512 + tid) :
    Owns neox t (globalCell buffer (address buffer row (tid + iteration * 512) neox imaginary)) := by
  refine ⟨rfl, rfl, hb, ?_⟩
  change writer buffer (address buffer row (tid + iteration * 512) neox imaginary) neox = t
  rw [native_writer buffer row tid iteration neox imaginary ht hi]
  exact hthread.symm

theorem ownership_unique (neox : Bool) (t u : Nat) (l : Location)
    (ht : Owns neox t l) (hu : Owns neox u l) : t = u := ht.2.2.2.symm.trans hu.2.2.2

theorem lane_query_values (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t j : Nat) (s : State α) (imaginary : Bool) (hj : j < 4) :
    (laneFinished ops input neox row tid t s).memory
        (globalCell 0 (address 0 row (tid + j * 512) neox imaginary)) =
      some (rotated ops input 0 row (tid + j * 512) neox imaginary) := by
  change (keyRound ops input neox row tid t (laneKeyStart ops input neox row tid t s)).memory
    (globalCell 0 (address 0 row (tid + j * 512) neox imaginary)) = _
  rw [key_round_memory_frame]
  · exact query_sequence_value ops input neox row tid t 4 j (laneStarted row tid t s) imaginary hj
  all_goals
    intro he
    have hbad : (0 : Nat) = 1 := congrArg Location.buffer he
    omega

theorem lane_key_values (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) (imaginary : Bool) :
    (laneFinished ops input neox row tid t s).memory (globalCell 1 (address 1 row tid neox imaginary)) =
      some (rotated ops input 1 row tid neox imaginary) := by
  cases imaginary
  · exact (key_round_values ops input neox row tid t (laneKeyStart ops input neox row tid t s)).1
  · exact (key_round_values ops input neox row tid t (laneKeyStart ops input neox row tid t s)).2

theorem lane_values (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) : LaneValues ops input neox row tid (laneFinished ops input neox row tid t s) :=
  ⟨fun j hj imaginary => lane_query_values ops input neox row tid t j s imaginary hj,
   fun imaginary => lane_key_values ops input neox row tid t s imaginary⟩

theorem lane_memory_frame (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) (ht : tid < 512) (hthread : t = row * 512 + tid)
    (l : Location) (outside : ¬ Owns neox t l) :
    (laneFinished ops input neox row tid t s).memory l = s.memory l := by
  have hq : ∀ j, j < 4 → ∀ imaginary : Bool,
      l ≠ globalCell 0 (address 0 row (tid + j * 512) neox imaginary) := by
    intro j hj imaginary he
    apply outside
    rw [he]
    exact native_address_owned neox 0 row tid j t imaginary ht (Or.inl rfl) hj hthread
  have hk : ∀ imaginary : Bool, l ≠ globalCell 1 (address 1 row tid neox imaginary) := by
    intro imaginary he
    apply outside
    rw [he]
    exact native_address_owned neox 1 row tid 0 t imaginary ht (Or.inr rfl) (by decide) hthread
  change (keyRound ops input neox row tid t (laneKeyStart ops input neox row tid t s)).memory l = _
  rw [key_round_memory_frame ops input neox row tid t _ l (hk false) (hk true)]
  exact query_sequence_memory_frame ops input neox row tid t 4 (laneStarted row tid t s) l hq

theorem lane_cache_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) (ht : tid < 512) (hthread : t = row * 512 + tid)
    (hc : CacheReads p input s) : CacheReads p input (laneFinished ops input neox row tid t s) := by
  intro offset hoffset
  rw [lane_memory_frame ops input neox row tid t s ht hthread]
  · exact hc offset hoffset
  · intro ho
    have hb : (2 : Nat) = 0 ∨ 2 = 1 := ho.2.2.1
    omega

theorem lane_other_pc (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t u : Nat) (s : State α) (hu : u ≠ t) :
    (laneFinished ops input neox row tid t s).pc u = s.pc u := by
  calc
    _ = (laneKeyDone ops input neox row tid t s).pc u := by simp [laneFinished, advance, hu]
    _ = (laneKeyStart ops input neox row tid t s).pc u :=
      key_round_other_pc ops input neox row tid t u _ hu
    _ = (laneQueries ops input neox row tid t s).pc u := by
      simp [laneKeyStart, beginKey, setIndex, LarkReduction.setIndex, advance, hu]
    _ = (laneStarted row tid t s).pc u := query_sequence_other_pc ops input neox row tid t 4 u _ hu
    _ = s.pc u := by simp [laneStarted, setIndex, LarkReduction.setIndex, advance, hu]

theorem lane_epochs (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) : (laneFinished ops input neox row tid t s).epochs = s.epochs := by
  change (keyRound ops input neox row tid t (laneKeyStart ops input neox row tid t s)).epochs = s.epochs
  rw [key_round_epochs]
  exact query_sequence_epochs ops input neox row tid t 4 (laneStarted row tid t s)

theorem lane_trace_length (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) : (laneFinished ops input neox row tid t s).trace.length = s.trace.length + 30 := by
  change (keyRound ops input neox row tid t (laneKeyStart ops input neox row tid t s)).trace.length = _
  rw [key_round_trace_length]
  change (querySequence ops input neox row tid t 4 (laneStarted row tid t s)).trace.length + 6 = s.trace.length + 30
  simp only [query_sequence_trace_length]
  rfl

theorem lane_halt (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) : (laneFinished ops input neox row tid t s).pc t = 49 := by
  simp [laneFinished, advance]

theorem lane_good (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row tid t : Nat) (s : State α) (ht : tid < 512) (hthread : t = row * 512 + tid)
    (old : ∀ a ∈ s.trace, Good neox a) :
    ∀ a ∈ (laneFinished ops input neox row tid t s).trace, Good neox a := by
  have hq := query_sequence_good ops input neox row tid t (laneStarted row tid t s) ht hthread old 4 (by decide)
  have ha : writer 1 (address 1 row tid neox false) neox = t := by
    simpa [hthread] using native_writer 1 row tid 0 neox false ht (by decide)
  have hb : writer 1 (address 1 row tid neox true) neox = t := by
    simpa [hthread] using native_writer 1 row tid 0 neox true ht (by decide)
  exact key_round_good neox ops input row tid t (laneKeyStart ops input neox row tid t s) ha hb hq

#print axioms native_address_owned
#print axioms ownership_unique
#print axioms lane_query_values
#print axioms lane_key_values
#print axioms lane_values
#print axioms lane_memory_frame
#print axioms lane_cache_reads
#print axioms lane_other_pc
#print axioms lane_epochs
#print axioms lane_trace_length
#print axioms lane_halt
#print axioms lane_good
end LarkNativeRope
