import Lark.NativeRopeLaneFrame
import Lark.ScalarLaunch

/-! Native scheduler invariant. Pending lanes retain their original owned
input cells; halted lanes retain all their outputs. Actual source execution
preserves both classes and derives trace classification from initialization. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def Pending (input : Nat → Nat → α) (neox : Bool) (t : Nat) (s : State α) : Prop :=
  QueryInputs input neox (t / 512) (t % 512) s ∧ KeyInputs input neox (t / 512) (t % 512) s
def Completed (ops : Ops α) (input : Nat → Nat → α) (neox : Bool) (t : Nat) (s : State α) : Prop :=
  LaneValues ops input neox (t / 512) (t % 512) s

structure Invariant (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α) (s : State α) : Prop where
  control : ∀ t, t < p.rows * 512 → s.pc t = 0 ∨ s.pc t = 49
  cache : CacheReads p input s
  pending : ∀ t, t < p.rows * 512 → s.pc t = 0 → Pending input neox t s
  completed : ∀ t, t < p.rows * 512 → s.pc t = 49 → Completed ops input neox t s
  good : ∀ a ∈ s.trace, Good neox a

def post (ops : Ops α) (input : Nat → Nat → α) (neox : Bool) (s : State α) (t : Nat) : State α :=
  if s.pc t = 49 then s else laneFinished ops input neox (t / 512) (t % 512) t s

theorem valid_thread (p : Shape) (t : Nat) (ht : t < p.rows * 512) :
    t / 512 < p.rows ∧ t % 512 < 512 ∧ t = t / 512 * 512 + t % 512 := by omega

theorem pending_frame (input : Nat → Nat → α) (neox : Bool) (t : Nat) (s next : State α)
    (frame : ∀ l, Owns neox t l → next.memory l = s.memory l) (old : Pending input neox t s) :
    Pending input neox t next := by
  have ht : t % 512 < 512 := Nat.mod_lt _ (by decide)
  have hthread : t = t / 512 * 512 + t % 512 := by omega
  constructor
  · intro j hj imaginary
    rw [frame _ (native_address_owned neox 0 (t / 512) (t % 512) j t imaginary ht (Or.inl rfl) hj hthread)]
    exact old.1 j hj imaginary
  · intro imaginary
    have ho : Owns neox t (globalCell 1 (address 1 (t / 512) (t % 512) neox imaginary)) := by
      simpa using native_address_owned neox 1 (t / 512) (t % 512) 0 t imaginary ht (Or.inr rfl) (by decide) hthread
    rw [frame _ ho]
    exact old.2 imaginary

theorem completed_frame (ops : Ops α) (input : Nat → Nat → α) (neox : Bool) (t : Nat) (s next : State α)
    (frame : ∀ l, Owns neox t l → next.memory l = s.memory l) (old : Completed ops input neox t s) :
    Completed ops input neox t next := by
  have ht : t % 512 < 512 := Nat.mod_lt _ (by decide)
  have hthread : t = t / 512 * 512 + t % 512 := by omega
  constructor
  · intro j hj imaginary
    rw [frame _ (native_address_owned neox 0 (t / 512) (t % 512) j t imaginary ht (Or.inl rfl) hj hthread)]
    exact old.1 j hj imaginary
  · intro imaginary
    have ho : Owns neox t (globalCell 1 (address 1 (t / 512) (t % 512) neox imaginary)) := by
      simpa using native_address_owned neox 1 (t / 512) (t % 512) 0 t imaginary ht (Or.inr rfl) (by decide) hthread
    rw [frame _ ho]
    exact old.2 imaginary

theorem initial_invariant (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) : Invariant p neox ops input (initial p input outside) := by
  constructor
  · intro t ht
    exact Or.inl rfl
  · intro offset hoffset
    exact initial_cache p input outside offset hoffset
  · intro t ht hpc
    have co := valid_thread p t ht
    constructor
    · intro j hj imaginary
      exact initial_query p input outside _
        (address_bound p 0 (t / 512) (t % 512 + j * 512) neox imaginary co.1
          (native_pair_bound 0 (t % 512) j co.2.1 hj))
    · intro imaginary
      exact initial_key p input outside _
        (address_bound p 1 (t / 512) (t % 512) neox imaginary co.1 co.2.1)
  · intro t ht hpc
    have hzero : (initial p input outside).pc t = 0 := rfl
    omega
  · intro a hm
    simp [initial, LarkInOut.initial, LarkNonlinear.initial] at hm

theorem finished_invariant (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (ht : t < p.rows * 512) (hp : s.pc t = 0)
    (old : Invariant p neox ops input s) :
    Invariant p neox ops input (laneFinished ops input neox (t / 512) (t % 512) t s) := by
  let final := laneFinished ops input neox (t / 512) (t % 512) t s
  have co := valid_thread p t ht
  have stop : final.pc t = 49 := lane_halt ops input neox _ _ _ _
  have pcOther : ∀ u, u ≠ t → final.pc u = s.pc u :=
    fun u hu => lane_other_pc ops input neox _ _ t u s hu
  have memoryOther : ∀ u, u ≠ t → ∀ l, Owns neox u l → final.memory l = s.memory l := by
    intro u hu l hl
    apply lane_memory_frame ops input neox _ _ t s co.2.1 co.2.2 l
    intro own
    exact hu (ownership_unique neox u t l hl own)
  change Invariant p neox ops input final
  constructor
  · intro u hu
    by_cases he : u = t
    · subst u
      exact Or.inr stop
    · rw [pcOther u he]
      exact old.control u hu
  · exact lane_cache_reads p ops input neox _ _ t s co.2.1 co.2.2 old.cache
  · intro u hu hzero
    have he : u ≠ t := by intro he; subst u; omega
    have hbefore : s.pc u = 0 := by simpa only [pcOther u he] using hzero
    exact pending_frame input neox u s final (memoryOther u he) (old.pending u hu hbefore)
  · intro u hu hhalt
    by_cases he : u = t
    · subst u
      exact lane_values ops input neox _ _ t s
    · have hbefore : s.pc u = 49 := by simpa only [pcOther u he] using hhalt
      exact completed_frame ops input neox u s final (memoryOther u he) (old.completed u hu hbefore)
  · exact lane_good ops input neox _ _ t s co.2.1 co.2.2 old.good

theorem lane_contract (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α) :
    LarkScalarLaunch.LaneContract ops (layout p) (geometry p) 256 49 (program neox)
      (post ops input neox) (Invariant p neox ops input) := by
  intro s hs t ht
  have ht' : t < p.rows * 512 := ht
  by_cases hd : s.pc t = 49
  · simp only [post, if_pos hd]
    exact ⟨halted_lane p neox ops t 255 s hd, hs, hd, by intro u hu; exact hu⟩
  · have hzero : s.pc t = 0 := by
      rcases hs.control t ht' with hz | hh
      · exact hz
      · exact False.elim (hd hh)
    have co := valid_thread p t ht'
    have inputs := hs.pending t ht' hzero
    simp only [post, if_neg hd]
    refine ⟨lane_execution p neox ops input _ _ t s co.1 co.2.1 co.2.2 hzero hs.cache inputs.1 inputs.2,
      finished_invariant p neox ops input t s ht' hzero hs, lane_halt ops input neox _ _ t s, ?_⟩
    intro u hu
    by_cases he : u = t
    · subst u
      omega
    · rw [lane_other_pc ops input neox _ _ t u s he]
      exact hu

#print axioms valid_thread
#print axioms pending_frame
#print axioms completed_frame
#print axioms initial_invariant
#print axioms finished_invariant
#print axioms lane_contract
end LarkNativeRope
