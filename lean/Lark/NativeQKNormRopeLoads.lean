import Lark.NativeQKNormRopeLoad

/-! Composition of all four native input loads, with values and exact frames. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def fourLoads (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  loadAt ops input t 3 (loadAt ops input t 2 (loadAt ops input t 1 (loadAt ops input t 0 s)))

theorem four_loads_eq (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.rows * 1280) (hp : s.pc t = 7)
    (h5 : s.indices t 5 = some ((inputAddress t 0 : Nat) : Int)) (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 8) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (fourLoads ops input t s) := by
  let s1 := loadAt ops input t 0 s
  let s2 := loadAt ops input t 1 s1
  let s3 := loadAt ops input t 2 s2
  rewrite [show extra + 8 = (extra + 6) + 2 by omega,
    load_at_eq p neox ops input t 0 (extra + 6) s ht (by decide) hp h5 hr]
  change LarkCollective.runLane _ _ _ _ _ (extra + 6) s1 = _
  have h5a : s1.indices t 5 = some ((inputAddress t 0 : Nat) : Int) := by rw [load_at_base]; exact h5
  rewrite [show extra + 6 = (extra + 4) + 2 by omega,
    load_at_eq p neox ops input t 1 (extra + 4) s1 ht (by decide)
      (by simp [s1, load_at_pc]) h5a (load_at_reads p ops input t 0 s hr)]
  change LarkCollective.runLane _ _ _ _ _ (extra + 4) s2 = _
  have h5b : s2.indices t 5 = some ((inputAddress t 0 : Nat) : Int) := by rw [load_at_base]; exact h5a
  have hr2 := load_at_reads p ops input t 1 s1 (load_at_reads p ops input t 0 s hr)
  rewrite [show extra + 4 = (extra + 2) + 2 by omega,
    load_at_eq p neox ops input t 2 (extra + 2) s2 ht (by decide)
      (by simp [s2, load_at_pc]) h5b hr2]
  change LarkCollective.runLane _ _ _ _ _ (extra + 2) s3 = _
  have h5c : s3.indices t 5 = some ((inputAddress t 0 : Nat) : Int) := by rw [load_at_base]; exact h5b
  rewrite [load_at_eq p neox ops input t 3 extra s3 ht (by decide)
    (by simp [s3, load_at_pc]) h5c (load_at_reads p ops input t 2 s2 hr2)]
  rfl

theorem four_loads_pc (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (fourLoads ops input t s).pc t = 15 := by simp [fourLoads, load_at_pc]

theorem four_loads_values (ops : Ops α) (input : Nat → Nat → α) (t e : Nat)
    (s : State α) (he : e < 4) :
    (fourLoads ops input t s).regs t e = some (inputValue ops input t e) := by
  have hc : e = 0 ∨ e = 1 ∨ e = 2 ∨ e = 3 := by omega
  rcases hc with rfl | rfl | rfl | rfl <;>
    simp [fourLoads, loadAt, loaded, setIndex, setReg, record, advance, inputValue]

theorem load_at_low_indices (ops : Ops α) (input : Nat → Nat → α) (t e r : Nat)
    (s : State α) (hr : r < 7) : (loadAt ops input t e s).indices t r = s.indices t r := by
  have hn : ¬ r = 7 + e := by omega
  simp [loadAt, loaded, setIndex, setReg, record, advance, hn]

theorem four_loads_low_indices (ops : Ops α) (input : Nat → Nat → α) (t r : Nat)
    (s : State α) (hr : r < 7) : (fourLoads ops input t s).indices t r = s.indices t r := by
  unfold fourLoads
  repeat rw [load_at_low_indices ops input t _ r _ hr]

theorem four_loads_preserves (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (fourLoads ops input t s).memory = s.memory ∧
    (fourLoads ops input t s).epochs = s.epochs := ⟨rfl, rfl⟩

theorem four_loads_trace (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (fourLoads ops input t s).trace =
      [⟨t, globalCell 1 (inputAddress t 3), false, s.epochs t⟩,
       ⟨t, globalCell 1 (inputAddress t 2), false, s.epochs t⟩,
       ⟨t, globalCell 1 (inputAddress t 1), false, s.epochs t⟩,
       ⟨t, globalCell 1 (inputAddress t 0), false, s.epochs t⟩] ++ s.trace := rfl

theorem four_loads_other (ops : Ops α) (input : Nat → Nat → α) (t u : Nat) (s : State α)
    (hu : u ≠ t) : (fourLoads ops input t s).pc u = s.pc u ∧
      (fourLoads ops input t s).indices u = s.indices u ∧
      (fourLoads ops input t s).regs u = s.regs u := by
  refine ⟨?_, ?_, ?_⟩
  · simp [fourLoads, loadAt, loaded, setIndex, setReg, record, advance, hu]
  · funext r
    simp [fourLoads, loadAt, loaded, setIndex, setReg, record, advance, hu]
  · funext r
    simp [fourLoads, loadAt, loaded, setIndex, setReg, record, advance, hu]

theorem four_loads_good (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (good : ∀ a ∈ s.trace, Good a) : ∀ a ∈ (fourLoads ops input t s).trace, Good a := by
  unfold fourLoads
  apply load_at_good
  apply load_at_good
  apply load_at_good
  exact load_at_good ops input t 0 s good

def loadedPrefix (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  fourLoads ops input t (indexed t s)

theorem loaded_prefix_eq (p : Shape) (neox : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.rows * 1280) (hp : s.pc t = 0)
    (hr : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 15) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (loadedPrefix ops input t s) := by
  rewrite [show extra + 15 = (extra + 8) + 7 by omega, indexed_eq p neox ops t (extra + 8) s ht hp]
  rewrite [four_loads_eq p neox ops input t extra (indexed t s) ht
    (indexed_ready t s).pc (indexed_ready t s).inputBaseIx hr]
  rfl

#print axioms four_loads_eq
#print axioms four_loads_pc
#print axioms four_loads_values
#print axioms load_at_low_indices
#print axioms four_loads_low_indices
#print axioms four_loads_preserves
#print axioms four_loads_trace
#print axioms four_loads_other
#print axioms four_loads_good
#print axioms loaded_prefix_eq
end LarkNativeQKNormRope
