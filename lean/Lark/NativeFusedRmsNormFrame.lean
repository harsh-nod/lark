import Lark.NativeFusedRmsNormPrefix

/-! Frames for actual in-place prefix effects. Distinct threads own disjoint
residual/shared cells; every other cell and every other thread's controls remain
unchanged. This permits the scheduler's sequential fold without reseeding cells.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def Owns (t : Nat) (l : Location) : Prop :=
  (l.space = .global ∧ l.owner = 0 ∧ l.buffer = 1 ∧ writer l.offset = t) ∨
  (l.space = .shared ∧ l.owner = t / 1024 ∧ l.buffer = 1 ∧
    (l.offset / 8) % 1024 = t % 1024)

theorem owns_unique (t u : Nat) (l : Location) (ht : Owns t l) (hu : Owns u l) : t = u := by
  rcases ht with ht | ht <;> rcases hu with hu | hu
  all_goals simp_all
  omega

theorem slot_owner (tid ordinal : Nat) (ht : tid < 1024) (_ho : ordinal < 16) :
    (slot tid ordinal / 8) % 1024 = tid := by
  unfold slot column
  omega

theorem residual_owned (p : Shape) (t ordinal : Nat) (ho : ordinal < 16) :
    Owns t (globalCell 1 (flatAddress (t / 1024) (t % 1024) ordinal)) := by
  have hw := address_writer p (t / 1024) (t % 1024) (ordinal / 8) (ordinal % 8)
    (Nat.mod_lt _ (by decide)) (by omega) (Nat.mod_lt _ (by decide))
  apply Or.inl
  refine ⟨rfl, rfl, rfl, ?_⟩
  change writer (address (t / 1024) (column (t % 1024) (ordinal / 8) (ordinal % 8))) = t
  rewrite [hw]
  omega

theorem shared_owned (t ordinal : Nat) (ho : ordinal < 16) :
    Owns t (unroundedCell t (slot (t % 1024) ordinal)) :=
  Or.inr ⟨rfl, rfl, rfl, slot_owner _ _ (Nat.mod_lt _ (by decide)) ho⟩

theorem global_input_unowned (t buffer offset : Nat) (hb : buffer = 0 ∨ buffer = 2) :
    ¬ Owns t (globalCell buffer offset) := by
  rcases hb with rfl | rfl <;> simp [Owns, globalCell]

theorem component_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (acc : α) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8) (he : t = row * 1024 + tid)
    (l : Location) (hl : ¬ Owns t l) :
    (componentAfter ops input row tid iteration component t acc s).memory l = s.memory l := by
  have hw : Owns t (globalCell 1 (address row (column tid iteration component))) :=
    Or.inl ⟨rfl, rfl, rfl, (address_writer p row tid iteration component ht hi hc).trans he.symm⟩
  have hs : Owns t (unroundedCell t (column tid iteration component)) := by
    apply Or.inr
    refine ⟨rfl, rfl, rfl, ?_⟩
    change (column tid iteration component / 8) % 1024 = t % 1024
    unfold column
    omega
  have hnw : l ≠ globalCell 1 (address row (column tid iteration component)) := by
    intro eq; exact hl (eq ▸ hw)
  have hns : l ≠ unroundedCell t (column tid iteration component) := by
    intro eq; exact hl (eq ▸ hs)
  simp only [component_memory, if_neg hns, if_neg hnw]

theorem component_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    (componentAfter ops input row tid iteration component t acc s).pc u = s.pc u ∧
    (componentAfter ops input row tid iteration component t acc s).indices u = s.indices u ∧
    (componentAfter ops input row tid iteration component t acc s).regs u = s.regs u := by
  simp [componentAfter, setIndex, setReg, written, record, advance, hu]

theorem component_index_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t q : Nat) (acc : α) (s : State α)
    (h5 : q ≠ 5) (h6 : q ≠ 6) (h7 : q ≠ 7) :
    (componentAfter ops input row tid iteration component t acc s).indices t q = s.indices t q := by
  simp [componentAfter, setIndex, setReg, written, record, advance, h5, h6, h7]

theorem components_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (acc : α) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (he : t = row * 1024 + tid)
    (hcount : component + remaining ≤ 8) (l : Location) (hl : ¬ Owns t l) :
    (components ops input row tid iteration t component remaining acc s).memory l = s.memory l := by
  induction remaining generalizing component acc s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (component + 1) _ _ (by omega)).trans
        (component_frame p ops input row tid iteration component t acc s ht hi (by omega) he l hl)

theorem components_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    (components ops input row tid iteration t component remaining acc s).pc u = s.pc u ∧
    (components ops input row tid iteration t component remaining acc s).indices u = s.indices u ∧
    (components ops input row tid iteration t component remaining acc s).regs u = s.regs u := by
  induction remaining generalizing component acc s with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ remaining ih =>
      have h := ih (component + 1) (ops.add acc (squared ops input row tid iteration component))
        (componentAfter ops input row tid iteration component t acc s)
      have hc := component_other ops input row tid iteration component t u acc s hu
      exact ⟨h.1.trans hc.1, h.2.1.trans hc.2.1, h.2.2.trans hc.2.2⟩

theorem components_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (acc : α) (s : State α) :
    (components ops input row tid iteration t component remaining acc s).epochs = s.epochs := by
  induction remaining generalizing component acc s with
  | zero => rfl
  | succ remaining ih => exact ih (component + 1) _ _

theorem components_index_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t component remaining q : Nat) (acc : α) (s : State α)
    (h5 : q ≠ 5) (h6 : q ≠ 6) (h7 : q ≠ 7) :
    (components ops input row tid iteration t component remaining acc s).indices t q = s.indices t q := by
  induction remaining generalizing component acc s with
  | zero => rfl
  | succ remaining ih =>
      exact (ih (component + 1) _ _).trans
        (component_index_frame ops input row tid iteration component t q acc s h5 h6 h7)

theorem round_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (he : t = row * 1024 + tid)
    (l : Location) (hl : ¬ Owns t l) :
    (roundAfter ops input row tid iteration t acc s).memory l = s.memory l :=
  components_frame p ops input row tid iteration t 0 8 acc (beginRound t s) ht hi he (by decide) l hl

theorem round_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t u : Nat) (acc : α) (s : State α) (hu : u ≠ t) :
    (roundAfter ops input row tid iteration t acc s).pc u = s.pc u ∧
    (roundAfter ops input row tid iteration t acc s).indices u = s.indices u ∧
    (roundAfter ops input row tid iteration t acc s).regs u = s.regs u := by
  have h := components_other ops input row tid iteration t 0 8 u acc (beginRound t s) hu
  simpa only [roundAfter, endRound, beginRound, setIndex, advance, if_neg hu,
    hu, false_and, ↓reduceIte] using h

theorem round_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) :
    (roundAfter ops input row tid iteration t acc s).epochs = s.epochs :=
  components_epochs ops input row tid iteration t 0 8 acc (beginRound t s)

theorem round_index_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t q : Nat) (acc : α) (s : State α)
    (h4 : q ≠ 4) (h5 : q ≠ 5) (h6 : q ≠ 6) (h7 : q ≠ 7) :
    (roundAfter ops input row tid iteration t acc s).indices t q = s.indices t q := by
  have h := components_index_frame ops input row tid iteration t 0 8 q acc (beginRound t s) h5 h6 h7
  simpa only [roundAfter, endRound, beginRound, setIndex, advance, h4, h5,
    and_false, ↓reduceIte] using h

theorem initialized_other (ops : Ops α) (t u : Nat) (s : State α) (hu : u ≠ t) :
    (initialized ops t s).pc u = s.pc u ∧
    (initialized ops t s).indices u = s.indices u ∧ (initialized ops t s).regs u = s.regs u := by
  simp [initialized, indexedAt, setIndex, setReg, advance, hu]

theorem prefix_other (ops : Ops α) (input : Nat → Nat → α) (t u : Nat) (s : State α) (hu : u ≠ t) :
    (prefixState ops input t s).pc u = s.pc u ∧
    (prefixState ops input t s).indices u = s.indices u ∧ (prefixState ops input t s).regs u = s.regs u := by
  have h0 := initialized_other ops t u s hu
  have h1 := round_other ops input (t / 1024) (t % 1024) 0 t u (ops.literal 0 1) (initialized ops t s) hu
  have h2 := round_other ops input (t / 1024) (t % 1024) 1 t u
    (folded ops input (t / 1024) (t % 1024) 0 0 8 (ops.literal 0 1))
    (roundAfter ops input (t / 1024) (t % 1024) 0 t (ops.literal 0 1) (initialized ops t s)) hu
  refine ⟨?_, h2.2.1.trans (h1.2.1.trans h0.2.1), h2.2.2.trans (h1.2.2.trans h0.2.2)⟩
  simpa only [prefixState, beforeShuffle, advance, if_neg hu] using h2.1.trans (h1.1.trans h0.1)

theorem prefix_epochs (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (prefixState ops input t s).epochs = s.epochs := by
  simp only [prefixState, advance, beforeShuffle, round_epochs, initialized_preserves ops t s |>.2.2]

theorem prefix_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (l : Location) (hl : ¬ Owns t l) :
    (prefixState ops input t s).memory l = s.memory l := by
  have ht : t % 1024 < 1024 := Nat.mod_lt _ (by decide)
  have he : t = t / 1024 * 1024 + t % 1024 := by omega
  have h1 := round_frame p ops input (t / 1024) (t % 1024) 0 t (ops.literal 0 1)
    (initialized ops t s) ht (by decide) he l hl
  have h2 := round_frame p ops input (t / 1024) (t % 1024) 1 t
    (folded ops input (t / 1024) (t % 1024) 0 0 8 (ops.literal 0 1))
    (roundAfter ops input (t / 1024) (t % 1024) 0 t (ops.literal 0 1) (initialized ops t s))
    ht (by decide) he l hl
  exact h2.trans h1

theorem prefix_pending_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t u ordinal : Nat) (s : State α) (hu : u ≠ t)
    (pending : Pending input (u / 1024) (u % 1024) ordinal s) :
    Pending input (u / 1024) (u % 1024) ordinal (prefixState ops input t s) := by
  constructor
  · intro j hj
    exact (prefix_frame p ops input t s _ (global_input_unowned t 0 _ (Or.inl rfl))).trans (pending.1 j hj)
  · intro j hk hj
    have hn : ¬ Owns t (globalCell 1 (flatAddress (u / 1024) (u % 1024) j)) := by
      intro ho
      exact hu (owns_unique u t _ (residual_owned p u j hj) ho)
    exact (prefix_frame p ops input t s _ hn).trans (pending.2 j hk hj)

theorem prefix_completed_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t u ordinal : Nat) (s : State α) (hu : u ≠ t) (ho : ordinal ≤ 16)
    (done : Completed ops input (u / 1024) (u % 1024) u ordinal s) :
    Completed ops input (u / 1024) (u % 1024) u ordinal (prefixState ops input t s) := by
  intro j hj
  have hn1 : ¬ Owns t (globalCell 1 (flatAddress (u / 1024) (u % 1024) j)) := by
    intro ht; exact hu (owns_unique u t _ (residual_owned p u j (by omega)) ht)
  have hn2 : ¬ Owns t (unroundedCell u (slot (u % 1024) j)) := by
    intro ht; exact hu (owns_unique u t _ (shared_owned u j (by omega)) ht)
  exact ⟨(prefix_frame p ops input t s _ hn1).trans (done j hj).1,
    (prefix_frame p ops input t s _ hn2).trans (done j hj).2⟩

#print axioms owns_unique
#print axioms residual_owned
#print axioms shared_owned
#print axioms component_frame
#print axioms component_other
#print axioms components_frame
#print axioms components_other
#print axioms components_epochs
#print axioms round_frame
#print axioms round_other
#print axioms round_index_frame
#print axioms prefix_other
#print axioms prefix_epochs
#print axioms prefix_frame
#print axioms prefix_pending_other
#print axioms prefix_completed_other
end LarkNativeFusedRmsNorm
