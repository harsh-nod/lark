import Lark.NativeSglangRmsNormState

/-! Actual five-instruction native initialization; inputs and traces are framed.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg int32_cast execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def indexedAt (row tid t : Nat) (s : State α) : State α :=
  let s := setIndex s t 0 (row : Int) 1
  let s := setIndex s t 1 (tid : Int) 2
  let s := setIndex s t 2 ((tid % 32 : Nat) : Int) 3
  setIndex s t 3 ((tid / 32 : Nat) : Int) 4

def initialized (t : Nat) (s : State α) : State α :=
  setIndex (indexedAt (t / 1024) (t % 1024) t s) t 4 0 5

theorem indexed_eq (p : Shape) (repaired : Bool) (ops : Ops α) (t extra : Nat) (s : State α)
    (ht : t < p.rows * 1024) (hp : s.pc t = 0) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 4) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
        (indexedAt (t / 1024) (t % 1024) t s) := by
  have hr : t / 1024 < 131072 := by have h := p.bound; omega
  have hm : t % 1024 < 1024 := Nat.mod_lt _ (by decide)
  let s1 := setIndex s t 0 ((t / 1024 : Nat) : Int) 1
  let s2 := setIndex s1 t 1 ((t % 1024 : Nat) : Int) 2
  let s3 := setIndex s2 t 2 (((t % 1024) % 32 : Nat) : Int) 3
  have h1 := execute_index_of ops (layout p) (geometry p) t 0 1 .bid s
    ((t / 1024 : Nat) : Int)
    (by simpa only [evalIndex, geometry] using int32_cast (t / 1024) (by omega)) (by omega)
  change execute _ _ _ _ _ s = some s1 at h1
  have h2 := execute_index_of ops (layout p) (geometry p) t 1 2 .tid s1
    ((t % 1024 : Nat) : Int)
    (by simpa only [evalIndex, geometry] using int32_cast (t % 1024) (by omega))
    (by simp [s1, setIndex, advance])
  change execute _ _ _ _ _ s1 = some s2 at h2
  have he3 : evalIndex (geometry p) t s2 (.mod (.ivar 1) (.const 32)) =
      some (((t % 1024) % 32 : Nat) : Int) := by
    have hn : 0 ≤ (t : Int) % 1024 := Int.emod_nonneg _ (by decide)
    simp [evalIndex, s2, setIndex, advance, int32, hn]
  have h3 := execute_index_of ops (layout p) (geometry p) t 2 3
    (.mod (.ivar 1) (.const 32)) s2 _ he3 (by simp [s2, setIndex, advance])
  change execute _ _ _ _ _ s2 = some s3 at h3
  have he4 : evalIndex (geometry p) t s3 (.div (.ivar 1) (.const 32)) =
      some (((t % 1024) / 32 : Nat) : Int) := by
    have hn : 0 ≤ (t : Int) % 1024 := Int.emod_nonneg _ (by decide)
    simp [evalIndex, s3, s2, setIndex, advance, int32, hn, Int.ofNat_ediv]
  have h4 := execute_index_of ops (layout p) (geometry p) t 3 4
    (.div (.ivar 1) (.const 32)) s3 _ he4 (by simp [s3, setIndex, advance])
  change execute _ _ _ _ _ s3 = some (indexedAt (t / 1024) (t % 1024) t s) at h4
  rewrite [scalar_step p repaired ops t 0 _ _ s s1 (by cases repaired <;> decide) hp h1]
  rewrite [scalar_step p repaired ops t 1 _ _ s1 s2 (by cases repaired <;> decide) (by simp [s1, setIndex, advance]) h2]
  rewrite [scalar_step p repaired ops t 2 _ _ s2 s3 (by cases repaired <;> decide) (by simp [s2, setIndex, advance]) h3]
  rewrite [scalar_step p repaired ops t 3 _ _ s3 _ (by cases repaired <;> decide) (by simp [s3, setIndex, advance]) h4]
  rfl

theorem initialized_eq (p : Shape) (repaired : Bool) (ops : Ops α)
    (t extra : Nat) (s : State α) (ht : t < p.rows * 1024) (hp : s.pc t = 0) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 5) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra (initialized t s) := by
  rewrite [show extra + 5 = (extra + 1) + 4 by omega,
    indexed_eq p repaired ops t (extra + 1) s ht hp]
  let s4 := indexedAt (t / 1024) (t % 1024) t s
  have h5 := execute_index_of ops (layout p) (geometry p) t 4 5 (.const 0) s4 0 rfl
    (by simp [s4, indexedAt, setIndex, advance])
  change execute _ _ _ _ _ s4 = some (initialized t s) at h5
  exact scalar_step p repaired ops t 4 extra _ s4 _ (by cases repaired <;> decide)
    (by simp [s4, indexedAt, setIndex, advance]) h5

theorem initialized_fields (t : Nat) (s : State α) :
    (initialized t s).pc t = 5 ∧
    (initialized t s).indices t 0 = some ((t / 1024 : Nat) : Int) ∧
    (initialized t s).indices t 1 = some ((t % 1024 : Nat) : Int) ∧
    (initialized t s).indices t 2 = some (((t % 1024) % 32 : Nat) : Int) ∧
    (initialized t s).indices t 3 = some (((t % 1024) / 32 : Nat) : Int) ∧
    (initialized t s).indices t 4 = some 0 := by
  simp [initialized, indexedAt, setIndex, advance]

theorem initialized_preserves (t : Nat) (s : State α) :
    (initialized t s).memory = s.memory ∧
    (initialized t s).trace = s.trace ∧ (initialized t s).epochs = s.epochs := ⟨rfl, rfl, rfl⟩

theorem initialized_other (t u : Nat) (s : State α) (hu : u ≠ t) :
    (initialized t s).pc u = s.pc u ∧
    (initialized t s).indices u = s.indices u ∧
    (initialized t s).regs u = s.regs u := by
  simp [initialized, indexedAt, setIndex, advance, hu]

#print axioms indexed_eq
#print axioms initialized_eq
#print axioms initialized_fields
#print axioms initialized_preserves
#print axioms initialized_other
end LarkNativeSglangRmsNorm
