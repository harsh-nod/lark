import Lark.NativeFusedRmsNormState

/-! Actual seven-instruction native initialization; inputs and traces are framed.
-/
namespace LarkNativeFusedRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg int32_cast execute_index_of execute_pure_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def indexedAt (row tid t : Nat) (s : State α) : State α :=
  let s := setIndex s t 0 (row : Int) 1
  let s := setIndex s t 1 (tid : Int) 2
  let s := setIndex s t 2 ((tid % 32 : Nat) : Int) 3
  setIndex s t 3 ((tid / 32 : Nat) : Int) 4

def initialized (ops : Ops α) (t : Nat) (s : State α) : State α :=
  let s := indexedAt (t / 1024) (t % 1024) t s
  let s := setReg s t 0 (ops.literal 0 1) 5
  let s := setReg s t 1 (ops.literal 0 1) 6
  setIndex s t 4 0 7

theorem indexed_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (ht : t < p.rows * 1024) (hp : s.pc t = 0) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 4) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (indexedAt (t / 1024) (t % 1024) t s) := by
  have hr : t / 1024 < 256 := by have h := p.bound; omega
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
  rewrite [scalar_step p ops t 0 _ _ s s1 (by decide) hp h1]
  rewrite [scalar_step p ops t 1 _ _ s1 s2 (by decide) (by simp [s1, setIndex, advance]) h2]
  rewrite [scalar_step p ops t 2 _ _ s2 s3 (by decide) (by simp [s2, setIndex, advance]) h3]
  rewrite [scalar_step p ops t 3 _ _ s3 _ (by decide) (by simp [s3, setIndex, advance]) h4]
  rfl

theorem initialized_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (ht : t < p.rows * 1024) (hp : s.pc t = 0) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 7) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (initialized ops t s) := by
  rewrite [show extra + 7 = (extra + 3) + 4 by omega, indexed_eq p ops t (extra + 3) s ht hp]
  let s4 := indexedAt (t / 1024) (t % 1024) t s
  let s5 := setReg s4 t 0 (ops.literal 0 1) 5
  let s6 := setReg s5 t 1 (ops.literal 0 1) 6
  have h5 := execute_pure_of ops (layout p) (geometry p) t 0 5 (.lit 0 1) s4 (ops.literal 0 1)
    (by simp [evalExpr]) (by simp [s4, indexedAt, setIndex, advance])
  change execute _ _ _ _ _ s4 = some s5 at h5
  have h6 := execute_pure_of ops (layout p) (geometry p) t 1 6 (.lit 0 1) s5 (ops.literal 0 1)
    (by simp [evalExpr]) (by simp [s5, setReg, advance])
  change execute _ _ _ _ _ s5 = some s6 at h6
  have h7 := execute_index_of ops (layout p) (geometry p) t 4 7 (.const 0) s6 0 rfl
    (by simp [s6, setReg, advance])
  change execute _ _ _ _ _ s6 = some (initialized ops t s) at h7
  rewrite [scalar_step p ops t 4 _ _ s4 s5 (by decide) (by simp [s4, indexedAt, setIndex, advance]) h5]
  rewrite [scalar_step p ops t 5 _ _ s5 s6 (by decide) (by simp [s5, setReg, advance]) h6]
  rewrite [scalar_step p ops t 6 _ _ s6 _ (by decide) (by simp [s6, setReg, advance]) h7]
  rfl

theorem initialized_fields (ops : Ops α) (t : Nat) (s : State α) :
    (initialized ops t s).pc t = 7 ∧
    (initialized ops t s).indices t 0 = some ((t / 1024 : Nat) : Int) ∧
    (initialized ops t s).indices t 1 = some ((t % 1024 : Nat) : Int) ∧
    (initialized ops t s).indices t 4 = some 0 ∧
    (initialized ops t s).regs t 0 = some (ops.literal 0 1) := by
  simp [initialized, indexedAt, setIndex, setReg, advance]

theorem initialized_preserves (ops : Ops α) (t : Nat) (s : State α) :
    (initialized ops t s).memory = s.memory ∧
    (initialized ops t s).trace = s.trace ∧ (initialized ops t s).epochs = s.epochs := ⟨rfl, rfl, rfl⟩

#print axioms indexed_eq
#print axioms initialized_eq
#print axioms initialized_fields
#print axioms initialized_preserves
end LarkNativeFusedRmsNorm
