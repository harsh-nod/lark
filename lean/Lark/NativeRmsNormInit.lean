import Lark.NativeRmsNormValue

/-! Actual scalar-machine initialization for the fixed native program.
This is the first execution phase, not a complete kernel certificate.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg int32_cast execute_index_of execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem scalar_step (ops : Ops α) (l : Layout) (g : Geometry)
    (p : List LarkCollective.Instr) (t extra : Nat) (s next : State α) (i : Instr)
    (hp : LarkCollective.parked p s t = none)
    (hi : p[s.pc t]? = some (.scalar i))
    (he : execute ops l g t i s = some next) :
    LarkCollective.runLane ops l g p t (extra + 1) s =
      LarkCollective.runLane ops l g p t extra next := by
  rewrite [LarkCollective.runLane, hp]
  simp only [hi, bind, pure, Option.bind, he]

/-- Keep integer checks separate from symbolic evaluation of the native guard. -/
theorem eval_sub_mul (g : Geometry) (t reg : Nat) (s : State α) (value a b : Int)
    (hi : s.indices t reg = some value)
    (ha : int32 a = some a) (hb : int32 b = some b)
    (hm : int32 (value * b) = some (value * b))
    (hs : int32 (a - value * b) = some (a - value * b)) :
    evalIndex g t s (.sub (.const a) (.mul (.ivar reg) (.const b))) = some (a - value * b) := by
  simp only [evalIndex, hi, ha, hb, hm, hs, bind, pure, Option.bind]

def indexedAt (row tid t : Nat) (s : State α) : State α :=
  let s := setIndex s t 0 (row : Int) 1
  let s := setIndex s t 1 (tid : Int) 2
  let s := setIndex s t 2 ((tid % 64 : Nat) : Int) 3
  let s := setIndex s t 3 ((tid / 64 : Nat) : Int) 4
  setIndex s t 4 (1024 - ((tid / 64 : Nat) : Int) * 64) 5

def indexed (t : Nat) (s : State α) : State α := indexedAt (t / 1024) (t % 1024) t s

def initialized (ops : Ops α) (t : Nat) (s : State α) : State α :=
  let s := indexed t s
  let s := setReg s t 0 (ops.literal 0 1) 6
  let s := setReg s t 1 (ops.literal 0 1) 7
  setIndex s t 5 ((t % 1024 : Nat) : Int) 8

theorem indexedAt_eq (p : Shape) (ops : Ops α) (row tid t extra : Nat) (s : State α)
    (hrow : t / 1024 = row) (hmod : t % 1024 = tid)
    (hr : row < 256) (hp : s.pc t = 0) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 5) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (indexedAt row tid t s) := by
  let lane := tid % 64
  let warp := tid / 64
  let valid : Int := 1024 - (warp : Int) * 64
  have hrow32 : row < 2147483648 := by omega
  have hwarp : warp < 16 := by dsimp [warp]; omega
  have hvalid : 0 ≤ valid ∧ valid < 2147483648 := by dsimp [valid]; omega
  have hmul : 0 ≤ (warp : Int) * 64 ∧ (warp : Int) * 64 < 2147483648 := by omega
  let s1 := setIndex s t 0 (row : Int) 1
  let s2 := setIndex s1 t 1 (tid : Int) 2
  let s3 := setIndex s2 t 2 (lane : Int) 3
  let s4 := setIndex s3 t 3 (warp : Int) 4
  have h1 := execute_index_of ops (layout p) (geometry p) t 0 1 .bid s (row : Int)
    (by simpa only [evalIndex, geometry, hrow] using int32_cast row hrow32) (by omega)
  change execute _ _ _ _ _ s = some s1 at h1
  have h2 := execute_index_of ops (layout p) (geometry p) t 1 2 .tid s1 (tid : Int)
    (by simpa only [evalIndex, geometry, hmod] using int32_cast tid (by omega))
    (by simp [s1, setIndex, advance])
  change execute _ _ _ _ _ s1 = some s2 at h2
  have he3 : evalIndex (geometry p) t s2 (.mod (.ivar 1) (.const 64)) = some (lane : Int) := by
    simp [evalIndex, s2, setIndex, advance, int32, lane]
  have h3 := execute_index_of ops (layout p) (geometry p) t 2 3
    (.mod (.ivar 1) (.const 64)) s2 (lane : Int) he3 (by simp [s2, setIndex, advance])
  change execute _ _ _ _ _ s2 = some s3 at h3
  have he4 : evalIndex (geometry p) t s3 (.div (.ivar 1) (.const 64)) = some (warp : Int) := by
    simp [evalIndex, s3, s2, setIndex, advance, int32, warp]
    rfl
  have h4 := execute_index_of ops (layout p) (geometry p) t 3 4
    (.div (.ivar 1) (.const 64)) s3 (warp : Int) he4 (by simp [s3, setIndex, advance])
  change execute _ _ _ _ _ s3 = some s4 at h4
  have he5 : evalIndex (geometry p) t s4
      (.sub (.const 1024) (.mul (.ivar 3) (.const 64))) = some valid := by
    apply eval_sub_mul _ _ _ _ _ _ _ (by simp [s4, setIndex, advance])
    · exact int32_cast 1024 (by decide)
    · exact int32_cast 64 (by decide)
    · unfold int32
      exact if_pos hmul
    · unfold int32
      exact if_pos hvalid
  have h5 := execute_index_of ops (layout p) (geometry p) t 4 5
    (.sub (.const 1024) (.mul (.ivar 3) (.const 64))) s4 (valid : Int) he5
    (by simp [s4, setIndex, advance])
  change execute _ _ _ _ _ s4 = some (indexedAt row tid t s) at h5
  rewrite [scalar_step ops _ _ _ _ _ _ _ _ (by simp [LarkCollective.parked, program, hp])
    (by simp [program, hp]) h1]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _ (by simp [LarkCollective.parked, program, s1, setIndex, advance])
    (by simp [program, s1, setIndex, advance]) h2]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _ (by simp [LarkCollective.parked, program, s2, setIndex, advance])
    (by simp [program, s2, setIndex, advance]) h3]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _ (by simp [LarkCollective.parked, program, s3, setIndex, advance])
    (by simp [program, s3, setIndex, advance]) h4]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _ (by simp [LarkCollective.parked, program, s4, setIndex, advance])
    (by simp [program, s4, setIndex, advance]) h5]
  rfl

theorem indexed_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (ht : t < p.rows * 1024) (hp : s.pc t = 0) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 5) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (indexed t s) := by
  apply indexedAt_eq p ops (t / 1024) (t % 1024) t extra s rfl rfl
  · have hrow : t / 1024 < p.rows := (Nat.div_lt_iff_lt_mul (by decide)).mpr ht
    have h := p.bound
    omega
  · exact hp

theorem initialized_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (ht : t < p.rows * 1024) (hp : s.pc t = 0) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 8) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (initialized ops t s) := by
  rewrite [show extra + 8 = (extra + 3) + 5 by omega, indexed_eq p ops t (extra + 3) s ht hp]
  let s5 := indexed t s
  let s6 := setReg s5 t 0 (ops.literal 0 1) 6
  let s7 := setReg s6 t 1 (ops.literal 0 1) 7
  have h6 := execute_pure_of ops (layout p) (geometry p) t 0 6 (.lit 0 1) s5 (ops.literal 0 1)
    (by simp [evalExpr]) (by simp [s5, indexed, indexedAt, setIndex, advance])
  change execute _ _ _ _ _ s5 = some s6 at h6
  have h7 := execute_pure_of ops (layout p) (geometry p) t 1 7 (.lit 0 1) s6 (ops.literal 0 1)
    (by simp [evalExpr]) (by simp [s6, setReg, advance])
  change execute _ _ _ _ _ s6 = some s7 at h7
  have h8 := execute_index_of ops (layout p) (geometry p) t 5 8 (.ivar 1) s7 ((t % 1024 : Nat) : Int)
    (by simp [evalIndex, s7, s6, s5, indexed, indexedAt, setReg, setIndex, advance])
    (by simp [s7, setReg, advance])
  change execute _ _ _ _ _ s7 = some (initialized ops t s) at h8
  rewrite [scalar_step ops _ _ _ _ _ _ _ _
    (by simp [LarkCollective.parked, program, s5, indexed, indexedAt, setIndex, advance])
    (by simp [program, s5, indexed, indexedAt, setIndex, advance]) h6]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _ (by simp [LarkCollective.parked, program, s6, setReg, advance])
    (by simp [program, s6, setReg, advance]) h7]
  rewrite [scalar_step ops _ _ _ _ _ _ _ _ (by simp [LarkCollective.parked, program, s7, setReg, advance])
    (by simp [program, s7, setReg, advance]) h8]
  rfl

theorem initialized_preserves (ops : Ops α) (t : Nat) (s : State α) :
    (initialized ops t s).memory = s.memory ∧
    (initialized ops t s).trace = s.trace ∧ (initialized ops t s).epochs = s.epochs := ⟨rfl, rfl, rfl⟩

theorem initialized_fields (ops : Ops α) (t : Nat) (s : State α) :
    (initialized ops t s).pc t = 8 ∧
    (initialized ops t s).indices t 0 = some ((t / 1024 : Nat) : Int) ∧
    (initialized ops t s).indices t 1 = some ((t % 1024 : Nat) : Int) ∧
    (initialized ops t s).indices t 2 = some (((t % 1024) % 64 : Nat) : Int) ∧
    (initialized ops t s).indices t 3 = some (((t % 1024) / 64 : Nat) : Int) ∧
    (initialized ops t s).indices t 4 = some (1024 - (((t % 1024) / 64 : Nat) : Int) * 64) ∧
    (initialized ops t s).indices t 5 = some ((t % 1024 : Nat) : Int) ∧
    (initialized ops t s).regs t 0 = some (ops.literal 0 1) ∧
    (initialized ops t s).regs t 1 = some (ops.literal 0 1) := by
  simp [initialized, indexed, indexedAt, setIndex, setReg, advance]

theorem initialized_other (ops : Ops α) (t u : Nat) (s : State α) (hu : u ≠ t) :
    (initialized ops t s).pc u = s.pc u ∧
    (initialized ops t s).indices u = s.indices u ∧
    (initialized ops t s).regs u = s.regs u := by
  simp [initialized, indexed, indexedAt, setIndex, setReg, advance, hu]

theorem initialized_from_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (t extra : Nat) (ht : t < p.rows * 1024) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 8)
      (initial (layout p) input outside) =
    LarkCollective.runLane ops (layout p) (geometry p) program t extra
      (initialized ops t (initial (layout p) input outside)) :=
  initialized_eq p ops t extra _ ht rfl

#print axioms initialized_eq
#print axioms indexed_eq
#print axioms indexedAt_eq
#print axioms initialized_preserves
#print axioms initialized_fields
#print axioms initialized_other
#print axioms initialized_from_initial
end LarkNativeRmsNorm
