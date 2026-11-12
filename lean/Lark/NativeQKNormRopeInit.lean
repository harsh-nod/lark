import Lark.NativeQKNormRopeIndex

/-! Actual seven-instruction native initialization, including all checked
intermediate index expressions and both distinct row strides. -/
namespace LarkNativeQKNormRope
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def indexed (t : Nat) (s : State α) : State α :=
  let s := setIndex s t 0 ((t / 32 : Nat) : Int) 1
  let s := setIndex s t 1 ((row t : Nat) : Int) 2
  let s := setIndex s t 2 ((head t : Nat) : Int) 3
  let s := setIndex s t 3 ((t % 32 : Nat) : Int) 4
  let s := setIndex s t 4 ((column t 0 : Nat) : Int) 5
  let s := setIndex s t 5 ((inputAddress t 0 : Nat) : Int) 6
  setIndex s t 6 ((outputAddress t 0 : Nat) : Int) 7

structure IndexReady (t : Nat) (s : State α) : Prop where
  pc : s.pc t = 7
  globalHeadIx : s.indices t 0 = some ((t / 32 : Nat) : Int)
  rowIx : s.indices t 1 = some ((row t : Nat) : Int)
  headIx : s.indices t 2 = some ((head t : Nat) : Int)
  laneIx : s.indices t 3 = some ((t % 32 : Nat) : Int)
  columnIx : s.indices t 4 = some ((column t 0 : Nat) : Int)
  inputBaseIx : s.indices t 5 = some ((inputAddress t 0 : Nat) : Int)
  outputBaseIx : s.indices t 6 = some ((outputAddress t 0 : Nat) : Int)

theorem indexed_eq (p : Shape) (neox : Bool) (ops : Ops α) (t extra : Nat)
    (s : State α) (ht : t < p.rows * 1280) (hp : s.pc t = 0) :
    LarkCollective.runLane ops (layout p) (geometry p) (program neox) t (extra + 7) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program neox) t extra (indexed t s) := by
  let s1 := setIndex s t 0 ((t / 32 : Nat) : Int) 1
  let s2 := setIndex s1 t 1 ((row t : Nat) : Int) 2
  let s3 := setIndex s2 t 2 ((head t : Nat) : Int) 3
  let s4 := setIndex s3 t 3 ((t % 32 : Nat) : Int) 4
  let s5 := setIndex s4 t 4 ((column t 0 : Nat) : Int) 5
  let s6 := setIndex s5 t 5 ((inputAddress t 0 : Nat) : Int) 6
  let s7 := setIndex s6 t 6 ((outputAddress t 0 : Nat) : Int) 7
  have e1 := execute_index_of ops (layout p) (geometry p) t 0 1
    (.add (.mul .bid (.const 8)) (.div .tid (.const 32))) s _ (eval_head_global p t s ht) (by omega)
  change execute _ _ _ _ _ s = some s1 at e1
  have h0a : s1.indices t 0 = some ((t / 32 : Nat) : Int) := by simp [s1, setIndex, advance]
  have e2 := execute_index_of ops (layout p) (geometry p) t 1 2
    (.div (.ivar 0) (.const 40)) s1 _ (eval_row p t s1 h0a) (by simp [s1, setIndex, advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have h0b : s2.indices t 0 = some ((t / 32 : Nat) : Int) := by simp [s2, s1, setIndex, advance]
  have e3 := execute_index_of ops (layout p) (geometry p) t 2 3
    (.mod (.ivar 0) (.const 40)) s2 _ (eval_head p t s2 h0b) (by simp [s2, setIndex, advance])
  change execute _ _ _ _ _ s2 = some s3 at e3
  have e4 := execute_index_of ops (layout p) (geometry p) t 3 4
    (.mod .tid (.const 32)) s3 _ (eval_lane p t s3) (by simp [s3, setIndex, advance])
  change execute _ _ _ _ _ s3 = some s4 at e4
  have h3 : s4.indices t 3 = some ((t % 32 : Nat) : Int) := by simp [s4, setIndex, advance]
  have e5 := execute_index_of ops (layout p) (geometry p) t 4 5
    (.mul (.ivar 3) (.const 4)) s4 _ (eval_column p t s4 h3) (by simp [s4, setIndex, advance])
  change execute _ _ _ _ _ s4 = some s5 at e5
  have h1 : s5.indices t 1 = some ((row t : Nat) : Int) := by simp [s5, s4, s3, s2, setIndex, advance]
  have h2 : s5.indices t 2 = some ((head t : Nat) : Int) := by simp [s5, s4, s3, setIndex, advance]
  have h4 : s5.indices t 4 = some ((column t 0 : Nat) : Int) := by simp [s5, setIndex, advance]
  have e6 := execute_index_of ops (layout p) (geometry p) t 5 6
    (baseIndex 6144) s5 _ (eval_input_base p t s5 ht h1 h2 h4) (by simp [s5, setIndex, advance])
  change execute _ _ _ _ _ s5 = some s6 at e6
  have h1' : s6.indices t 1 = some ((row t : Nat) : Int) := by simp [s6, s5, s4, s3, s2, setIndex, advance]
  have h2' : s6.indices t 2 = some ((head t : Nat) : Int) := by simp [s6, s5, s4, s3, setIndex, advance]
  have h4' : s6.indices t 4 = some ((column t 0 : Nat) : Int) := by simp [s6, s5, setIndex, advance]
  have e7 := execute_index_of ops (layout p) (geometry p) t 6 7
    (baseIndex 5120) s6 _ (eval_output_base p t s6 ht h1' h2' h4') (by simp [s6, setIndex, advance])
  change execute _ _ _ _ _ s6 = some s7 at e7
  rewrite [scalar_step p neox ops t 0 _ _ s s1 (by cases neox <;> decide) hp e1]
  rewrite [scalar_step p neox ops t 1 _ _ s1 s2 (by cases neox <;> decide) (by simp [s1, setIndex, advance]) e2]
  rewrite [scalar_step p neox ops t 2 _ _ s2 s3 (by cases neox <;> decide) (by simp [s2, setIndex, advance]) e3]
  rewrite [scalar_step p neox ops t 3 _ _ s3 s4 (by cases neox <;> decide) (by simp [s3, setIndex, advance]) e4]
  rewrite [scalar_step p neox ops t 4 _ _ s4 s5 (by cases neox <;> decide) (by simp [s4, setIndex, advance]) e5]
  rewrite [scalar_step p neox ops t 5 _ _ s5 s6 (by cases neox <;> decide) (by simp [s5, setIndex, advance]) e6]
  rewrite [scalar_step p neox ops t 6 _ _ s6 s7 (by cases neox <;> decide) (by simp [s6, setIndex, advance]) e7]
  rfl

theorem indexed_ready (t : Nat) (s : State α) : IndexReady t (indexed t s) := by
  constructor <;> simp [indexed, setIndex, advance]

theorem indexed_preserves (t : Nat) (s : State α) :
    (indexed t s).memory = s.memory ∧ (indexed t s).trace = s.trace ∧
    (indexed t s).epochs = s.epochs ∧ (indexed t s).regs = s.regs := ⟨rfl, rfl, rfl, rfl⟩

theorem indexed_other (t u : Nat) (s : State α) (hu : u ≠ t) :
    (indexed t s).pc u = s.pc u ∧ (indexed t s).indices u = s.indices u := by
  constructor
  · simp [indexed, setIndex, advance, hu]
  · funext r
    simp [indexed, setIndex, advance, hu]

#print axioms indexed_eq
#print axioms indexed_ready
#print axioms indexed_preserves
#print axioms indexed_other
end LarkNativeQKNormRope
