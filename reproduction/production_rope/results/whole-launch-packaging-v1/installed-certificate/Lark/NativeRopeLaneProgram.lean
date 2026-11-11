import Lark.NativeRopeQuerySequence

/-! The actual two-index lane initializer and the source loop exits. These
steps retain the native 512-thread geometry and do not access memory. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def laneStarted (row tid t : Nat) (s : State α) : State α :=
  setIndex (setIndex s t 0 (row : Int) 1) t 1 (tid : Int) 2
def beginKey (tid t : Nat) (s : State α) : State α :=
  setIndex (advance s t 25) t 10 (tid : Int) 26

theorem thread_coordinates (row tid t : Nat) (ht : tid < 512) (he : t = row * 512 + tid) :
    t / 512 = row ∧ t % 512 = tid := by omega

theorem lane_started_ready (row tid t : Nat) (s : State α) :
    (laneStarted row tid t s).pc t = 2 ∧
    (laneStarted row tid t s).indices t 0 = some (row : Int) ∧
    (laneStarted row tid t s).indices t 1 = some (tid : Int) := by
  simp [laneStarted, setIndex, LarkReduction.setIndex, advance]

theorem begin_key_ready (row tid t : Nat) (s : State α) (hrow : s.indices t 0 = some (row : Int)) :
    (beginKey tid t s).pc t = 26 ∧ (beginKey tid t s).indices t 0 = some (row : Int) ∧
    (beginKey tid t s).indices t 10 = some (tid : Int) := by
  simp [beginKey, setIndex, LarkReduction.setIndex, advance, hrow]

theorem lane_start_cycle (p : Shape) (neox : Bool) (ops : Ops α)
    (row tid t extra : Nat) (s : State α) (hr : row < p.rows) (ht : tid < 512)
    (hthread : t = row * 512 + tid) (hp : s.pc t = 0) :
    runLane ops (layout p) (geometry p) (program neox) t (extra + 2) s =
      runLane ops (layout p) (geometry p) (program neox) t extra (laneStarted row tid t s) := by
  let s1 := setIndex s t 0 (row : Int) 1
  have co := thread_coordinates row tid t ht hthread
  have hs := p.bound
  have he1 : evalIndex (geometry p) t s .bid = some (row : Int) := by
    simp only [evalIndex, geometry, co.1]
    exact LarkReduction.int32_cast row (by omega)
  have e1 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 0 1 .bid s _ he1 (by omega)
  change execute _ _ _ _ _ s = some s1 at e1
  have he2 : evalIndex (geometry p) t s1 .tid = some (tid : Int) := by
    simp only [evalIndex, geometry, co.2]
    exact LarkReduction.int32_cast tid (by omega)
  have e2 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 1 2 .tid s1 _ he2
    (by simp [s1, setIndex, LarkReduction.setIndex, advance])
  change execute _ _ _ _ _ s1 = some (laneStarted row tid t s) at e2
  rewrite [scalar_step p neox ops t 0 _ _ s s1 (by cases neox <;> decide) hp e1]
  rewrite [scalar_step p neox ops t 1 _ _ s1 _ (by cases neox <;> decide)
    (by simp [s1, setIndex, LarkReduction.setIndex, advance]) e2]
  rfl

theorem query_exit_cycle (p : Shape) (neox : Bool) (ops : Ops α)
    (tid t extra : Nat) (s : State α) (ht : tid < 512) (hm : t % 512 = tid)
    (hp : s.pc t = 2) (hindex : s.indices t 1 = some ((tid + 2048 : Nat) : Int)) :
    runLane ops (layout p) (geometry p) (program neox) t (extra + 2) s =
      runLane ops (layout p) (geometry p) (program neox) t extra (beginKey tid t s) := by
  let s1 := advance s t 25
  have hnot : ¬ ((tid + 2048 : Nat) : Int) < 2048 := by omega
  have hpred : evalPredicate (geometry p) t s (.lt (.ivar 1) (.const 2048)) = some false := by
    simp [evalPredicate, evalIndex, hindex, int32, hnot] <;> omega
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 1) (.const 2048)) 25) s = some s1 := by
    simp only [execute, hpred, bind, pure, Option.bind]
    rfl
  have he2 : evalIndex (geometry p) t s1 .tid = some (tid : Int) := by
    simp only [evalIndex, geometry, hm]
    exact LarkReduction.int32_cast tid (by omega)
  have e2 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 10 26 .tid s1 _ he2
    (by simp [s1, advance])
  change execute _ _ _ _ _ s1 = some (beginKey tid t s) at e2
  rewrite [scalar_step p neox ops t 2 _ _ s s1 (by cases neox <;> decide) hp e1]
  rewrite [scalar_step p neox ops t 25 _ _ s1 _ (by cases neox <;> decide) (by simp [s1, advance]) e2]
  rfl

theorem key_exit_cycle (p : Shape) (neox : Bool) (ops : Ops α)
    (tid t extra : Nat) (s : State α) (hp : s.pc t = 26)
    (hindex : s.indices t 10 = some ((tid + 512 : Nat) : Int)) :
    runLane ops (layout p) (geometry p) (program neox) t (extra + 1) s =
      runLane ops (layout p) (geometry p) (program neox) t extra (advance s t 49) := by
  have hnot : ¬ ((tid + 512 : Nat) : Int) < 512 := by omega
  have hpred : evalPredicate (geometry p) t s (.lt (.ivar 10) (.const 512)) = some false := by
    simp [evalPredicate, evalIndex, hindex, int32, hnot] <;> omega
  have e : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 10) (.const 512)) 49) s =
      some (advance s t 49) := by
    simp only [execute, hpred, bind, pure, Option.bind]
    rfl
  exact scalar_step p neox ops t 26 extra _ s _ (by cases neox <;> decide) hp e

theorem halted_lane (p : Shape) (neox : Bool) (ops : Ops α) (t extra : Nat)
    (s : State α) (hp : s.pc t = 49) :
    runLane ops (layout p) (geometry p) (program neox) t (extra + 1) s = some s := by
  simp only [runLane, parked, hp, final_halt]

#print axioms thread_coordinates
#print axioms lane_started_ready
#print axioms begin_key_ready
#print axioms lane_start_cycle
#print axioms query_exit_cycle
#print axioms key_exit_cycle
#print axioms halted_lane
end LarkNativeRope
