import Lark.NativeSoftmaxMaxLoop

/-! Both actual outer-loop tests, initialization and counter updates for the
first softmax pass, including the inner loop's false exit. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of predicate_lt_of predicate_nlt_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def maxBeginRound (t : Nat) (s : State α) : State α :=
  setIndex (advance s t 7) t 5 0 8

def maxEndRound (t tid iteration : Nat) (s : State α) : State α :=
  advance (setIndex (advance s t 17) t 4 ((base tid (iteration+1) : Nat) : Int) 18) t 6

theorem max_begin_round_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (t tid iteration extra : Nat) (s : State α)
    (ht : tid < 1024) (hi : iteration < 7) (hp : s.pc t = 6)
    (h4 : s.indices t 4 = some ((base tid iteration : Nat) : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra (maxBeginRound t s) := by
  have bound : base tid iteration < 50257 := by unfold base; omega
  have pred := predicate_lt_of (geometry p) t s (.ivar 4) (.const 50257)
    (base tid iteration : Int) 50257 h4 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 4) (.const 50257)) 19) s = some (advance s t 7) := by
    simp [execute,pred,hp]
  have e2 := execute_index_of ops (layout p) (geometry p) t 5 8 (.const 0)
    (advance s t 7) 0 rfl (by simp [advance])
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 6 _ _ s _ (by cases guarded <;> decide) hp e1]
  rewrite [scalar_step p guarded ops t 7 _ _ _ _ (by cases guarded <;> decide)
    (by simp [advance]) e2]
  rfl

theorem max_end_round_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (t tid iteration extra : Nat) (s : State α)
    (ht : tid < 1024) (hi : iteration < 7) (hp : s.pc t = 8)
    (h4 : s.indices t 4 = some ((base tid iteration : Nat) : Int))
    (h5 : s.indices t 5 = some 8) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (maxEndRound t tid iteration s) := by
  have pred := predicate_nlt_of (geometry p) t s (.ivar 5) (.const 8) 8 8 h5 rfl (by omega)
  let s1 := advance s t 17
  let s2 := setIndex s1 t 4 ((base tid (iteration+1) : Nat) : Int) 18
  have e1 : execute ops (layout p) (geometry p) t
      (.branch (.lt (.ivar 5) (.const 8)) 17) s = some s1 := by
    simp [execute,pred,hp,s1]
  have hb : base tid iteration + 8192 < 2147483648 := by unfold base; omega
  have he := eval_nat_sum (geometry p) t (base tid iteration) 8192 s1 (.ivar 4) (.const 8192) h4 rfl hb
  have he' : evalIndex (geometry p) t s1 (.add (.ivar 4) (.const 8192)) =
      some ((base tid (iteration+1) : Nat) : Int) := by
    have hbase : base tid iteration + 8192 = base tid (iteration+1) := by
      simp [base,Nat.add_mul]
      omega
    simpa only [hbase] using he
  have e2 := execute_index_of ops (layout p) (geometry p) t 4 18
    (.add (.ivar 4) (.const 8192)) s1 _ he' (by simp [s1,advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have e3 : execute ops (layout p) (geometry p) t (.jump 6) s2 =
      some (maxEndRound t tid iteration s) := rfl
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p guarded ops t 8 _ _ s s1 (by cases guarded <;> decide) hp e1]
  rewrite [scalar_step p guarded ops t 17 _ _ s1 s2 (by cases guarded <;> decide)
    (by simp [s1,advance]) e2]
  rewrite [scalar_step p guarded ops t 18 _ _ s2 _ (by cases guarded <;> decide)
    (by simp [s2,setIndex,advance]) e3]
  rfl

structure MaxRoundReady (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) : Prop where
  pc : s.pc t = 6
  rowIndex : s.indices t 0 = some (row : Int)
  tidIndex : s.indices t 1 = some (tid : Int)
  baseIndex : s.indices t 4 = some ((base tid iteration : Nat) : Int)
  accumulator : s.regs t 0 = some acc
  reads : Reads p input s
  good : ∀ a ∈ s.trace, Good a

theorem max_begin_round_ready (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α)
    (ready : MaxRoundReady p input row tid iteration t acc s) :
    MaxReady p input row tid iteration 0 t acc (maxBeginRound t s) := by
  exact {
    pc := by simp [maxBeginRound,setIndex,advance]
    rowIndex := by simpa [maxBeginRound,setIndex,advance] using ready.rowIndex
    tidIndex := by simpa [maxBeginRound,setIndex,advance] using ready.tidIndex
    baseIndex := by simpa [maxBeginRound,setIndex,advance] using ready.baseIndex
    componentIndex := by simp [maxBeginRound,setIndex,advance]
    accumulator := ready.accumulator
    reads := ready.reads
    good := ready.good }

theorem max_end_round_ready (p : Shape) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α)
    (ready : MaxReady p input row tid iteration 8 t acc s) :
    MaxRoundReady p input row tid (iteration+1) t acc (maxEndRound t tid iteration s) := by
  exact {
    pc := by simp [maxEndRound,setIndex,advance]
    rowIndex := by simpa [maxEndRound,setIndex,advance] using ready.rowIndex
    tidIndex := by simpa [maxEndRound,setIndex,advance] using ready.tidIndex
    baseIndex := by simp [maxEndRound,setIndex,advance]
    accumulator := ready.accumulator
    reads := ready.reads
    good := ready.good }

def maxRoundAfter (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) : State α :=
  maxEndRound t tid iteration
    (maxComponents ops input row tid iteration t 0 8 acc (maxBeginRound t s))

def maxRoundCost (tid iteration : Nat) : Nat := 5 + maxComponentsCost tid iteration 0 8

theorem max_round_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α)
    (ready : MaxRoundReady p input row tid iteration t acc s) :
    MaxRoundReady p input row tid (iteration+1) t
      (maxFold ops input row tid iteration 0 8 acc)
      (maxRoundAfter ops input row tid iteration t acc s) :=
  max_end_round_ready p input row tid iteration t _ _
    (max_components_ready p ops input row tid iteration t 0 8 acc (maxBeginRound t s)
      (max_begin_round_ready p input row tid iteration t acc s ready))

theorem max_round_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t extra : Nat) (acc : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 7)
    (ready : MaxRoundReady p input row tid iteration t acc s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t
        (extra + maxRoundCost tid iteration) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (maxRoundAfter ops input row tid iteration t acc s) := by
  have beginReady := max_begin_round_ready p input row tid iteration t acc s ready
  have last := max_components_ready p ops input row tid iteration t 0 8 acc (maxBeginRound t s) beginReady
  rewrite [show extra + maxRoundCost tid iteration =
      (extra + 3 + maxComponentsCost tid iteration 0 8) + 2 by unfold maxRoundCost; omega,
    max_begin_round_eq p guarded ops t tid iteration _ s ht hi ready.pc ready.baseIndex]
  rewrite [max_components_eq p guarded ops input row tid iteration t 0 8 (extra+3) acc _
    hr ht hi (by decide) beginReady]
  exact max_end_round_eq p guarded ops t tid iteration extra _ ht hi last.pc last.baseIndex last.componentIndex

theorem max_round_cost_bound (tid iteration : Nat) : maxRoundCost tid iteration ≤ 77 := by
  have h := max_components_cost_bound tid iteration 0 8
  unfold maxRoundCost
  omega

theorem max_round_frames (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) :
    (maxRoundAfter ops input row tid iteration t acc s).memory = s.memory ∧
    (maxRoundAfter ops input row tid iteration t acc s).epochs = s.epochs ∧
    (maxRoundAfter ops input row tid iteration t acc s).trace.length = s.trace.length + 8 :=
  max_components_frames ops input row tid iteration t 0 8 acc (maxBeginRound t s)

theorem max_round_index_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t r : Nat) (acc : α) (s : State α)
    (h4 : r ≠ 4) (h5 : r ≠ 5) (h6 : r ≠ 6) (h7 : r ≠ 7) :
    (maxRoundAfter ops input row tid iteration t acc s).indices t r = s.indices t r := by
  have hend (q : State α) : (maxEndRound t tid iteration q).indices t r = q.indices t r := by
    simp [maxEndRound,setIndex,advance,h4]
  change (maxEndRound t tid iteration
    (maxComponents ops input row tid iteration t 0 8 acc (maxBeginRound t s))).indices t r = _
  rewrite [hend]
  rewrite [max_components_index_other ops input row tid iteration t 0 8 r acc _ h5 h6 h7]
  simp [maxBeginRound,setIndex,advance,h5]

#print axioms max_begin_round_eq
#print axioms max_end_round_eq
#print axioms max_begin_round_ready
#print axioms max_end_round_ready
#print axioms max_round_ready
#print axioms max_round_eq
#print axioms max_round_cost_bound
#print axioms max_round_frames
#print axioms max_round_index_other
end LarkNativeSoftmax
