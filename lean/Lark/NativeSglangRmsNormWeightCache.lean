import Lark.NativeSglangRmsNormInputPreloads

/-! Actual six-instruction weight preload cycle, retaining raw half values. -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem eval_weight_column (p : Shape) (t tid iteration component : Nat) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8)
    (h1 : s.indices t 1 = some (tid : Int))
    (h9 : s.indices t 9 = some (iteration : Int)) (h10 : s.indices t 10 = some (component : Int)) :
    evalIndex (geometry p) t s (columnIndex 9 10) = some ((column tid iteration component : Nat) : Int) := by
  have hm := eval_nat_mul (geometry p) t iteration 1024 s (.ivar 9) h9 (by decide) (by omega)
  have ha := eval_nat_sum (geometry p) t (iteration * 1024) tid s _ (.ivar 1) hm h1 (by omega)
  have hv := eval_nat_mul (geometry p) t (iteration * 1024 + tid) 8 s _ ha (by decide) (by omega)
  exact eval_nat_sum (geometry p) t ((iteration * 1024 + tid) * 8) component s _ _ hv h10 (by omega)

theorem eval_weight_slot (p : Shape) (t iteration component : Nat) (s : State α)
    (hi : iteration < 2) (hc : component < 8)
    (h9 : s.indices t 9 = some (iteration : Int)) (h10 : s.indices t 10 = some (component : Int)) :
    evalIndex (geometry p) t s (.add (.mul (.ivar 9) (.const 8)) (.ivar 10)) =
      some ((iteration * 8 + component : Nat) : Int) := by
  have hm := eval_nat_mul (geometry p) t iteration 8 s (.ivar 9) h9 (by decide) (by omega)
  exact eval_nat_sum (geometry p) t (iteration * 8) component s _ _ hm h10 (by omega)

def weightCacheAfter (input : Nat → Nat → α) (tid iteration component t : Nat) (s : State α) : State α :=
  let col := column tid iteration component
  let slot := iteration * 8 + component
  let s := advance s t 20
  let s := setIndex s t 11 (col : Int) 21
  let s := setIndex s t 12 (slot : Int) 22
  let s := cacheWritten t 23 (privateCell t 1 slot) (input 2 col)
    (record s t (globalCell 2 col) false)
  let s := setIndex s t 10 ((component + 1 : Nat) : Int) 24
  advance s t 19

theorem copy_weight_half (p : Shape) (ops : Ops α) (t offset slot : Nat)
    (s : State α) (value : α) (hi : offset < 16384) (hs : slot < 16)
    (hindex : s.indices t 11 = some (offset : Int)) (hslot : s.indices t 12 = some (slot : Int))
    (hm : s.memory (globalCell 2 offset) = some value) (hp : s.pc t = 22) :
    execute ops (layout p) (geometry p) t (.store .local 1 (.ivar 12) (.load .global 2 (.ivar 11))) s =
      some (cacheWritten t 23 (privateCell t 1 slot) value (record s t (globalCell 2 offset) false)) := by
  simp only [execute,evalExpr,evalIndex,hindex,hslot,weight_location p t offset hi,
    private_location p t 1 slot true (by decide) hs,hm,bind,pure,Option.bind]
  simp only [cacheWritten,privateCell,record,advance,hp]

theorem weight_cache_cycle (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (tid iteration component t extra : Nat) (s : State α)
    (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8)
    (h1 : s.indices t 1 = some (tid : Int)) (h9 : s.indices t 9 = some (iteration : Int))
    (h10 : s.indices t 10 = some (component : Int)) (hp : s.pc t = 19)
    (hm : s.memory (globalCell 2 (column tid iteration component)) = some (input 2 (column tid iteration component))) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 6) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
        (weightCacheAfter input tid iteration component t s) := by
  let col := column tid iteration component
  let slot := iteration * 8 + component
  let s1 := advance s t 20
  let s2 := setIndex s1 t 11 (col : Int) 21
  let s3 := setIndex s2 t 12 (slot : Int) 22
  let s4 := cacheWritten t 23 (privateCell t 1 slot) (input 2 col) (record s3 t (globalCell 2 col) false)
  let s5 := setIndex s4 t 10 ((component + 1 : Nat) : Int) 24
  have pred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 10) (.const 8)
    (component : Int) 8 h10 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 10) (.const 8)) 25) s = some s1 := by
    simp only [execute,pred,hp,bind,pure,Option.bind]
    rfl
  have he2 := eval_weight_column p t tid iteration component s1 ht hi hc h1 h9 h10
  have e2 := execute_index_of ops (layout p) (geometry p) t 11 21 (columnIndex 9 10) s1 _ he2
    (by simp [s1,advance])
  have he3 := eval_weight_slot p t iteration component s2 hi hc
    (by simpa [s2,s1,setIndex,advance] using h9) (by simpa [s2,s1,setIndex,advance] using h10)
  have e3 := execute_index_of ops (layout p) (geometry p) t 12 22
    (.add (.mul (.ivar 9) (.const 8)) (.ivar 10)) s2 _ he3 (by simp [s2,setIndex,advance])
  have e4 := copy_weight_half p ops t col slot s3 (input 2 col)
    (column_bound tid iteration component ht hi hc) (by omega)
    (by simp [s3,s2,setIndex,advance]) (by simp [s3,setIndex,advance]) hm (by simp [s3,setIndex,advance])
  have idx4 : s4.indices t 10 = some (component : Int) := by
    simp [s4,s3,s2,s1,cacheWritten,record,setIndex,advance,h10]
  have he5 := eval_nat_sum (geometry p) t component 1 s4 (.ivar 10) (.const 1) idx4 rfl (by omega)
  have e5 := execute_index_of ops (layout p) (geometry p) t 10 24
    (.add (.ivar 10) (.const 1)) s4 _ he5 (by simp [s4,cacheWritten,advance])
  have e6 : execute ops (layout p) (geometry p) t (.jump 19) s5 =
      some (weightCacheAfter input tid iteration component t s) := rfl
  rewrite [scalar_step p repaired ops t 19 _ _ s s1 (by cases repaired <;> decide) hp e1]
  rewrite [scalar_step p repaired ops t 20 _ _ s1 s2 (by cases repaired <;> decide) (by simp [s1,advance]) e2]
  rewrite [scalar_step p repaired ops t 21 _ _ s2 s3 (by cases repaired <;> decide) (by simp [s2,setIndex,advance]) e3]
  rewrite [scalar_step p repaired ops t 22 _ _ s3 s4 (by cases repaired <;> decide) (by simp [s3,setIndex,advance]) e4]
  rewrite [scalar_step p repaired ops t 23 _ _ s4 s5 (by cases repaired <;> decide) (by simp [s4,cacheWritten,advance]) e5]
  rewrite [scalar_step p repaired ops t 24 _ _ s5 _ (by cases repaired <;> decide) (by simp [s5,setIndex,advance]) e6]
  rfl

theorem weight_cache_fields (input : Nat → Nat → α) (tid iteration component t : Nat) (s : State α) :
    (weightCacheAfter input tid iteration component t s).pc t = 19 ∧
    (weightCacheAfter input tid iteration component t s).indices t 0 = s.indices t 0 ∧
    (weightCacheAfter input tid iteration component t s).indices t 1 = s.indices t 1 ∧
    (weightCacheAfter input tid iteration component t s).indices t 9 = s.indices t 9 ∧
    (weightCacheAfter input tid iteration component t s).indices t 10 = some ((component + 1 : Nat) : Int) := by
  simp [weightCacheAfter,setIndex,cacheWritten,record,advance]

theorem weight_cache_memory (input : Nat → Nat → α) (tid iteration component t : Nat)
    (s : State α) (l : Location) :
    (weightCacheAfter input tid iteration component t s).memory l =
      if l = privateCell t 1 (iteration * 8 + component)
      then some (input 2 (column tid iteration component)) else s.memory l := rfl

theorem weight_cache_epochs (input : Nat → Nat → α) (tid iteration component t : Nat) (s : State α) :
    (weightCacheAfter input tid iteration component t s).epochs = s.epochs := rfl

theorem weight_cache_trace (input : Nat → Nat → α) (tid iteration component t : Nat) (s : State α) :
    (weightCacheAfter input tid iteration component t s).trace =
      ⟨t,privateCell t 1 (iteration * 8 + component),true,s.epochs t⟩ ::
      ⟨t,globalCell 2 (column tid iteration component),false,s.epochs t⟩ :: s.trace := rfl

theorem weight_cache_good (input : Nat → Nat → α) (tid iteration component t : Nat)
    (s : State α) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (weightCacheAfter input tid iteration component t s).trace, Good a := by
  intro a ha
  simp only [weight_cache_trace,List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · exact Good.localAccess rfl rfl
  · exact Good.input rfl rfl (Or.inr rfl) rfl
  · exact good a ha

#print axioms eval_weight_column
#print axioms eval_weight_slot
#print axioms copy_weight_half
#print axioms weight_cache_cycle
#print axioms weight_cache_fields
#print axioms weight_cache_memory
#print axioms weight_cache_epochs
#print axioms weight_cache_trace
#print axioms weight_cache_good
end LarkNativeSglangRmsNorm
