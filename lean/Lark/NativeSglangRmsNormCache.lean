import Lark.NativeSglangRmsNormInit

/-! Actual seven-instruction input preload cycle. Raw half values are copied
without applying a floating-point conversion; both memory events are retained.+-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def privateCell (t buffer offset : Nat) : Location := ⟨.local,t,buffer,offset⟩

def inputCacheAfter (input : Nat → Nat → α) (row tid iteration component t : Nat)
    (s : State α) : State α :=
  let col := column tid iteration component
  let offset := address row col
  let slot := iteration * 8 + component
  let s := advance s t 8
  let s := setIndex s t 6 (col : Int) 9
  let s := setIndex s t 7 (offset : Int) 10
  let s := setIndex s t 8 (slot : Int) 11
  let s := cacheWritten t 12 (privateCell t 0 slot) (input 1 offset)
    (record s t (globalCell 1 offset) false)
  let s := setIndex s t 5 ((component + 1 : Nat) : Int) 13
  advance s t 7

theorem copy_input_half (p : Shape) (ops : Ops α) (t offset slot : Nat)
    (s : State α) (value : α) (hi : offset < p.rows * 16384) (hs : slot < 16)
    (hindex : s.indices t 7 = some (offset : Int))
    (hslot : s.indices t 8 = some (slot : Int))
    (hm : s.memory (globalCell 1 offset) = some value) (hp : s.pc t = 11) :
    execute ops (layout p) (geometry p) t (.store .local 0 (.ivar 8) (.load .global 1 (.ivar 7))) s =
      some (cacheWritten t 12 (privateCell t 0 slot) value
        (record s t (globalCell 1 offset) false)) := by
  simp only [execute, evalExpr, evalIndex, hindex, hslot, input_location p t offset hi,
    private_location p t 0 slot true (by decide) hs, hm, bind, pure, Option.bind]
  simp only [cacheWritten, privateCell, record, advance, hp]

theorem input_cache_cycle (p : Shape) (repaired : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row tid iteration component t extra : Nat) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (hi : iteration < 2) (hc : component < 8)
    (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 1 = some (tid : Int))
    (h4 : s.indices t 4 = some (iteration : Int)) (h5 : s.indices t 5 = some (component : Int))
    (hp : s.pc t = 7)
    (hm : s.memory (globalCell 1 (address row (column tid iteration component))) =
      some (input 1 (address row (column tid iteration component)))) :
    LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t (extra + 7) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t extra
        (inputCacheAfter input row tid iteration component t s) := by
  let col := column tid iteration component
  let offset := address row col
  let slot := iteration * 8 + component
  let s1 := advance s t 8
  let s2 := setIndex s1 t 6 (col : Int) 9
  let s3 := setIndex s2 t 7 (offset : Int) 10
  let s4 := setIndex s3 t 8 (slot : Int) 11
  let s5 := cacheWritten t 12 (privateCell t 0 slot) (input 1 offset)
    (record s4 t (globalCell 1 offset) false)
  let s6 := setIndex s5 t 5 ((component + 1 : Nat) : Int) 13
  have hpred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 5) (.const 8)
    (component : Int) 8 h5 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 5) (.const 8)) 14) s = some s1 := by
    simp only [execute, hpred, hp, bind, pure, Option.bind]
    rfl
  have he2 := eval_column p t tid iteration component s1 ht hi hc h1 h4 h5
  have e2 := execute_index_of ops (layout p) (geometry p) t 6 9 (columnIndex 4 5) s1 _ he2
    (by simp [s1, advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have hcol := column_bound tid iteration component ht hi hc
  have he3 := eval_address p t row col s2 hr hcol
    (by simpa [s2, s1, setIndex, advance] using h0) (by simp [s2, setIndex, advance])
  have e3 := execute_index_of ops (layout p) (geometry p) t 7 10
    (.add (.mul (.ivar 0) (.const 16384)) (.ivar 6)) s2 _ he3 (by simp [s2, setIndex, advance])
  change execute _ _ _ _ _ s2 = some s3 at e3
  have he4 := eval_slot p t iteration component s3 hi hc
    (by simpa [s3, s2, s1, setIndex, advance] using h4)
    (by simpa [s3, s2, s1, setIndex, advance] using h5)
  have e4 := execute_index_of ops (layout p) (geometry p) t 8 11
    (.add (.mul (.ivar 4) (.const 8)) (.ivar 5)) s3 _ he4 (by simp [s3, setIndex, advance])
  change execute _ _ _ _ _ s3 = some s4 at e4
  have hb := address_bound p row tid iteration component hr ht hi hc
  have e5 := copy_input_half p ops t offset slot s4 (input 1 offset) hb (by omega)
    (by simp [s4, s3, setIndex, advance]) (by simp [s4, setIndex, advance]) hm
    (by simp [s4, setIndex, advance])
  change execute _ _ _ _ _ s4 = some s5 at e5
  have idx5 : s5.indices t 5 = some (component : Int) := by
    simp [s5, s4, s3, s2, s1, cacheWritten, record, setIndex, advance, h5]
  have he6 := eval_nat_sum (geometry p) t component 1 s5 (.ivar 5) (.const 1) idx5 rfl (by omega)
  have e6 := execute_index_of ops (layout p) (geometry p) t 5 13
    (.add (.ivar 5) (.const 1)) s5 _ he6 (by simp [s5, cacheWritten, advance])
  change execute _ _ _ _ _ s5 = some s6 at e6
  have e7 : execute ops (layout p) (geometry p) t (.jump 7) s6 =
      some (inputCacheAfter input row tid iteration component t s) := rfl
  rewrite [scalar_step p repaired ops t 7 _ _ s s1 (by cases repaired <;> decide) hp e1]
  rewrite [scalar_step p repaired ops t 8 _ _ s1 s2 (by cases repaired <;> decide) (by simp [s1, advance]) e2]
  rewrite [scalar_step p repaired ops t 9 _ _ s2 s3 (by cases repaired <;> decide) (by simp [s2, setIndex, advance]) e3]
  rewrite [scalar_step p repaired ops t 10 _ _ s3 s4 (by cases repaired <;> decide) (by simp [s3, setIndex, advance]) e4]
  rewrite [scalar_step p repaired ops t 11 _ _ s4 s5 (by cases repaired <;> decide) (by simp [s4, setIndex, advance]) e5]
  rewrite [scalar_step p repaired ops t 12 _ _ s5 s6 (by cases repaired <;> decide) (by simp [s5, cacheWritten, advance]) e6]
  rewrite [scalar_step p repaired ops t 13 _ _ s6 _ (by cases repaired <;> decide) (by simp [s6, setIndex, advance]) e7]
  rfl

theorem input_cache_fields (input : Nat → Nat → α) (row tid iteration component t : Nat) (s : State α) :
    (inputCacheAfter input row tid iteration component t s).pc t = 7 ∧
    (inputCacheAfter input row tid iteration component t s).indices t 0 = s.indices t 0 ∧
    (inputCacheAfter input row tid iteration component t s).indices t 1 = s.indices t 1 ∧
    (inputCacheAfter input row tid iteration component t s).indices t 4 = s.indices t 4 ∧
    (inputCacheAfter input row tid iteration component t s).indices t 5 = some ((component + 1 : Nat) : Int) := by
  simp [inputCacheAfter, setIndex, cacheWritten, record, advance]

theorem input_cache_memory (input : Nat → Nat → α) (row tid iteration component t : Nat)
    (s : State α) (l : Location) :
    (inputCacheAfter input row tid iteration component t s).memory l =
      if l = privateCell t 0 (iteration * 8 + component)
      then some (input 1 (address row (column tid iteration component))) else s.memory l := rfl

theorem input_cache_epochs (input : Nat → Nat → α) (row tid iteration component t : Nat) (s : State α) :
    (inputCacheAfter input row tid iteration component t s).epochs = s.epochs := rfl

theorem input_cache_trace (input : Nat → Nat → α) (row tid iteration component t : Nat) (s : State α) :
    (inputCacheAfter input row tid iteration component t s).trace =
      ⟨t,privateCell t 0 (iteration * 8 + component),true,s.epochs t⟩ ::
      ⟨t,globalCell 1 (address row (column tid iteration component)),false,s.epochs t⟩ :: s.trace := rfl

theorem input_cache_good (input : Nat → Nat → α) (row tid iteration component t : Nat)
    (s : State α) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (inputCacheAfter input row tid iteration component t s).trace, Good a := by
  intro a ha
  simp only [input_cache_trace, List.mem_cons] at ha
  rcases ha with rfl | rfl | ha
  · exact Good.localAccess rfl rfl
  · exact Good.input rfl rfl (Or.inl rfl) rfl
  · exact good a ha

#print axioms copy_input_half
#print axioms input_cache_cycle
#print axioms input_cache_fields
#print axioms input_cache_memory
#print axioms input_cache_epochs
#print axioms input_cache_trace
#print axioms input_cache_good
end LarkNativeSglangRmsNorm
