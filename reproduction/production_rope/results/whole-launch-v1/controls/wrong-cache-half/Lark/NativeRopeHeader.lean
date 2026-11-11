import Lark.NativeRopeCoordinates

/-! Actual eleven-instruction native Q/K loop headers: branch, pair coordinates,
gathered cache loads and both in-place addresses. No mutable input is read yet. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def queryHeaderAfter (ops : Ops α) (input : Nat → Nat → α)
    (neox : Bool) (row pair t : Nat) (s : State α) : State α :=
  let s1 := advance s t 3
  let s2 := setIndex s1 t 2 ((pair / 64 : Nat) : Int) 4
  let s3 := setIndex s2 t 3 ((pair % 64 : Nat) : Int) 5
  let s4 := setIndex s3 t 4 ((component neox pair false : Nat) : Int) 6
  let s5 := setIndex s4 t 5 ((component neox pair true : Nat) : Int) 7
  let s6 := setIndex s5 t 6 ((cacheCos row pair : Nat) : Int) 8
  let s7 := setIndex s6 t 7 ((cacheSin row pair : Nat) : Int) 9
  let s8 := setReg (record s7 t (globalCell 2 (cacheCos row pair)) false) t 0 (ops.fromHalf (input 2 (cacheCos row pair))) 10
  let s9 := setReg (record s8 t (globalCell 2 (cacheSin row pair)) false) t 1 (ops.fromHalf (input 2 (cacheSin row pair))) 11
  let s10 := setIndex s9 t 8 ((address 0 row pair neox false : Nat) : Int) 12
  setIndex s10 t 9 ((address 0 row pair neox true : Nat) : Int) 13

theorem query_header_cycle (p : Shape) (neox : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row pair t extra : Nat) (s : State α)
    (hr : row < p.rows) (hi : pair < 2048) (hp : s.pc t = 2)
    (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 1 = some (pair : Int))
    (hc : s.memory (globalCell 2 (cacheCos row pair)) = some (input 2 (cacheCos row pair)))
    (hs : s.memory (globalCell 2 (cacheSin row pair)) = some (input 2 (cacheSin row pair))) :
    runLane ops (layout p) (geometry p) (program neox) t (extra + 11) s =
      runLane ops (layout p) (geometry p) (program neox) t extra
        (queryHeaderAfter ops input neox row pair t s) := by
  let s1 := advance s t 3
  let s2 := setIndex s1 t 2 ((pair / 64 : Nat) : Int) 4
  let s3 := setIndex s2 t 3 ((pair % 64 : Nat) : Int) 5
  let s4 := setIndex s3 t 4 ((component neox pair false : Nat) : Int) 6
  let s5 := setIndex s4 t 5 ((component neox pair true : Nat) : Int) 7
  let s6 := setIndex s5 t 6 ((cacheCos row pair : Nat) : Int) 8
  let s7 := setIndex s6 t 7 ((cacheSin row pair : Nat) : Int) 9
  let s8 := setReg (record s7 t (globalCell 2 (cacheCos row pair)) false) t 0 (ops.fromHalf (input 2 (cacheCos row pair))) 10
  let s9 := setReg (record s8 t (globalCell 2 (cacheSin row pair)) false) t 1 (ops.fromHalf (input 2 (cacheSin row pair))) 11
  let s10 := setIndex s9 t 8 ((address 0 row pair neox false : Nat) : Int) 12
  let s11 := setIndex s10 t 9 ((address 0 row pair neox true : Nat) : Int) 13
  have hbounds := cache_bounds p row pair hr
  have hpred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 1) (.const 2048)
    (pair : Int) 2048 h1 (by rfl) (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 1) (.const 2048)) 25) s = some s1 := by
    simp only [execute, hpred, hp, bind, pure, Option.bind]
    rfl
  have he2 := eval_head (geometry p) t 1 pair s1 h1
  have e2 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 2 4
    (.div (.ivar 1) (.const 64)) s1 _ he2 (by simp [s1, advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have idx2 : s2.indices t 1 = some (pair : Int) := by
    simpa [s2, s1, setIndex, LarkReduction.setIndex, setReg, record, advance] using h1
  have he3 := eval_pair_remainder (geometry p) t 1 pair s2 idx2
  have e3 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 3 5
    (.mod (.ivar 1) (.const 64)) s2 _ he3 (by simp [s2, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s2 = some s3 at e3
  have rem3 : s3.indices t 3 = some ((pair % 64 : Nat) : Int) := by simp [s3, setIndex, LarkReduction.setIndex, setReg, record, advance]
  have he4 := eval_x (geometry p) t 3 pair s3 neox rem3
  have e4 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 4 6
    (xIndex neox 3) s3 _ he4 (by simp [s3, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s3 = some s4 at e4
  have rem4 : s4.indices t 3 = some ((pair % 64 : Nat) : Int) := by simp [s4, s3, setIndex, LarkReduction.setIndex, setReg, record, advance]
  have he5 := eval_y (geometry p) t 3 pair s4 neox rem4
  have e5 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 5 7
    (yIndex neox 3) s4 _ he5 (by simp [s4, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s4 = some s5 at e5
  have row5 : s5.indices t 0 = some (row : Int) := by simpa [s5, s4, s3, s2, s1, setIndex, LarkReduction.setIndex, setReg, record, advance] using h0
  have rem5 : s5.indices t 3 = some ((pair % 64 : Nat) : Int) := by simp [s5, s4, s3, setIndex, LarkReduction.setIndex, setReg, record, advance]
  have he6 := eval_cache_cos_address p (geometry p) t row (pair % 64) 0 3 s5 hr (Nat.mod_lt _ (by decide)) row5 rem5
  have e6 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 6 8
    (.add (.mul (.ivar 0) (.const 128)) (.ivar 3)) s5 _ he6 (by simp [s5, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s5 = some s6 at e6
  have cos6 : s6.indices t 6 = some ((cacheCos row pair : Nat) : Int) := by simp [s6, setIndex, LarkReduction.setIndex, setReg, record, advance]
  have he7 := eval_nat_add (geometry p) t s6 (.ivar 6) (.const 64) (cacheCos row pair) 64 cos6 (by rfl)
    (by have hb := p.bound; simp [cacheCos]; have hj := Nat.mod_lt pair (by decide : 0 < 64); omega)
  have e7 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 7 9
    (.add (.ivar 6) (.const 64)) s6 _ he7 (by simp [s6, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s6 = some s7 at e7
  have cos7 : s7.indices t 6 = some ((cacheCos row pair : Nat) : Int) := by simp [s7, s6, setIndex, LarkReduction.setIndex, setReg, record, advance]
  have he8 := load_cache p ops t (cacheCos row pair) 6 s7 (input 2 (cacheCos row pair)) hbounds.1 cos7 hc
  have e8 : execute ops (layout p) (geometry p) t (.assign 0 (.un .fromHalf (.load .global 2 (.ivar 6)))) s7 = some s8 := by
    simp only [execute, he8, bind, pure, Option.bind]
    rw [show s7.pc t + 1 = 10 by simp [s7, setIndex, LarkReduction.setIndex, setReg, record, advance]]
    rfl
  have sin8 : s8.indices t 7 = some ((cacheSin row pair : Nat) : Int) := by simp [s8, s7, setIndex, LarkReduction.setIndex, setReg, record, advance]
  have he9 := load_cache p ops t (cacheSin row pair) 7 s8 (input 2 (cacheSin row pair)) hbounds.2 sin8 hs
  have e9 : execute ops (layout p) (geometry p) t (.assign 1 (.un .fromHalf (.load .global 2 (.ivar 7)))) s8 = some s9 := by
    simp only [execute, he9, bind, pure, Option.bind]
    rw [show s8.pc t + 1 = 11 by simp [s8, setIndex, LarkReduction.setIndex, setReg, record, advance]]
    rfl
  have he10 := eval_pair_address p (geometry p) t 0 row pair 0 2 4 s9 neox false hr hi
    (by simpa [s9, s8, s7, s6, s5, s4, s3, s2, s1, setIndex, LarkReduction.setIndex, setReg, record, advance] using h0)
    (by simp [s9, s8, s7, s6, s5, s4, s3, s2, setIndex, LarkReduction.setIndex, setReg, record, advance])
    (by simp [s9, s8, s7, s6, s5, s4, setIndex, LarkReduction.setIndex, setReg, record, advance])
  have e10 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 8 12
    (.add (.add (.mul (.ivar 0) (.const 4096)) (.mul (.ivar 2) (.const 128))) (.ivar 4)) s9 _ he10
    (by simp [s9, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s9 = some s10 at e10
  have he11 := eval_pair_address p (geometry p) t 0 row pair 0 2 5 s10 neox true hr hi
    (by simpa [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, setIndex, LarkReduction.setIndex, setReg, record, advance] using h0)
    (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, setIndex, LarkReduction.setIndex, setReg, record, advance])
    (by simp [s10, s9, s8, s7, s6, s5, setIndex, LarkReduction.setIndex, setReg, record, advance])
  have e11 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 9 13
    (.add (.add (.mul (.ivar 0) (.const 4096)) (.mul (.ivar 2) (.const 128))) (.ivar 5)) s10 _ he11
    (by simp [s10, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s10 = some s11 at e11
  rewrite [scalar_step p neox ops t 2 _ _ s s1 (by cases neox <;> decide) hp e1]
  rewrite [scalar_step p neox ops t 3 _ _ s1 s2 (by cases neox <;> decide) (by simp [s1, setIndex, LarkReduction.setIndex, setReg, record, advance]) e2]
  rewrite [scalar_step p neox ops t 4 _ _ s2 s3 (by cases neox <;> decide) (by simp [s2, setIndex, LarkReduction.setIndex, setReg, record, advance]) e3]
  rewrite [scalar_step p neox ops t 5 _ _ s3 s4 (by cases neox <;> decide) (by simp [s3, setIndex, LarkReduction.setIndex, setReg, record, advance]) e4]
  rewrite [scalar_step p neox ops t 6 _ _ s4 s5 (by cases neox <;> decide) (by simp [s4, setIndex, LarkReduction.setIndex, setReg, record, advance]) e5]
  rewrite [scalar_step p neox ops t 7 _ _ s5 s6 (by cases neox <;> decide) (by simp [s5, setIndex, LarkReduction.setIndex, setReg, record, advance]) e6]
  rewrite [scalar_step p neox ops t 8 _ _ s6 s7 (by cases neox <;> decide) (by simp [s6, setIndex, LarkReduction.setIndex, setReg, record, advance]) e7]
  rewrite [scalar_step p neox ops t 9 _ _ s7 s8 (by cases neox <;> decide) (by simp [s7, setIndex, LarkReduction.setIndex, setReg, record, advance]) e8]
  rewrite [scalar_step p neox ops t 10 _ _ s8 s9 (by cases neox <;> decide) (by simp [s8, setIndex, LarkReduction.setIndex, setReg, record, advance]) e9]
  rewrite [scalar_step p neox ops t 11 _ _ s9 s10 (by cases neox <;> decide) (by simp [s9, setIndex, LarkReduction.setIndex, setReg, record, advance]) e10]
  rewrite [scalar_step p neox ops t 12 _ _ s10 s11 (by cases neox <;> decide) (by simp [s10, setIndex, LarkReduction.setIndex, setReg, record, advance]) e11]
  rfl

#print axioms query_header_cycle

def keyHeaderAfter (ops : Ops α) (input : Nat → Nat → α)
    (neox : Bool) (row pair t : Nat) (s : State α) : State α :=
  let s1 := advance s t 27
  let s2 := setIndex s1 t 11 ((pair / 64 : Nat) : Int) 28
  let s3 := setIndex s2 t 12 ((pair % 64 : Nat) : Int) 29
  let s4 := setIndex s3 t 13 ((component neox pair false : Nat) : Int) 30
  let s5 := setIndex s4 t 14 ((component neox pair true : Nat) : Int) 31
  let s6 := setIndex s5 t 15 ((cacheCos row pair : Nat) : Int) 32
  let s7 := setIndex s6 t 16 ((cacheSin row pair : Nat) : Int) 33
  let s8 := setReg (record s7 t (globalCell 2 (cacheCos row pair)) false) t 10 (ops.fromHalf (input 2 (cacheCos row pair))) 34
  let s9 := setReg (record s8 t (globalCell 2 (cacheSin row pair)) false) t 11 (ops.fromHalf (input 2 (cacheSin row pair))) 35
  let s10 := setIndex s9 t 17 ((address 1 row pair neox false : Nat) : Int) 36
  setIndex s10 t 18 ((address 1 row pair neox true : Nat) : Int) 37

theorem key_header_cycle (p : Shape) (neox : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row pair t extra : Nat) (s : State α)
    (hr : row < p.rows) (hi : pair < 512) (hp : s.pc t = 26)
    (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 10 = some (pair : Int))
    (hc : s.memory (globalCell 2 (cacheCos row pair)) = some (input 2 (cacheCos row pair)))
    (hs : s.memory (globalCell 2 (cacheSin row pair)) = some (input 2 (cacheSin row pair))) :
    runLane ops (layout p) (geometry p) (program neox) t (extra + 11) s =
      runLane ops (layout p) (geometry p) (program neox) t extra
        (keyHeaderAfter ops input neox row pair t s) := by
  let s1 := advance s t 27
  let s2 := setIndex s1 t 11 ((pair / 64 : Nat) : Int) 28
  let s3 := setIndex s2 t 12 ((pair % 64 : Nat) : Int) 29
  let s4 := setIndex s3 t 13 ((component neox pair false : Nat) : Int) 30
  let s5 := setIndex s4 t 14 ((component neox pair true : Nat) : Int) 31
  let s6 := setIndex s5 t 15 ((cacheCos row pair : Nat) : Int) 32
  let s7 := setIndex s6 t 16 ((cacheSin row pair : Nat) : Int) 33
  let s8 := setReg (record s7 t (globalCell 2 (cacheCos row pair)) false) t 10 (ops.fromHalf (input 2 (cacheCos row pair))) 34
  let s9 := setReg (record s8 t (globalCell 2 (cacheSin row pair)) false) t 11 (ops.fromHalf (input 2 (cacheSin row pair))) 35
  let s10 := setIndex s9 t 17 ((address 1 row pair neox false : Nat) : Int) 36
  let s11 := setIndex s10 t 18 ((address 1 row pair neox true : Nat) : Int) 37
  have hbounds := cache_bounds p row pair hr
  have hpred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 10) (.const 512)
    (pair : Int) 512 h1 (by rfl) (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 10) (.const 512)) 49) s = some s1 := by
    simp only [execute, hpred, hp, bind, pure, Option.bind]
    rfl
  have he2 := eval_head (geometry p) t 10 pair s1 h1
  have e2 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 11 28
    (.div (.ivar 10) (.const 64)) s1 _ he2 (by simp [s1, advance])
  change execute _ _ _ _ _ s1 = some s2 at e2
  have idx2 : s2.indices t 10 = some (pair : Int) := by
    simpa [s2, s1, setIndex, LarkReduction.setIndex, setReg, record, advance] using h1
  have he3 := eval_pair_remainder (geometry p) t 10 pair s2 idx2
  have e3 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 12 29
    (.mod (.ivar 10) (.const 64)) s2 _ he3 (by simp [s2, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s2 = some s3 at e3
  have rem3 : s3.indices t 12 = some ((pair % 64 : Nat) : Int) := by simp [s3, setIndex, LarkReduction.setIndex, setReg, record, advance]
  have he4 := eval_x (geometry p) t 12 pair s3 neox rem3
  have e4 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 13 30
    (xIndex neox 12) s3 _ he4 (by simp [s3, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s3 = some s4 at e4
  have rem4 : s4.indices t 12 = some ((pair % 64 : Nat) : Int) := by simp [s4, s3, setIndex, LarkReduction.setIndex, setReg, record, advance]
  have he5 := eval_y (geometry p) t 12 pair s4 neox rem4
  have e5 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 14 31
    (yIndex neox 12) s4 _ he5 (by simp [s4, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s4 = some s5 at e5
  have row5 : s5.indices t 0 = some (row : Int) := by simpa [s5, s4, s3, s2, s1, setIndex, LarkReduction.setIndex, setReg, record, advance] using h0
  have rem5 : s5.indices t 12 = some ((pair % 64 : Nat) : Int) := by simp [s5, s4, s3, setIndex, LarkReduction.setIndex, setReg, record, advance]
  have he6 := eval_cache_cos_address p (geometry p) t row (pair % 64) 0 12 s5 hr (Nat.mod_lt _ (by decide)) row5 rem5
  have e6 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 15 32
    (.add (.mul (.ivar 0) (.const 128)) (.ivar 12)) s5 _ he6 (by simp [s5, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s5 = some s6 at e6
  have cos6 : s6.indices t 15 = some ((cacheCos row pair : Nat) : Int) := by simp [s6, setIndex, LarkReduction.setIndex, setReg, record, advance]
  have he7 := eval_nat_add (geometry p) t s6 (.ivar 15) (.const 64) (cacheCos row pair) 64 cos6 (by rfl)
    (by have hb := p.bound; simp [cacheCos]; have hj := Nat.mod_lt pair (by decide : 0 < 64); omega)
  have e7 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 16 33
    (.add (.ivar 15) (.const 64)) s6 _ he7 (by simp [s6, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s6 = some s7 at e7
  have cos7 : s7.indices t 15 = some ((cacheCos row pair : Nat) : Int) := by simp [s7, s6, setIndex, LarkReduction.setIndex, setReg, record, advance]
  have he8 := load_cache p ops t (cacheCos row pair) 15 s7 (input 2 (cacheCos row pair)) hbounds.1 cos7 hc
  have e8 : execute ops (layout p) (geometry p) t (.assign 10 (.un .fromHalf (.load .global 2 (.ivar 15)))) s7 = some s8 := by
    simp only [execute, he8, bind, pure, Option.bind]
    rw [show s7.pc t + 1 = 34 by simp [s7, setIndex, LarkReduction.setIndex, setReg, record, advance]]
    rfl
  have sin8 : s8.indices t 16 = some ((cacheSin row pair : Nat) : Int) := by simp [s8, s7, setIndex, LarkReduction.setIndex, setReg, record, advance]
  have he9 := load_cache p ops t (cacheSin row pair) 16 s8 (input 2 (cacheSin row pair)) hbounds.2 sin8 hs
  have e9 : execute ops (layout p) (geometry p) t (.assign 11 (.un .fromHalf (.load .global 2 (.ivar 16)))) s8 = some s9 := by
    simp only [execute, he9, bind, pure, Option.bind]
    rw [show s8.pc t + 1 = 35 by simp [s8, setIndex, LarkReduction.setIndex, setReg, record, advance]]
    rfl
  have he10 := eval_pair_address p (geometry p) t 1 row pair 0 11 13 s9 neox false hr hi
    (by simpa [s9, s8, s7, s6, s5, s4, s3, s2, s1, setIndex, LarkReduction.setIndex, setReg, record, advance] using h0)
    (by simp [s9, s8, s7, s6, s5, s4, s3, s2, setIndex, LarkReduction.setIndex, setReg, record, advance])
    (by simp [s9, s8, s7, s6, s5, s4, setIndex, LarkReduction.setIndex, setReg, record, advance])
  have e10 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 17 36
    (.add (.add (.mul (.ivar 0) (.const 1024)) (.mul (.ivar 11) (.const 128))) (.ivar 13)) s9 _ he10
    (by simp [s9, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s9 = some s10 at e10
  have he11 := eval_pair_address p (geometry p) t 1 row pair 0 11 14 s10 neox true hr hi
    (by simpa [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, setIndex, LarkReduction.setIndex, setReg, record, advance] using h0)
    (by simp [s10, s9, s8, s7, s6, s5, s4, s3, s2, s1, setIndex, LarkReduction.setIndex, setReg, record, advance])
    (by simp [s10, s9, s8, s7, s6, s5, setIndex, LarkReduction.setIndex, setReg, record, advance])
  have e11 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 18 37
    (.add (.add (.mul (.ivar 0) (.const 1024)) (.mul (.ivar 11) (.const 128))) (.ivar 14)) s10 _ he11
    (by simp [s10, setIndex, LarkReduction.setIndex, setReg, record, advance])
  change execute _ _ _ _ _ s10 = some s11 at e11
  rewrite [scalar_step p neox ops t 26 _ _ s s1 (by cases neox <;> decide) hp e1]
  rewrite [scalar_step p neox ops t 27 _ _ s1 s2 (by cases neox <;> decide) (by simp [s1, setIndex, LarkReduction.setIndex, setReg, record, advance]) e2]
  rewrite [scalar_step p neox ops t 28 _ _ s2 s3 (by cases neox <;> decide) (by simp [s2, setIndex, LarkReduction.setIndex, setReg, record, advance]) e3]
  rewrite [scalar_step p neox ops t 29 _ _ s3 s4 (by cases neox <;> decide) (by simp [s3, setIndex, LarkReduction.setIndex, setReg, record, advance]) e4]
  rewrite [scalar_step p neox ops t 30 _ _ s4 s5 (by cases neox <;> decide) (by simp [s4, setIndex, LarkReduction.setIndex, setReg, record, advance]) e5]
  rewrite [scalar_step p neox ops t 31 _ _ s5 s6 (by cases neox <;> decide) (by simp [s5, setIndex, LarkReduction.setIndex, setReg, record, advance]) e6]
  rewrite [scalar_step p neox ops t 32 _ _ s6 s7 (by cases neox <;> decide) (by simp [s6, setIndex, LarkReduction.setIndex, setReg, record, advance]) e7]
  rewrite [scalar_step p neox ops t 33 _ _ s7 s8 (by cases neox <;> decide) (by simp [s7, setIndex, LarkReduction.setIndex, setReg, record, advance]) e8]
  rewrite [scalar_step p neox ops t 34 _ _ s8 s9 (by cases neox <;> decide) (by simp [s8, setIndex, LarkReduction.setIndex, setReg, record, advance]) e9]
  rewrite [scalar_step p neox ops t 35 _ _ s9 s10 (by cases neox <;> decide) (by simp [s9, setIndex, LarkReduction.setIndex, setReg, record, advance]) e10]
  rewrite [scalar_step p neox ops t 36 _ _ s10 s11 (by cases neox <;> decide) (by simp [s10, setIndex, LarkReduction.setIndex, setReg, record, advance]) e11]
  rfl

#print axioms key_header_cycle

end LarkNativeRope
