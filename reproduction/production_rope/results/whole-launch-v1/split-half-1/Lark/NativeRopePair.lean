import Lark.NativeRopeState

/-! Actual ten-instruction query pair cycle, retaining both input reads before
either in-place store, both memory effects and the complete four-access trace.
Entry reachability is an obligation of the following lane/launch proofs. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def pairReal (ops : Ops α) (x y c s : α) : α :=
  ops.sub (ops.mul (ops.fromHalf x) c) (ops.mul (ops.fromHalf y) s)
def pairImaginary (ops : Ops α) (x y c s : α) : α :=
  ops.add (ops.mul (ops.fromHalf y) c) (ops.mul (ops.fromHalf x) s)

def queryPairAfter (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α) : State α :=
  let s := setReg (record s t (globalCell 0 a) false) t 2 (ops.fromHalf x) 14
  let s := setReg (record s t (globalCell 0 b) false) t 3 (ops.fromHalf y) 15
  let s := setReg s t 4 (ops.mul (ops.fromHalf x) c) 16
  let s := setReg s t 5 (ops.mul (ops.fromHalf y) sn) 17
  let s := setReg s t 6 (ops.mul (ops.fromHalf y) c) 18
  let s := setReg s t 7 (ops.mul (ops.fromHalf x) sn) 19
  let s := setReg s t 8 (pairReal ops x y c sn) 20
  let s := setReg s t 9 (pairImaginary ops x y c sn) 21
  let s := written t 22 (globalCell 0 a) (ops.toHalf (pairReal ops x y c sn)) s
  written t 23 (globalCell 0 b) (ops.toHalf (pairImaginary ops x y c sn)) s

theorem query_pair_cycle (p : Shape) (neox : Bool) (ops : Ops α) (t a b extra : Nat)
    (x y c sn : α) (s : State α) (hp : s.pc t = 13)
    (ha : a < p.rows * 4096) (hb : b < p.rows * 4096)
    (hix : s.indices t 8 = some (a : Int)) (hiy : s.indices t 9 = some (b : Int))
    (hx : s.memory (globalCell 0 a) = some x) (hy : s.memory (globalCell 0 b) = some y)
    (hc : s.regs t 0 = some c) (hs : s.regs t 1 = some sn) :
    runLane ops (layout p) (geometry p) (program neox) t (extra + 10) s =
      runLane ops (layout p) (geometry p) (program neox) t extra
        (queryPairAfter ops t a b x y c sn s) := by
  have hla := mutable_location p t 0 a false (Or.inl rfl) ha
  have hlb := mutable_location p t 0 b false (Or.inl rfl) hb
  have hwa := mutable_location p t 0 a true (Or.inl rfl) ha
  have hwb := mutable_location p t 0 b true (Or.inl rfl) hb
  let s1 := setReg (record s t (globalCell 0 a) false) t 2 (ops.fromHalf x) 14
  let s2 := setReg (record s1 t (globalCell 0 b) false) t 3 (ops.fromHalf y) 15
  let s3 := setReg s2 t 4 (ops.mul (ops.fromHalf x) c) 16
  let s4 := setReg s3 t 5 (ops.mul (ops.fromHalf y) sn) 17
  let s5 := setReg s4 t 6 (ops.mul (ops.fromHalf y) c) 18
  let s6 := setReg s5 t 7 (ops.mul (ops.fromHalf x) sn) 19
  let s7 := setReg s6 t 8 (pairReal ops x y c sn) 20
  let s8 := setReg s7 t 9 (pairImaginary ops x y c sn) 21
  let s9 := written t 22 (globalCell 0 a) (ops.toHalf (pairReal ops x y c sn)) s8
  let s10 := written t 23 (globalCell 0 b) (ops.toHalf (pairImaginary ops x y c sn)) s9
  have he1 := load_mutable p ops t 0 a 8 s x (Or.inl rfl) ha hix hx
  have e1 : execute ops (layout p) (geometry p) t
      (.assign 2 (.un .fromHalf (.load .global 0 (.ivar 8)))) s = some s1 := by
    simp only [execute, he1, bind, pure, Option.bind]
    rw [show s.pc t + 1 = 14 by omega]
    rfl
  have he2 := load_mutable p ops t 0 b 9 s1 y (Or.inl rfl) hb hiy hy
  have e2 : execute ops (layout p) (geometry p) t
      (.assign 3 (.un .fromHalf (.load .global 0 (.ivar 9)))) s1 = some s2 := by
    simp only [execute, he2, bind, pure, Option.bind]
    rw [show s1.pc t + 1 = 15 by simp [s1, setReg, advance]]
    rfl
  have e3 := execute_pure_of ops (layout p) (geometry p) t 4 16
    (.bin .mul (.reg 2) (.reg 0)) s2 (ops.mul (ops.fromHalf x) c)
    (by simp [evalExpr, applyBinary, s2, s1, setReg, record, advance, hc])
    (by simp [s2, setReg, advance])
  change execute _ _ _ _ _ s2 = some s3 at e3
  have e4 := execute_pure_of ops (layout p) (geometry p) t 5 17
    (.bin .mul (.reg 3) (.reg 1)) s3 (ops.mul (ops.fromHalf y) sn)
    (by simp [evalExpr, applyBinary, s3, s2, s1, setReg, record, advance, hs])
    (by simp [s3, setReg, advance])
  change execute _ _ _ _ _ s3 = some s4 at e4
  have e5 := execute_pure_of ops (layout p) (geometry p) t 6 18
    (.bin .mul (.reg 3) (.reg 0)) s4 (ops.mul (ops.fromHalf y) c)
    (by simp [evalExpr, applyBinary, s4, s3, s2, s1, setReg, record, advance, hc])
    (by simp [s4, setReg, advance])
  change execute _ _ _ _ _ s4 = some s5 at e5
  have e6 := execute_pure_of ops (layout p) (geometry p) t 7 19
    (.bin .mul (.reg 2) (.reg 1)) s5 (ops.mul (ops.fromHalf x) sn)
    (by simp [evalExpr, applyBinary, s5, s4, s3, s2, s1, setReg, record, advance, hs])
    (by simp [s5, setReg, advance])
  change execute _ _ _ _ _ s5 = some s6 at e6
  have e7 := execute_pure_of ops (layout p) (geometry p) t 8 20
    (.bin .sub (.reg 4) (.reg 5)) s6 (pairReal ops x y c sn)
    (by simp [evalExpr, applyBinary, s6, s5, s4, s3, setReg, advance, pairReal])
    (by simp [s6, setReg, advance])
  change execute _ _ _ _ _ s6 = some s7 at e7
  have e8 := execute_pure_of ops (layout p) (geometry p) t 9 21
    (.bin .add (.reg 6) (.reg 7)) s7 (pairImaginary ops x y c sn)
    (by simp [evalExpr, applyBinary, s7, s6, s5, setReg, advance, pairImaginary])
    (by simp [s7, setReg, advance])
  change execute _ _ _ _ _ s7 = some s8 at e8
  have expr9 : evalExpr ops (layout p) (geometry p) t (.un .toHalf (.reg 8)) s8 =
      some (ops.toHalf (pairReal ops x y c sn), s8) := by
    simp [evalExpr, applyUnary, s8, s7, setReg, advance]
  have e9 : execute ops (layout p) (geometry p) t
      (.store .global 0 (.ivar 8) (.un .toHalf (.reg 8))) s8 = some s9 := by
    have hpc : s8.pc t + 1 = 22 := by simp [s8, setReg, advance]
    have idx : s8.indices t 8 = some (a : Int) := hix
    simp only [execute, evalIndex, idx, hwa, expr9, bind, pure, Option.bind, hpc]
    rfl
  have expr10 : evalExpr ops (layout p) (geometry p) t (.un .toHalf (.reg 9)) s9 =
      some (ops.toHalf (pairImaginary ops x y c sn), s9) := by
    simp [evalExpr, applyUnary, s9, s8, written, record, setReg, advance]
  have e10 : execute ops (layout p) (geometry p) t
      (.store .global 0 (.ivar 9) (.un .toHalf (.reg 9))) s9 = some s10 := by
    have hpc : s9.pc t + 1 = 23 := by simp [s9, written, advance]
    have idx : s9.indices t 9 = some (b : Int) := hiy
    simp only [execute, evalIndex, idx, hwb, expr10, bind, pure, Option.bind, hpc]
    rfl
  rewrite [scalar_step p neox ops t 13 _ _ s s1 (by cases neox <;> decide) hp e1]
  rewrite [scalar_step p neox ops t 14 _ _ s1 s2 (by cases neox <;> decide)
    (by simp [s1, setReg, advance]) e2]
  rewrite [scalar_step p neox ops t 15 _ _ s2 s3 (by cases neox <;> decide)
    (by simp [s2, setReg, advance]) e3]
  rewrite [scalar_step p neox ops t 16 _ _ s3 s4 (by cases neox <;> decide)
    (by simp [s3, setReg, advance]) e4]
  rewrite [scalar_step p neox ops t 17 _ _ s4 s5 (by cases neox <;> decide)
    (by simp [s4, setReg, advance]) e5]
  rewrite [scalar_step p neox ops t 18 _ _ s5 s6 (by cases neox <;> decide)
    (by simp [s5, setReg, advance]) e6]
  rewrite [scalar_step p neox ops t 19 _ _ s6 s7 (by cases neox <;> decide)
    (by simp [s6, setReg, advance]) e7]
  rewrite [scalar_step p neox ops t 20 _ _ s7 s8 (by cases neox <;> decide)
    (by simp [s7, setReg, advance]) e8]
  rewrite [scalar_step p neox ops t 21 _ _ s8 s9 (by cases neox <;> decide)
    (by simp [s8, setReg, advance]) e9]
  rewrite [scalar_step p neox ops t 22 _ _ s9 s10 (by cases neox <;> decide)
    (by simp [s9, written, advance]) e10]
  rfl


def keyPairAfter (ops : Ops α) (t a b : Nat) (x y c sn : α) (s : State α) : State α :=
  let s := setReg (record s t (globalCell 1 a) false) t 12 (ops.fromHalf x) 38
  let s := setReg (record s t (globalCell 1 b) false) t 13 (ops.fromHalf y) 39
  let s := setReg s t 14 (ops.mul (ops.fromHalf x) c) 40
  let s := setReg s t 15 (ops.mul (ops.fromHalf y) sn) 41
  let s := setReg s t 16 (ops.mul (ops.fromHalf y) c) 42
  let s := setReg s t 17 (ops.mul (ops.fromHalf x) sn) 43
  let s := setReg s t 18 (pairReal ops x y c sn) 44
  let s := setReg s t 19 (pairImaginary ops x y c sn) 45
  let s := written t 46 (globalCell 1 a) (ops.toHalf (pairReal ops x y c sn)) s
  written t 47 (globalCell 1 b) (ops.toHalf (pairImaginary ops x y c sn)) s

theorem key_pair_cycle (p : Shape) (neox : Bool) (ops : Ops α) (t a b extra : Nat)
    (x y c sn : α) (s : State α) (hp : s.pc t = 37)
    (ha : a < p.rows * 1024) (hb : b < p.rows * 1024)
    (hix : s.indices t 17 = some (a : Int)) (hiy : s.indices t 18 = some (b : Int))
    (hx : s.memory (globalCell 1 a) = some x) (hy : s.memory (globalCell 1 b) = some y)
    (hc : s.regs t 10 = some c) (hs : s.regs t 11 = some sn) :
    runLane ops (layout p) (geometry p) (program neox) t (extra + 10) s =
      runLane ops (layout p) (geometry p) (program neox) t extra
        (keyPairAfter ops t a b x y c sn s) := by
  have hla := mutable_location p t 1 a false (Or.inr rfl) ha
  have hlb := mutable_location p t 1 b false (Or.inr rfl) hb
  have hwa := mutable_location p t 1 a true (Or.inr rfl) ha
  have hwb := mutable_location p t 1 b true (Or.inr rfl) hb
  let s1 := setReg (record s t (globalCell 1 a) false) t 12 (ops.fromHalf x) 38
  let s2 := setReg (record s1 t (globalCell 1 b) false) t 13 (ops.fromHalf y) 39
  let s3 := setReg s2 t 14 (ops.mul (ops.fromHalf x) c) 40
  let s4 := setReg s3 t 15 (ops.mul (ops.fromHalf y) sn) 41
  let s5 := setReg s4 t 16 (ops.mul (ops.fromHalf y) c) 42
  let s6 := setReg s5 t 17 (ops.mul (ops.fromHalf x) sn) 43
  let s7 := setReg s6 t 18 (pairReal ops x y c sn) 44
  let s8 := setReg s7 t 19 (pairImaginary ops x y c sn) 45
  let s9 := written t 46 (globalCell 1 a) (ops.toHalf (pairReal ops x y c sn)) s8
  let s10 := written t 47 (globalCell 1 b) (ops.toHalf (pairImaginary ops x y c sn)) s9
  have he1 := load_mutable p ops t 1 a 17 s x (Or.inr rfl) ha hix hx
  have e1 : execute ops (layout p) (geometry p) t
      (.assign 12 (.un .fromHalf (.load .global 1 (.ivar 17)))) s = some s1 := by
    simp only [execute, he1, bind, pure, Option.bind]
    rw [show s.pc t + 1 = 38 by omega]
    rfl
  have he2 := load_mutable p ops t 1 b 18 s1 y (Or.inr rfl) hb hiy hy
  have e2 : execute ops (layout p) (geometry p) t
      (.assign 13 (.un .fromHalf (.load .global 1 (.ivar 18)))) s1 = some s2 := by
    simp only [execute, he2, bind, pure, Option.bind]
    rw [show s1.pc t + 1 = 39 by simp [s1, setReg, advance]]
    rfl
  have e3 := execute_pure_of ops (layout p) (geometry p) t 14 40
    (.bin .mul (.reg 12) (.reg 10)) s2 (ops.mul (ops.fromHalf x) c)
    (by simp [evalExpr, applyBinary, s2, s1, setReg, record, advance, hc])
    (by simp [s2, setReg, advance])
  change execute _ _ _ _ _ s2 = some s3 at e3
  have e4 := execute_pure_of ops (layout p) (geometry p) t 15 41
    (.bin .mul (.reg 13) (.reg 11)) s3 (ops.mul (ops.fromHalf y) sn)
    (by simp [evalExpr, applyBinary, s3, s2, s1, setReg, record, advance, hs])
    (by simp [s3, setReg, advance])
  change execute _ _ _ _ _ s3 = some s4 at e4
  have e5 := execute_pure_of ops (layout p) (geometry p) t 16 42
    (.bin .mul (.reg 13) (.reg 10)) s4 (ops.mul (ops.fromHalf y) c)
    (by simp [evalExpr, applyBinary, s4, s3, s2, s1, setReg, record, advance, hc])
    (by simp [s4, setReg, advance])
  change execute _ _ _ _ _ s4 = some s5 at e5
  have e6 := execute_pure_of ops (layout p) (geometry p) t 17 43
    (.bin .mul (.reg 12) (.reg 11)) s5 (ops.mul (ops.fromHalf x) sn)
    (by simp [evalExpr, applyBinary, s5, s4, s3, s2, s1, setReg, record, advance, hs])
    (by simp [s5, setReg, advance])
  change execute _ _ _ _ _ s5 = some s6 at e6
  have e7 := execute_pure_of ops (layout p) (geometry p) t 18 44
    (.bin .sub (.reg 14) (.reg 15)) s6 (pairReal ops x y c sn)
    (by simp [evalExpr, applyBinary, s6, s5, s4, s3, setReg, advance, pairReal])
    (by simp [s6, setReg, advance])
  change execute _ _ _ _ _ s6 = some s7 at e7
  have e8 := execute_pure_of ops (layout p) (geometry p) t 19 45
    (.bin .add (.reg 16) (.reg 17)) s7 (pairImaginary ops x y c sn)
    (by simp [evalExpr, applyBinary, s7, s6, s5, setReg, advance, pairImaginary])
    (by simp [s7, setReg, advance])
  change execute _ _ _ _ _ s7 = some s8 at e8
  have expr9 : evalExpr ops (layout p) (geometry p) t (.un .toHalf (.reg 18)) s8 =
      some (ops.toHalf (pairReal ops x y c sn), s8) := by
    simp [evalExpr, applyUnary, s8, s7, setReg, advance]
  have e9 : execute ops (layout p) (geometry p) t
      (.store .global 1 (.ivar 17) (.un .toHalf (.reg 18))) s8 = some s9 := by
    have hpc : s8.pc t + 1 = 46 := by simp [s8, setReg, advance]
    have idx : s8.indices t 17 = some (a : Int) := hix
    simp only [execute, evalIndex, idx, hwa, expr9, bind, pure, Option.bind, hpc]
    rfl
  have expr10 : evalExpr ops (layout p) (geometry p) t (.un .toHalf (.reg 19)) s9 =
      some (ops.toHalf (pairImaginary ops x y c sn), s9) := by
    simp [evalExpr, applyUnary, s9, s8, written, record, setReg, advance]
  have e10 : execute ops (layout p) (geometry p) t
      (.store .global 1 (.ivar 18) (.un .toHalf (.reg 19))) s9 = some s10 := by
    have hpc : s9.pc t + 1 = 47 := by simp [s9, written, advance]
    have idx : s9.indices t 18 = some (b : Int) := hiy
    simp only [execute, evalIndex, idx, hwb, expr10, bind, pure, Option.bind, hpc]
    rfl
  rewrite [scalar_step p neox ops t 37 _ _ s s1 (by cases neox <;> decide) hp e1]
  rewrite [scalar_step p neox ops t 38 _ _ s1 s2 (by cases neox <;> decide)
    (by simp [s1, setReg, advance]) e2]
  rewrite [scalar_step p neox ops t 39 _ _ s2 s3 (by cases neox <;> decide)
    (by simp [s2, setReg, advance]) e3]
  rewrite [scalar_step p neox ops t 40 _ _ s3 s4 (by cases neox <;> decide)
    (by simp [s3, setReg, advance]) e4]
  rewrite [scalar_step p neox ops t 41 _ _ s4 s5 (by cases neox <;> decide)
    (by simp [s4, setReg, advance]) e5]
  rewrite [scalar_step p neox ops t 42 _ _ s5 s6 (by cases neox <;> decide)
    (by simp [s5, setReg, advance]) e6]
  rewrite [scalar_step p neox ops t 43 _ _ s6 s7 (by cases neox <;> decide)
    (by simp [s6, setReg, advance]) e7]
  rewrite [scalar_step p neox ops t 44 _ _ s7 s8 (by cases neox <;> decide)
    (by simp [s7, setReg, advance]) e8]
  rewrite [scalar_step p neox ops t 45 _ _ s8 s9 (by cases neox <;> decide)
    (by simp [s8, setReg, advance]) e9]
  rewrite [scalar_step p neox ops t 46 _ _ s9 s10 (by cases neox <;> decide)
    (by simp [s9, written, advance]) e10]
  rfl


#print axioms query_pair_cycle
#print axioms key_pair_cycle
end LarkNativeRope
