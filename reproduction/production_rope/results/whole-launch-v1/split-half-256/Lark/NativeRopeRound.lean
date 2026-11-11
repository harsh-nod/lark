import Lark.NativeRopeHeaderFrame
import Lark.NativeRopePairFrame

/-! Complete actual 23-instruction native loop rounds, including the source
branch, cache/header, both in-place stores, increment and loop-back jump. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def rotated (ops : Ops α) (input : Nat → Nat → α) (buffer row pair : Nat)
    (neox imaginary : Bool) : α :=
  let x := input buffer (address buffer row pair neox false)
  let y := input buffer (address buffer row pair neox true)
  let c := ops.fromHalf (input 2 (cacheCos row pair))
  let sn := ops.fromHalf (input 2 (cacheSin row pair))
  ops.toHalf (if imaginary then pairImaginary ops x y c sn else pairReal ops x y c sn)

def queryBody (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) : State α :=
  queryPairAfter ops t (address 0 row pair neox false) (address 0 row pair neox true)
    (input 0 (address 0 row pair neox false)) (input 0 (address 0 row pair neox true))
    (ops.fromHalf (input 2 (cacheCos row pair))) (ops.fromHalf (input 2 (cacheSin row pair)))
    (queryHeaderAfter ops input neox row pair t s)

def queryRound (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) : State α :=
  advance (setIndex (queryBody ops input neox row pair t s) t 1 ((pair + 512 : Nat) : Int) 24) t 2

theorem query_round_cycle (p : Shape) (neox : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row pair t extra : Nat) (s : State α)
    (hr : row < p.rows) (hi : pair < 2048) (hp : s.pc t = 2)
    (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 1 = some (pair : Int))
    (hcacheCos : s.memory (globalCell 2 (cacheCos row pair)) = some (input 2 (cacheCos row pair)))
    (hcacheSin : s.memory (globalCell 2 (cacheSin row pair)) = some (input 2 (cacheSin row pair)))
    (hx : s.memory (globalCell 0 (address 0 row pair neox false)) =
      some (input 0 (address 0 row pair neox false)))
    (hy : s.memory (globalCell 0 (address 0 row pair neox true)) =
      some (input 0 (address 0 row pair neox true))) :
    runLane ops (layout p) (geometry p) (program neox) t (extra + 23) s =
      runLane ops (layout p) (geometry p) (program neox) t extra
        (queryRound ops input neox row pair t s) := by
  let h := queryHeaderAfter ops input neox row pair t s
  let body := queryBody ops input neox row pair t s
  let inc := setIndex body t 1 ((pair + 512 : Nat) : Int) 24
  obtain ⟨hpc, hrow, hpair, hixa, hixb, hc, hs⟩ := query_header_ready ops input neox row pair t s h0 h1
  have ha := address_bound p 0 row pair neox false hr hi
  have hb := address_bound p 0 row pair neox true hr hi
  have hmx : h.memory (globalCell 0 (address 0 row pair neox false)) =
      some (input 0 (address 0 row pair neox false)) := hx
  have hmy : h.memory (globalCell 0 (address 0 row pair neox true)) =
      some (input 0 (address 0 row pair neox true)) := hy
  have hbodypc : body.pc t = 23 := by simp [body, queryBody, queryPairAfter, written, advance]
  have hbodyindex : body.indices t 1 = some (pair : Int) := hpair
  have hinc := eval_nat_add (geometry p) t body (.ivar 1) (.const 512)
    pair 512 hbodyindex (by rfl) (by omega)
  have e1 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 1 24
    (.add (.ivar 1) (.const 512)) body _ hinc (by omega)
  change execute _ _ _ _ _ body = some inc at e1
  have e2 : execute ops (layout p) (geometry p) t (.jump 2) inc =
      some (queryRound ops input neox row pair t s) := rfl
  rewrite [query_header_cycle p neox ops input row pair t (extra + 12) s hr hi hp h0 h1 hcacheCos hcacheSin]
  rewrite [query_pair_cycle p neox ops t (address 0 row pair neox false) (address 0 row pair neox true) (extra + 2)
    (input 0 (address 0 row pair neox false)) (input 0 (address 0 row pair neox true))
    (ops.fromHalf (input 2 (cacheCos row pair))) (ops.fromHalf (input 2 (cacheSin row pair))) h hpc ha hb hixa hixb hmx hmy hc hs]
  change runLane ops (layout p) (geometry p) (program neox) t (extra + 2) body =
    runLane ops (layout p) (geometry p) (program neox) t extra (queryRound ops input neox row pair t s)
  rewrite [scalar_step p neox ops t 23 _ _ body inc (by cases neox <;> decide) hbodypc e1]
  rewrite [scalar_step p neox ops t 24 _ _ inc _ (by cases neox <;> decide)
    (by simp [inc, setIndex, LarkReduction.setIndex, advance]) e2]
  rfl

#print axioms query_round_cycle

def keyBody (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) : State α :=
  keyPairAfter ops t (address 1 row pair neox false) (address 1 row pair neox true)
    (input 1 (address 1 row pair neox false)) (input 1 (address 1 row pair neox true))
    (ops.fromHalf (input 2 (cacheCos row pair))) (ops.fromHalf (input 2 (cacheSin row pair)))
    (keyHeaderAfter ops input neox row pair t s)

def keyRound (ops : Ops α) (input : Nat → Nat → α) (neox : Bool)
    (row pair t : Nat) (s : State α) : State α :=
  advance (setIndex (keyBody ops input neox row pair t s) t 10 ((pair + 512 : Nat) : Int) 48) t 26

theorem key_round_cycle (p : Shape) (neox : Bool) (ops : Ops α)
    (input : Nat → Nat → α) (row pair t extra : Nat) (s : State α)
    (hr : row < p.rows) (hi : pair < 512) (hp : s.pc t = 26)
    (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 10 = some (pair : Int))
    (hcacheCos : s.memory (globalCell 2 (cacheCos row pair)) = some (input 2 (cacheCos row pair)))
    (hcacheSin : s.memory (globalCell 2 (cacheSin row pair)) = some (input 2 (cacheSin row pair)))
    (hx : s.memory (globalCell 1 (address 1 row pair neox false)) =
      some (input 1 (address 1 row pair neox false)))
    (hy : s.memory (globalCell 1 (address 1 row pair neox true)) =
      some (input 1 (address 1 row pair neox true))) :
    runLane ops (layout p) (geometry p) (program neox) t (extra + 23) s =
      runLane ops (layout p) (geometry p) (program neox) t extra
        (keyRound ops input neox row pair t s) := by
  let h := keyHeaderAfter ops input neox row pair t s
  let body := keyBody ops input neox row pair t s
  let inc := setIndex body t 10 ((pair + 512 : Nat) : Int) 48
  obtain ⟨hpc, hrow, hpair, hixa, hixb, hc, hs⟩ := key_header_ready ops input neox row pair t s h0 h1
  have ha := address_bound p 1 row pair neox false hr hi
  have hb := address_bound p 1 row pair neox true hr hi
  have hmx : h.memory (globalCell 1 (address 1 row pair neox false)) =
      some (input 1 (address 1 row pair neox false)) := hx
  have hmy : h.memory (globalCell 1 (address 1 row pair neox true)) =
      some (input 1 (address 1 row pair neox true)) := hy
  have hbodypc : body.pc t = 47 := by simp [body, keyBody, keyPairAfter, written, advance]
  have hbodyindex : body.indices t 10 = some (pair : Int) := hpair
  have hinc := eval_nat_add (geometry p) t body (.ivar 10) (.const 512)
    pair 512 hbodyindex (by rfl) (by omega)
  have e1 := LarkReduction.execute_index_of ops (layout p) (geometry p) t 10 48
    (.add (.ivar 10) (.const 512)) body _ hinc (by omega)
  change execute _ _ _ _ _ body = some inc at e1
  have e2 : execute ops (layout p) (geometry p) t (.jump 26) inc =
      some (keyRound ops input neox row pair t s) := rfl
  rewrite [key_header_cycle p neox ops input row pair t (extra + 12) s hr hi hp h0 h1 hcacheCos hcacheSin]
  rewrite [key_pair_cycle p neox ops t (address 1 row pair neox false) (address 1 row pair neox true) (extra + 2)
    (input 1 (address 1 row pair neox false)) (input 1 (address 1 row pair neox true))
    (ops.fromHalf (input 2 (cacheCos row pair))) (ops.fromHalf (input 2 (cacheSin row pair))) h hpc ha hb hixa hixb hmx hmy hc hs]
  change runLane ops (layout p) (geometry p) (program neox) t (extra + 2) body =
    runLane ops (layout p) (geometry p) (program neox) t extra (keyRound ops input neox row pair t s)
  rewrite [scalar_step p neox ops t 47 _ _ body inc (by cases neox <;> decide) hbodypc e1]
  rewrite [scalar_step p neox ops t 48 _ _ inc _ (by cases neox <;> decide)
    (by simp [inc, setIndex, LarkReduction.setIndex, advance]) e2]
  rfl

#print axioms key_round_cycle

end LarkNativeRope
