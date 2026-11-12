import Lark.NativeAwqGemmGlobal

/-! Full scalar/matrix instruction template of the independently adapted
FP16 AWQ kernel. Source-instance equality is checked separately; execution
and mathematical correctness are not asserted by a program definition.
-/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false

abbrev Instruction := LarkMFMA.Instr
def c (n : Nat) : Index := .const (n : Int)
def v (n : Nat) : Index := .ivar n
def ix (r : Nat) (value : Index) : Instruction := .scalar (.index r value)
def put (r : Nat) (value : Expr) : Instruction := .scalar (.assign r value)
def branch (test : Predicate) (target : Nat) : Instruction := .scalar (.branch test target)
def jump (target : Nat) : Instruction := .scalar (.jump target)
def blockBarrier : Instruction := .scalar (.barrier .block)

def banks (p : Shape) : Nat := tileN p/16
def whilePC (p : Shape) : Nat := 14+4*banks p
def firstBarrier (p : Shape) : Nat := 15+4*banks p
def middleBarrier (p : Shape) : Nat := 38+4*banks p
def outputPC (p : Shape) : Nat := 49+14*banks p
def haltPC (p : Shape) : Nat := 49+22*banks p

def indexInstructions (p : Shape) : List Instruction :=
  [ix 0 .tid,
   ix 1 (.mod (v 0) (c 32)),
   ix 2 (.div (v 0) (c 32)),
   ix 3 .bid,
   ix 4 (.div (v 3) (c (columnTiles p))),
   ix 5 (.mod (v 3) (c (columnTiles p))),
   ix 6 (.add (.add (.mul (v 4) (c 16)) (.mul (v 2) (c 8))) (.div (v 1) (c 4))),
   ix 7 (.mul (.mod (v 1) (c 4)) (c 8)),
   ix 8 (.add (.mul (.add (.mul (v 2) (c 8)) (.div (v 1) (c 4))) (c 40)) (v 7))] ++
  (List.range 4).map (fun e =>
    ix (9+e) (.add (.add (.mul (v 4) (c 16)) (.mul (.div (v 0) (c 16)) (c 4))) (c e)))

def initialInstructions (p : Shape) : List Instruction :=
  indexInstructions p ++
  (List.range (4*banks p)).map (fun r => put r (.lit 0 1)) ++
  [ix 13 (c 0),branch (.lt (v 13) (c (p.k/32))) (outputPC p),blockBarrier]

def aStageIndex : Index := .add (v 8) (v 14)
def aGlobalIndex (p : Shape) : Index :=
  .add (.add (.add (.mul (v 6) (c p.k)) (.mul (v 13) (c 32))) (v 7)) (v 14)
def bRowIndex (p : Shape) : Index :=
  .add (.add (.mul (v 2) (c (256/tileN p))) (.div (v 1) (c (tileN p/8))))
    (.mul (v 15) (c (512/tileN p)))
def bColIndex (p : Shape) : Index := .mul (.mod (v 1) (c (tileN p/8))) (c 8)
def bStageIndex (p : Shape) : Index := .add (.add (.mul (v 16) (c (tileN p+8))) (v 17)) (v 18)
def bGlobalIndex (p : Shape) : Index :=
  .add (.add (.add (.mul (.add (.mul (v 13) (c 32)) (v 16)) (c p.n))
    (.mul (v 5) (c (tileN p)))) (v 17)) (v 18)
def increment (r : Nat) : Instruction := ix r (.add (v r) (c 1))

def stagingInstructions (p : Shape) : List Instruction :=
  [ix 14 (c 0),
   branch (.lt (v 6) (c p.m)) (firstBarrier p+8),
   branch (.lt (v 14) (c 8)) (firstBarrier p+7),
   .scalar (.store .shared 0 aStageIndex (.load .global 0 (aGlobalIndex p))),
   increment 14,jump (firstBarrier p+3),jump (firstBarrier p+12),
   branch (.lt (v 14) (c 8)) (firstBarrier p+12),
   .scalar (.store .shared 0 aStageIndex (.un .toHalf (.lit 0 1))),
   increment 14,jump (firstBarrier p+8),
   ix 15 (c 0),branch (.lt (v 15) (c (banks p))) (middleBarrier p),
   ix 16 (bRowIndex p),ix 17 (bColIndex p),ix 18 (c 0),
   branch (.lt (v 18) (c 8)) (firstBarrier p+21),
   .scalar (.store .shared 1 (bStageIndex p) (.load .global 1 (bGlobalIndex p))),
   increment 18,jump (firstBarrier p+17),increment 15,jump (firstBarrier p+13),blockBarrier]

def leftBase (p : Shape) (half : Nat) : Nat := if half=0 then 4*banks p else 8*banks p+4
def rightBase (p : Shape) (half bank : Nat) : Nat := leftBase p half+4+bank*4
def aFragmentIndex (half e : Nat) : Index :=
  .add (.add (.add (.mul (.mod (v 0) (c 16)) (c 40)) (c (half*16)))
    (.mul (.div (v 0) (c 16)) (c 4))) (c e)
def bFragmentIndex (p : Shape) (half bank e : Nat) : Index :=
  .add (.add (.mul (.add (.add (c (half*16)) (.mul (.div (v 0) (c 16)) (c 4))) (c e))
    (c (tileN p+8))) (c (bank*16))) (.mod (v 0) (c 16))

def matrixPass (p : Shape) (half : Nat) : List Instruction :=
  (List.range 4).map (fun e => put (leftBase p half+e) (.load .shared 0 (aFragmentIndex half e))) ++
  (List.range (banks p)).flatMap (fun bank =>
    (List.range 4).map (fun e => put (rightBase p half bank+e) (.load .shared 1 (bFragmentIndex p half bank e))) ++
      [.mfma (bank*4) (leftBase p half) (rightBase p half bank) (bank*4)])

def outputIndex (p : Shape) (bank e : Nat) : Index :=
  .add (.add (.add (.mul (v (9+e)) (c p.n)) (.mul (v 5) (c (tileN p)))) (c (bank*16)))
    (.mod (v 0) (c 16))
def outputInstructions (p : Shape) : List Instruction :=
  (List.range (banks p)).flatMap (fun bank =>
    (List.range 4).flatMap (fun e =>
      [branch (.lt (v (9+e)) (c p.m)) (outputPC p+bank*8+e*2+2),
       .scalar (.store .global 2 (outputIndex p bank e) (.un .toHalf (.reg (bank*4+e))))]))

def program (p : Shape) : List Instruction :=
  initialInstructions p ++ stagingInstructions p ++ matrixPass p 0 ++ matrixPass p 1 ++
    [increment 13,jump (whilePC p)] ++ outputInstructions p ++ [.scalar .halt]

theorem banks_cases (p : Shape) : banks p=4 ∨ banks p=8 := by
  rcases tile_cases p with h | h
  · exact Or.inl (by simp [banks,h])
  · exact Or.inr (by simp [banks,h])

theorem initial_length (p : Shape) : (initialInstructions p).length=16+4*banks p := by
  simp [initialInstructions,indexInstructions,Nat.add_assoc] <;> omega

theorem index_instructions_length (p : Shape) : (indexInstructions p).length=13 := by
  simp [indexInstructions]

theorem staging_length (p : Shape) : (stagingInstructions p).length=23 := rfl

#print axioms banks_cases
#print axioms initial_length
#print axioms index_instructions_length
#print axioms staging_length
end LarkNativeAwqGemm
