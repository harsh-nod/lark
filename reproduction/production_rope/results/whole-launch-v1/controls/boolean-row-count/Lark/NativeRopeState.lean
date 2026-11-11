import Lark.NativeRopeAddress

/-! Scalar operational helpers for complete native in-place rotary execution. -/
namespace LarkNativeRope
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def globalCell (buffer offset : Nat) : Location := ⟨.global, 0, buffer, offset⟩
def setReg (s : State α) (t r : Nat) (v : α) (pc : Nat) : State α :=
  advance {s with regs := fun u q => if u = t ∧ q = r then some v else s.regs u q} t pc
def written (t pc : Nat) (loc : Location) (value : α) (s : State α) : State α :=
  advance { record s t loc true with
    memory := fun l => if l = loc then some value else s.memory l } t pc

theorem mutable_location (p : Shape) (t buffer offset : Nat) (write : Bool)
    (hb : buffer = 0 ∨ buffer = 1) (hi : offset < p.rows * width buffer) :
    location (layout p) (geometry p) t .global buffer (offset : Int) write =
      some (globalCell buffer offset) := by
  rcases hb with rfl | rfl <;> simp [width] at hi <;>
    simp [location, layout, globalCell, hi, show (Role.output == Role.input) = false from rfl]

theorem load_mutable (p : Shape) (ops : Ops α) (t buffer offset index : Nat)
    (s : State α) (value : α) (hb : buffer = 0 ∨ buffer = 1)
    (hi : offset < p.rows * width buffer) (hindex : s.indices t index = some (offset : Int))
    (hm : s.memory (globalCell buffer offset) = some value) :
    evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .global buffer (.ivar index))) s =
      some (ops.fromHalf value, record s t (globalCell buffer offset) false) := by
  simp only [evalExpr, evalIndex, hindex, mutable_location p t buffer offset false hb hi,
    hm, applyUnary, bind, pure, Option.bind]

theorem scalar_step (p : Shape) (neox : Bool) (ops : Ops α) (t pc extra : Nat)
    (i : Instr) (s next : State α) (hi : (program neox)[pc]? = some i) (hp : s.pc t = pc)
    (he : execute ops (layout p) (geometry p) t i s = some next) :
    runLane ops (layout p) (geometry p) (program neox) t (extra + 1) s =
      runLane ops (layout p) (geometry p) (program neox) t extra next := by
  have hparked : parked (program neox) s t = none := by
    cases i <;> simp_all [parked, execute]
  rewrite [runLane, hparked]
  simp only [hp, hi, bind, pure, Option.bind, he]

theorem execute_pure_of (ops : Ops α) (l : Layout) (g : Geometry) (t r pc : Nat)
    (e : Expr) (s : State α) (v : α) (he : evalExpr ops l g t e s = some (v, s))
    (hp : s.pc t + 1 = pc) :
    execute ops l g t (.assign r e) s = some (setReg s t r v pc) := by
  simp only [execute, he, hp, bind, pure, Option.bind]
  rfl

#print axioms mutable_location
#print axioms load_mutable
#print axioms scalar_step
#print axioms execute_pure_of
end LarkNativeRope
