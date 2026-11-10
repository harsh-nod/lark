import Lark.NativeAttentionState

/-! Actual checked index evaluation for the pinned source's accesses. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def initIndex : Index :=
  .add (.add (.ivar 2) (.mul (.add (.mul (.ivar 3) (.const 32)) (.ivar 1)) (.const 256))) (.ivar 4)
def globalIndex (row col : Nat) : Index :=
  .add (.add (.add (.ivar 2) (.mul (.ivar row) (.const 8192)))
    (.mul (.ivar 1) (.const 256))) (.ivar col)
def sharedIndex (col : Nat) : Index := .add (.mul (.ivar 1) (.const 256)) (.ivar col)

theorem init_store_code : program[7]? =
    some (.store .global 0 initIndex (.un .toHalf (.lit 0 1))) := rfl
theorem key_store_code : program[16]? = some
    (.store .shared 1 (sharedIndex 6) (.un .fromHalf (.load .global 2 (globalIndex 5 6)))) := rfl
theorem value_store_code : program[17]? = some
    (.store .shared 2 (sharedIndex 6) (.un .fromHalf (.load .global 3 (globalIndex 5 6)))) := rfl

theorem eval_init_index (p : Shape) (t tile col : Nat) (s : State α)
    (ht : t < p.groups * 32) (hi : tile < 4) (hc : col < 256)
    (hn : NativeIndices t s) (hrow : s.indices t 3 = some (tile : Int))
    (hcol : s.indices t 4 = some (col : Int)) :
    evalIndex (geometry p) t s initIndex = some ((globalAddress t tile col : Nat) : Int) := by
  have hf := global_address_int32 p t tile col ht hi hc
  have he : t / 32 * 32768 + (tile * 32 + t % 32) * 256 + col = globalAddress t tile col := by
    unfold globalAddress
    omega
  have hfull : t / 32 * 32768 + (tile * 32 + t % 32) * 256 + col < 2147483648 := by omega
  have h1 := LarkMatrix.eval_mul_nat (geometry p) t s (.ivar 3) (.const 32) tile 32
    hrow (by rfl) (by omega)
  have h2 := LarkMatrix.eval_add_nat (geometry p) t s (.mul (.ivar 3) (.const 32)) (.ivar 1)
    (tile * 32) (t % 32) h1 hn.2.1 (by omega)
  have h3 := LarkMatrix.eval_mul_nat (geometry p) t s
    (.add (.mul (.ivar 3) (.const 32)) (.ivar 1)) (.const 256)
    (tile * 32 + t % 32) 256 h2 (by rfl) (by omega)
  have h4 := LarkMatrix.eval_add_nat (geometry p) t s (.ivar 2)
    (.mul (.add (.mul (.ivar 3) (.const 32)) (.ivar 1)) (.const 256))
    (t / 32 * 32768) ((tile * 32 + t % 32) * 256) hn.2.2 h3 (by omega)
  have h5 := LarkMatrix.eval_add_nat (geometry p) t s
    (.add (.ivar 2) (.mul (.add (.mul (.ivar 3) (.const 32)) (.ivar 1)) (.const 256)))
    (.ivar 4) (t / 32 * 32768 + (tile * 32 + t % 32) * 256) col h4 hcol hfull
  exact h5.trans (congrArg (fun n : Nat => some (n : Int)) he)

theorem eval_global_index (p : Shape) (t tile col rowReg colReg : Nat) (s : State α)
    (ht : t < p.groups * 32) (hi : tile < 4) (hc : col < 256)
    (hn : NativeIndices t s) (hrow : s.indices t rowReg = some (tile : Int))
    (hcol : s.indices t colReg = some (col : Int)) :
    evalIndex (geometry p) t s (globalIndex rowReg colReg) =
      some ((globalAddress t tile col : Nat) : Int) := by
  have hf := global_address_int32 p t tile col ht hi hc
  have h1 := LarkMatrix.eval_mul_nat (geometry p) t s (.ivar rowReg) (.const 8192)
    tile 8192 hrow (by rfl) (by unfold globalAddress at hf; omega)
  have h2 := LarkMatrix.eval_mul_nat (geometry p) t s (.ivar 1) (.const 256)
    (t % 32) 256 hn.2.1 (by rfl) (by omega)
  have h3 := LarkMatrix.eval_add_nat (geometry p) t s (.ivar 2) (.mul (.ivar rowReg) (.const 8192))
    (t / 32 * 32768) (tile * 8192) hn.2.2 h1 (by unfold globalAddress at hf; omega)
  have h4 := LarkMatrix.eval_add_nat (geometry p) t s
    (.add (.ivar 2) (.mul (.ivar rowReg) (.const 8192))) (.mul (.ivar 1) (.const 256))
    (t / 32 * 32768 + tile * 8192) (t % 32 * 256) h3 h2 (by unfold globalAddress at hf; omega)
  exact LarkMatrix.eval_add_nat (geometry p) t s
    (.add (.add (.ivar 2) (.mul (.ivar rowReg) (.const 8192))) (.mul (.ivar 1) (.const 256)))
    (.ivar colReg) (t / 32 * 32768 + tile * 8192 + t % 32 * 256) col h4 hcol hf

theorem eval_shared_index (g : Geometry) (t reg col : Nat) (s : State α) (hc : col < 256)
    (hl : s.indices t 1 = some ((t % 32 : Nat) : Int))
    (hcol : s.indices t reg = some (col : Int)) :
    evalIndex g t s (sharedIndex reg) = some ((sharedAddress t col : Nat) : Int) := by
  have h1 := LarkMatrix.eval_mul_nat g t s (.ivar 1) (.const 256) (t % 32) 256 hl (by rfl) (by omega)
  exact LarkMatrix.eval_add_nat g t s (.mul (.ivar 1) (.const 256)) (.ivar reg)
    (t % 32 * 256) col h1 hcol (by omega)

theorem eval_counter (g : Geometry) (t reg n : Nat) (s : State α)
    (hn : s.indices t reg = some (n : Int)) (hb : n + 1 < 2147483648) :
    evalIndex g t s (.add (.ivar reg) (.const 1)) = some ((n + 1 : Nat) : Int) :=
  LarkMatrix.eval_add_nat g t s (.ivar reg) (.const 1) n 1 hn (by rfl) hb

#print axioms eval_init_index
#print axioms eval_global_index
end LarkNativeAttention
