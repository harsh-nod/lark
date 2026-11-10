import Lark.DotMap
import Lark.RowSoftmax

/-! Checked batched/grouped QK-transpose and probability/V addresses. -/
namespace LarkAttention
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

structure Shape where
  kvHeads : Nat
  groups : Nat
  seq : Nat
  dim : Nat
  scale : Nat
  kvPos : 0<kvHeads
  groupsPos : 0<groups
  seqPos : 0<seq
  dimPos : 0<dim
  scalePos : 0<scale
  scaleSquare : scale*scale=dim
  qBound : (kvHeads*groups)*(seq*dim)<2147483648
  kvBound : kvHeads*(seq*dim)<2147483648
  scoreBound : (kvHeads*groups)*(seq*seq)<2147483648

def heads (s : Shape) : Nat := s.kvHeads*s.groups
def rowCells (s : Shape) : Nat := s.seq*s.dim
def qCells (s : Shape) : Nat := heads s*rowCells s
def kvCells (s : Shape) : Nat := s.kvHeads*rowCells s
def scores (s : Shape) : Nat := heads s*(s.seq*s.seq)
theorem heads_pos (s : Shape) : 0<heads s := Nat.mul_pos s.kvPos s.groupsPos
theorem row_pos (s : Shape) : 0<rowCells s := Nat.mul_pos s.seqPos s.dimPos
theorem row_bound (s : Shape) : rowCells s<2147483648 :=
  LarkReduction.k_bound (heads s) (rowCells s) (heads_pos s) s.qBound
theorem seq_bound (s : Shape) : s.seq<2147483648 :=
  LarkReduction.k_bound s.dim s.seq s.dimPos (by simpa [rowCells,Nat.mul_comm] using row_bound s)
theorem dim_bound (s : Shape) : s.dim<2147483648 :=
  LarkReduction.k_bound s.seq s.dim s.seqPos (row_bound s)
theorem heads_bound (s : Shape) : heads s<2147483648 :=
  LarkReduction.k_bound (rowCells s) (heads s) (row_pos s) (by simpa [Nat.mul_comm] using s.qBound)
theorem groups_bound (s : Shape) : s.groups<2147483648 :=
  LarkReduction.k_bound s.kvHeads s.groups s.kvPos (heads_bound s)

def headIndex (block groups : Nat) : Index :=
  .div (.div (.ivar 0) (.const (block : Int))) (.const (groups : Int))
def kvIndex (s : Shape) (block : Nat) (row col : Index) : Index :=
  .add (.mul (headIndex block s.groups) (.const (rowCells s : Int)))
    (.add (.mul row (.const (s.dim : Int))) col)
def kvAddress (s : Shape) (block t row col : Nat) : Nat :=
  (t/block/s.groups)*rowCells s+(row*s.dim+col)

theorem kv_address_bound (s : Shape) (block t row col : Nat) (hp : 0<block)
    (ht : t<heads s*block) (hr : row<s.seq) (hc : col<s.dim) :
    kvAddress s block t row col<kvCells s := by
  have hh : t/block<heads s := (Nat.div_lt_iff_lt_mul hp).mpr ht
  have hk : t/block/s.groups<s.kvHeads := (Nat.div_lt_iff_lt_mul s.groupsPos).mpr hh
  have hi:=LarkReduction.address_bound s.seq s.dim row col hr hc
  exact LarkReduction.address_bound s.kvHeads (rowCells s) _ _ hk hi

theorem kv_eval (s : Shape) (block : Nat) (ri ci : Index) (g : Geometry) (t row col : Nat)
    (state : State α) (hi : state.indices t 0=some (t : Int))
    (hrow : evalIndex g t state ri=some (row : Int)) (hcol : evalIndex g t state ci=some (col : Int))
    (hp : 0<block) (ht : t<heads s*block) (hb : heads s*block<2147483648)
    (hr : row<s.seq) (hc : col<s.dim) :
    evalIndex g t state (kvIndex s block ri ci)=some ((kvAddress s block t row col : Nat) : Int) := by
  have hblock:=LarkReduction.k_bound (heads s) block (heads_pos s) hb
  have hhead:=LarkMatrix.eval_div_nat g t state (.ivar 0) (.const (block : Int)) t block hi
    (LarkReduction.int32_cast block hblock) (by omega)
  have hkv:=LarkMatrix.eval_div_nat g t state (.div (.ivar 0) (.const (block : Int)))
    (.const (s.groups : Int)) (t/block) s.groups hhead
    (LarkReduction.int32_cast s.groups (groups_bound s)) s.groupsPos
  have hfinal:=kv_address_bound s block t row col hp ht hr hc
  have hinner:=LarkReduction.address_bound s.seq s.dim row col hr hc
  have hbase : (t/block/s.groups)*rowCells s<2147483648 := by
    have hbound : kvCells s<2147483648 := s.kvBound
    unfold kvAddress at hfinal
    omega
  have hrmul : row*s.dim<2147483648 := by
    have hh:=row_bound s
    change row*s.dim+col<rowCells s at hinner
    omega
  have hisum : row*s.dim+col<2147483648 := by
    have hh:=row_bound s
    change row*s.dim+col<rowCells s at hinner
    omega
  have hfull : kvAddress s block t row col<2147483648 := by
    have hh : kvCells s<2147483648 := s.kvBound
    omega
  have hebase:=LarkMatrix.eval_mul_nat g t state (headIndex block s.groups) (.const (rowCells s : Int))
    (t/block/s.groups) (rowCells s) hkv (LarkReduction.int32_cast _ (row_bound s)) hbase
  have hermul:=LarkMatrix.eval_mul_nat g t state ri (.const (s.dim : Int)) row s.dim hrow
    (LarkReduction.int32_cast _ (dim_bound s)) hrmul
  have heinner:=LarkMatrix.eval_add_nat g t state (.mul ri (.const (s.dim : Int))) ci
    (row*s.dim) col hermul hcol hisum
  exact LarkMatrix.eval_add_nat g t state (.mul (headIndex block s.groups) (.const (rowCells s : Int)))
    (.add (.mul ri (.const (s.dim : Int))) ci) ((t/block/s.groups)*rowCells s) (row*s.dim+col)
    hebase heinner hfull

def scoreLeft (s : Shape) : LarkDot.Profile :=
  LarkMatrix.batchProfile (heads s) s.seq s.seq s.dim (heads_pos s) s.seqPos s.seqPos
    s.scoreBound s.qBound (by rw [Nat.mul_comm s.dim s.seq];exact s.qBound)
def scoreBase (s : Shape) : LarkDot.Profile :=
  { scoreLeft s with
    bSize:=kvCells s
    bIndex:=kvIndex s (s.seq*s.seq) (.mod (.ivar 0) (.const (s.seq : Int))) (.ivar 1)
    bAddress:=fun t j=>kvAddress s (s.seq*s.seq) t (t%s.seq) j
    bBound:=fun t j ht hj=>kv_address_bound s (s.seq*s.seq) t (t%s.seq) j
      (Nat.mul_pos s.seqPos s.seqPos) ht (Nat.mod_lt t s.seqPos) hj
    bEval:=fun _ g t j state hi hj ht hk=>kv_eval s (s.seq*s.seq)
      (.mod (.ivar 0) (.const (s.seq : Int))) (.ivar 1) g t (t%s.seq) j state hi
      (LarkMatrix.eval_mod_nat g t state (.ivar 0) (.const (s.seq : Int)) t s.seq hi
        (LarkReduction.int32_cast _ (seq_bound s)) s.seqPos) hj
      (Nat.mul_pos s.seqPos s.seqPos) ht s.scoreBound (Nat.mod_lt t s.seqPos) hk }
def scoreProfile (s : Shape) : LarkDotMap.Profile where
  toProfile:=scoreBase s
  aHalf:=true
  bHalf:=true
  post:=.bin .div .input (.lit (s.scale : Int) 1)
  validPost:=by simp [LarkPointwise.Valid]

def valueLeft (s : Shape) : LarkDot.Profile :=
  LarkMatrix.batchProfile (heads s) s.seq s.dim s.seq (heads_pos s) s.seqPos s.dimPos
    s.qBound s.scoreBound s.qBound
def valueBase (s : Shape) : LarkDot.Profile :=
  { valueLeft s with
    bSize:=kvCells s
    bIndex:=kvIndex s (rowCells s) (.ivar 1) (.mod (.ivar 0) (.const (s.dim : Int)))
    bAddress:=fun t j=>kvAddress s (rowCells s) t j (t%s.dim)
    bBound:=fun t j ht hj=>kv_address_bound s (rowCells s) t j (t%s.dim)
      (row_pos s) ht hj (Nat.mod_lt t s.dimPos)
    bEval:=fun _ g t j state hi hj ht hk=>kv_eval s (rowCells s) (.ivar 1)
      (.mod (.ivar 0) (.const (s.dim : Int))) g t j (t%s.dim) state hi hj
      (LarkMatrix.eval_mod_nat g t state (.ivar 0) (.const (s.dim : Int)) t s.dim hi
        (LarkReduction.int32_cast _ (dim_bound s)) s.dimPos)
      (row_pos s) ht s.qBound hk (Nat.mod_lt t s.dimPos) }
def valueProfile (s : Shape) : LarkDotMap.Profile where
  toProfile:=valueBase s
  aHalf:=false
  bHalf:=true
  post:=.un .toHalf .input
  validPost:=by trivial

def softmaxShape (s : Shape) : LarkRowSoftmax.Shape :=
  ⟨heads s*s.seq,s.seq,Nat.mul_pos (heads_pos s) s.seqPos,s.seqPos,
    by rw [Nat.mul_assoc];exact s.scoreBound⟩
theorem softmax_total (s : Shape) : LarkRowSoftmax.total (softmaxShape s)=scores s := by
  simp [LarkRowSoftmax.total,softmaxShape,scores,Nat.mul_assoc]

#print axioms kv_eval
end LarkAttention
