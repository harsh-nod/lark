import Lark.DotLoop

/-! Row-major scalar GEMM: index/address proofs instantiate the real counted loop. -/
namespace LarkMatrix
open LarkNonlinear LarkReduction
set_option maxRecDepth 4000
set_option maxHeartbeats 20000000

def leftIndex (n k : Nat) : Index :=
  .add (.mul (.div (.ivar 0) (.const (n : Int))) (.const (k : Int))) (.ivar 1)
def rightIndex (n : Nat) : Index :=
  .add (.mul (.ivar 1) (.const (n : Int))) (.mod (.ivar 0) (.const (n : Int)))
def leftAddress (n k t j : Nat) : Nat := (t/n)*k+j
def rightAddress (n t j : Nat) : Nat := j*n+t%n

theorem left_bound (m n k t j : Nat) (hn : 0<n) (ht : t<m*n) (hj : j<k) :
    leftAddress n k t j < m*k := by
  have hrow : t/n<m := (Nat.div_lt_iff_lt_mul hn).mpr ht
  exact address_bound m k (t/n) j hrow hj

theorem right_bound (n k t j : Nat) (hn : 0<n) (hj : j<k) :
    rightAddress n t j < k*n := by
  exact address_bound k n j (t%n) hj (Nat.mod_lt t hn)

theorem eval_div_nat (g : Geometry) (t : Nat) (s : State α) (a b : Index)
    (x y : Nat) (ha : evalIndex g t s a = some (x : Int))
    (hb : evalIndex g t s b = some (y : Int)) (hy : 0<y) :
    evalIndex g t s (.div a b) = some ((x/y : Nat) : Int) := by
  have h0 : ¬ ((y : Int)=0 ∨ (x : Int)<0 ∨ (y : Int)<0) := by omega
  simp only [evalIndex, ha, hb, bind, pure, Option.bind, h0, ↓reduceIte]
  exact congrArg some (Int.ofNat_ediv x y).symm

theorem eval_mod_nat (g : Geometry) (t : Nat) (s : State α) (a b : Index)
    (x y : Nat) (ha : evalIndex g t s a = some (x : Int))
    (hb : evalIndex g t s b = some (y : Int)) (hy : 0<y) :
    evalIndex g t s (.mod a b) = some ((x%y : Nat) : Int) := by
  have h0 : ¬ ((y : Int)=0 ∨ (x : Int)<0 ∨ (y : Int)<0) := by omega
  simp only [evalIndex, ha, hb, bind, pure, Option.bind, h0, ↓reduceIte]
  exact congrArg some (Int.ofNat_emod x y).symm

theorem left_eval (g : Geometry) (m n k t j : Nat) (s : State α)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hm : 0<m) (hn : 0<n) (ht : t<m*n) (hj : j<k)
    (hnb : n<2147483648) (hb : m*k<2147483648) :
    evalIndex g t s (leftIndex n k) = some ((leftAddress n k t j : Nat) : Int) := by
  have ha := left_bound m n k t j hn ht hj
  have hk := k_bound m k hm hb
  have hdiv := eval_div_nat g t s (.ivar 0) (.const (n : Int)) t n hi
    (int32_cast n hnb) hn
  have hmul : evalIndex g t s (.mul (.div (.ivar 0) (.const (n : Int)))
      (.const (k : Int))) = some (((t/n)*k : Nat) : Int) :=
    eval_mul_of g t s _ _ ((t/n : Nat) : Int) (k : Int) (((t/n)*k : Nat) : Int)
      hdiv (int32_cast k hk) (Eq.trans
        (congrArg int32 (Int.natCast_mul (t/n) k).symm)
        (int32_cast ((t/n)*k) (by unfold leftAddress at ha; omega)))
  exact eval_add_of g t s _ _ (((t/n)*k : Nat) : Int) (j : Int)
    ((leftAddress n k t j : Nat) : Int) hmul hij (Eq.trans
      (congrArg int32 (Int.natCast_add ((t/n)*k) j).symm)
      (int32_cast (leftAddress n k t j) (by omega)))

theorem right_eval (g : Geometry) (n k t j : Nat) (s : State α)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hn : 0<n) (hj : j<k) (hnb : n<2147483648) (hb : k*n<2147483648) :
    evalIndex g t s (rightIndex n) = some ((rightAddress n t j : Nat) : Int) := by
  have ha := right_bound n k t j hn hj
  have hmod := eval_mod_nat g t s (.ivar 0) (.const (n : Int)) t n hi
    (int32_cast n hnb) hn
  have hmul : evalIndex g t s (.mul (.ivar 1) (.const (n : Int))) =
      some ((j*n : Nat) : Int) :=
    eval_mul_of g t s _ _ (j : Int) (n : Int) ((j*n : Nat) : Int) hij
      (int32_cast n hnb) (Eq.trans (congrArg int32 (Int.natCast_mul j n).symm)
        (int32_cast (j*n) (by unfold rightAddress at ha; omega)))
  exact eval_add_of g t s _ _ ((j*n : Nat) : Int) ((t%n : Nat) : Int)
    ((rightAddress n t j : Nat) : Int) hmul hmod (Eq.trans
      (congrArg int32 (Int.natCast_add (j*n) (t%n)).symm)
      (int32_cast (rightAddress n t j) (by omega)))

def profile (m n k : Nat) (hm : 0<m) (hn : 0<n)
    (hnb : n<2147483648) (ha : m*k<2147483648) (hb : k*n<2147483648) : LarkDot.Profile :=
  { n := m*n, k := k, aSize := m*k, bSize := k*n,
    aIndex := leftIndex n k, bIndex := rightIndex n,
    aAddress := leftAddress n k, bAddress := rightAddress n,
    aBound := fun t j ht hj => left_bound m n k t j hn ht hj,
    bBound := fun t j _ hj => right_bound n k t j hn hj,
    aEval := fun _ g t j s hi hij ht hj => left_eval g m n k t j s hi hij hm hn ht hj hnb ha,
    bEval := fun _ g t j s hi hij _ hj => right_eval g n k t j s hi hij hn hj hnb hb }

theorem correct (ops : Ops α) (m n k w : Nat) (hm : 0<m) (hn : 0<n) (hk : 0<k)
    (hnb : n<2147483648) (ha : m*k<2147483648) (hb : k*n<2147483648)
    (hc : m*n<2147483648) (hw : 0<w) :
    let p := profile m n k hm hn hnb ha hb
    Correct ops (LarkDot.layout p) (LarkDot.geometry p w) (LarkDot.fuel p)
      (LarkDot.program p) (LarkDot.matrixSpec ops p) := by
  exact LarkDot.matrix_correct ops (profile m n k hm hn hnb ha hb) w
    (Nat.mul_pos hm hn) hk ⟨hc, k_bound m k hm ha⟩ hw

def batchLeftIndex (m n k : Nat) : Index :=
  .add (.mul (.div (.ivar 0) (.const ((m*n : Nat) : Int))) (.const ((m*k : Nat) : Int)))
    (.add (.mul (.mod (.div (.ivar 0) (.const (n : Int))) (.const (m : Int)))
      (.const (k : Int))) (.ivar 1))
def batchRightIndex (m n k : Nat) : Index :=
  .add (.mul (.div (.ivar 0) (.const ((m*n : Nat) : Int))) (.const ((k*n : Nat) : Int)))
    (rightIndex n)
def batchLeftAddress (m n k t j : Nat) : Nat := (t/(m*n))*(m*k)+((t/n)%m)*k+j
def batchRightAddress (m n k t j : Nat) : Nat := (t/(m*n))*(k*n)+(j*n+t%n)

theorem batch_left_bound (b m n k t j : Nat) (hm : 0<m) (hn : 0<n)
    (ht : t<b*(m*n)) (hj : j<k) : batchLeftAddress m n k t j < b*(m*k) := by
  have hbatch : t/(m*n)<b := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hm hn)).mpr ht
  have hrow := Nat.mod_lt (t/n) hm
  have hinner := address_bound m k ((t/n)%m) j hrow hj
  have houter := address_bound b (m*k) (t/(m*n)) (((t/n)%m)*k+j) hbatch hinner
  simpa [batchLeftAddress, Nat.add_assoc] using houter

theorem batch_right_bound (b m n k t j : Nat) (hm : 0<m) (hn : 0<n)
    (ht : t<b*(m*n)) (hj : j<k) : batchRightAddress m n k t j < b*(k*n) := by
  have hbatch : t/(m*n)<b := (Nat.div_lt_iff_lt_mul (Nat.mul_pos hm hn)).mpr ht
  have hinner : j*n+t%n<k*n := right_bound n k t j hn hj
  change (t/(m*n))*(k*n)+(j*n+t%n)<b*(k*n)
  exact address_bound b (k*n) (t/(m*n)) (j*n+t%n) hbatch hinner

theorem eval_mul_nat (g : Geometry) (t : Nat) (s : State α) (a b : Index)
    (x y : Nat) (ha : evalIndex g t s a = some (x : Int))
    (hb : evalIndex g t s b = some (y : Int)) (hxy : x*y<2147483648) :
    evalIndex g t s (.mul a b) = some ((x*y : Nat) : Int) :=
  eval_mul_of g t s a b (x : Int) (y : Int) ((x*y : Nat) : Int) ha hb
    (Eq.trans (congrArg int32 (Int.natCast_mul x y).symm) (int32_cast (x*y) hxy))

theorem eval_add_nat (g : Geometry) (t : Nat) (s : State α) (a b : Index)
    (x y : Nat) (ha : evalIndex g t s a = some (x : Int))
    (hb : evalIndex g t s b = some (y : Int)) (hxy : x+y<2147483648) :
    evalIndex g t s (.add a b) = some ((x+y : Nat) : Int) :=
  eval_add_of g t s a b (x : Int) (y : Int) ((x+y : Nat) : Int) ha hb
    (Eq.trans (congrArg int32 (Int.natCast_add x y).symm) (int32_cast (x+y) hxy))

theorem batch_left_eval (g : Geometry) (b m n k t j : Nat) (s : State α)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hb : 0<b) (hm : 0<m) (hn : 0<n) (ht : t<b*(m*n)) (hj : j<k)
    (hc : b*(m*n)<2147483648) (ha : b*(m*k)<2147483648) :
    evalIndex g t s (batchLeftIndex m n k) =
      some ((batchLeftAddress m n k t j : Nat) : Int) := by
  have hmn := k_bound b (m*n) hb hc
  have hmk := k_bound b (m*k) hb ha
  have hmb := k_bound n m hn (by simpa [Nat.mul_comm] using hmn)
  have hnb := k_bound m n hm hmn
  have hkb := k_bound m k hm hmk
  have haddr := batch_left_bound b m n k t j hm hn ht hj
  have hd := eval_div_nat g t s (.ivar 0) (.const ((m*n : Nat) : Int)) t (m*n)
    hi (int32_cast (m*n) hmn) (Nat.mul_pos hm hn)
  have houter := eval_mul_nat g t s _ (.const ((m*k : Nat) : Int)) (t/(m*n)) (m*k) hd (int32_cast (m*k) hmk)
    (by unfold batchLeftAddress at haddr; omega)
  have hr := eval_div_nat g t s (.ivar 0) (.const (n : Int)) t n hi (int32_cast n hnb) hn
  have hrm := eval_mod_nat g t s _ (.const (m : Int)) (t/n) m hr (int32_cast m hmb) hm
  have hinner := address_bound m k ((t/n)%m) j (Nat.mod_lt (t/n) hm) hj
  have hrk := eval_mul_nat g t s _ (.const (k : Int)) ((t/n)%m) k hrm (int32_cast k hkb)
    (by omega)
  have hsum := eval_add_nat g t s _ (.ivar 1) (((t/n)%m)*k) j hrk hij (by omega)
  have h := eval_add_nat g t s _ _ ((t/(m*n))*(m*k)) (((t/n)%m)*k+j) houter hsum
    (by unfold batchLeftAddress at haddr; omega)
  simpa only [batchLeftIndex, batchLeftAddress, Nat.add_assoc] using h

theorem batch_right_eval (g : Geometry) (b m n k t j : Nat) (s : State α)
    (hi : s.indices t 0 = some (t : Int)) (hij : s.indices t 1 = some (j : Int))
    (hb : 0<b) (hm : 0<m) (hn : 0<n) (ht : t<b*(m*n)) (hj : j<k)
    (hc : b*(m*n)<2147483648) (hba : b*(k*n)<2147483648) :
    evalIndex g t s (batchRightIndex m n k) =
      some ((batchRightAddress m n k t j : Nat) : Int) := by
  have hmn := k_bound b (m*n) hb hc
  have hkn := k_bound b (k*n) hb hba
  have hnb := k_bound m n hm hmn
  have haddr := batch_right_bound b m n k t j hm hn ht hj
  have hd := eval_div_nat g t s (.ivar 0) (.const ((m*n : Nat) : Int)) t (m*n)
    hi (int32_cast (m*n) hmn) (Nat.mul_pos hm hn)
  have houter := eval_mul_nat g t s _ (.const ((k*n : Nat) : Int)) (t/(m*n)) (k*n) hd (int32_cast (k*n) hkn)
    (by unfold batchRightAddress at haddr; omega)
  have hr := right_eval g n k t j s hi hij hn hj hnb hkn
  exact eval_add_nat g t s _ _ ((t/(m*n))*(k*n)) (j*n+t%n) houter hr (by unfold batchRightAddress at haddr; omega)

def batchProfile (b m n k : Nat) (hb : 0<b) (hm : 0<m) (hn : 0<n)
    (hc : b*(m*n)<2147483648) (ha : b*(m*k)<2147483648)
    (hba : b*(k*n)<2147483648) : LarkDot.Profile :=
  { n := b*(m*n), k := k, aSize := b*(m*k), bSize := b*(k*n),
    aIndex := batchLeftIndex m n k, bIndex := batchRightIndex m n k,
    aAddress := batchLeftAddress m n k, bAddress := batchRightAddress m n k,
    aBound := fun t j ht hj => batch_left_bound b m n k t j hm hn ht hj,
    bBound := fun t j ht hj => batch_right_bound b m n k t j hm hn ht hj,
    aEval := fun _ g t j s hi hij ht hj => batch_left_eval g b m n k t j s hi hij hb hm hn ht hj hc ha,
    bEval := fun _ g t j s hi hij ht hj => batch_right_eval g b m n k t j s hi hij hb hm hn ht hj hc hba }

#print axioms left_eval
#print axioms right_eval
#print axioms correct
#print axioms batch_left_eval
#print axioms batch_right_eval
end LarkMatrix
