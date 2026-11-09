import Lark.Matrix

/-! Valid square NCHW convolutions instantiate the already checked dot-loop machine. -/
namespace LarkConvolution
open LarkNonlinear LarkReduction LarkMatrix
set_option maxRecDepth 5000
set_option maxHeartbeats 20000000

def side (h k : Nat) : Nat := h-k+1
def inputIndex (ic : Index) (h k s : Nat) : Index :=
  .add (.add (.mul
    (.add (.add (.mul ic (.const (h : Int)))
      (.mod (.div (.ivar 0) (.const (s : Int))) (.const (s : Int))))
      (.mod (.div (.ivar 1) (.const (k : Int))) (.const (k : Int))))
    (.const (h : Int))) (.mod (.ivar 0) (.const (s : Int))))
    (.mod (.ivar 1) (.const (k : Int)))
def inputRow (h k s t j ch : Nat) : Nat := ch*h+(t/s)%s+(j/k)%k
def inputAddress (h k s t j ch : Nat) : Nat := inputRow h k s t j ch*h+t%s+j%k

theorem row_bound (cin h k s t j ch : Nat) (hk : 0<k) (hs : 0<s)
    (hshape : s+k=h+1) (hch : ch<cin) : inputRow h k s t j ch<cin*h := by
  have hy := Nat.mod_lt (t/s) hs
  have hky := Nat.mod_lt (j/k) hk
  have hoff : (t/s)%s+(j/k)%k<h := by omega
  have hrow := address_bound cin h ch ((t/s)%s+(j/k)%k) hch hoff
  simpa [inputRow,Nat.add_assoc] using hrow

theorem input_bound (cin h k s t j ch : Nat) (hk : 0<k) (hs : 0<s)
    (hshape : s+k=h+1) (hch : ch<cin) : inputAddress h k s t j ch<(cin*h)*h := by
  have hrow := row_bound cin h k s t j ch hk hs hshape hch
  have hx := Nat.mod_lt t hs
  have hkx := Nat.mod_lt j hk
  have hoff : t%s+j%k<h := by omega
  have haddr := address_bound (cin*h) h (inputRow h k s t j ch) (t%s+j%k) hrow hoff
  simpa [inputAddress,Nat.add_assoc] using haddr

theorem input_eval (g : Geometry) (cin h k s t j ch : Nat) (ic : Index) (st : State α)
    (hi : st.indices t 0=some (t : Int)) (hj : st.indices t 1=some (j : Int))
    (hic : evalIndex g t st ic=some (ch : Int)) (hk : 0<k) (hs : 0<s)
    (hshape : s+k=h+1) (hch : ch<cin) (ha : (cin*h)*h<2147483648) :
    evalIndex g t st (inputIndex ic h k s)=some ((inputAddress h k s t j ch : Nat) : Int) := by
  have hh : 0<h := by omega
  have hcin : 0<cin := by omega
  have hrow := row_bound cin h k s t j ch hk hs hshape hch
  have haddr := input_bound cin h k s t j ch hk hs hshape hch
  have hchh : cin*h<2147483648 :=
    k_bound h (cin*h) hh (by simpa [Nat.mul_comm] using ha)
  have hhb := k_bound cin h hcin hchh
  have hkb : k<2147483648 := by omega
  have hsb : s<2147483648 := by omega
  have hrowNat : ch*h+(t/s)%s+(j/k)%k<2147483648 := by
    unfold inputRow at hrow
    omega
  have haddrNat : inputRow h k s t j ch*h+t%s+j%k<2147483648 := by
    unfold inputAddress at haddr
    omega
  have htd := eval_div_nat g t st (.ivar 0) (.const (s : Int)) t s hi (int32_cast s hsb) hs
  have hty := eval_mod_nat g t st _ (.const (s : Int)) (t/s) s htd (int32_cast s hsb) hs
  have hjd := eval_div_nat g t st (.ivar 1) (.const (k : Int)) j k hj (int32_cast k hkb) hk
  have hjy := eval_mod_nat g t st _ (.const (k : Int)) (j/k) k hjd (int32_cast k hkb) hk
  have hcm := eval_mul_nat g t st ic (.const (h : Int)) ch h hic (int32_cast h hhb)
    (by unfold inputRow at hrow; omega)
  have hcy := eval_add_nat g t st _ _ (ch*h) ((t/s)%s) hcm hty
    (by unfold inputRow at hrow; omega)
  have hr := eval_add_nat g t st _ _ (ch*h+(t/s)%s) ((j/k)%k) hcy hjy (by omega)
  have hrm := eval_mul_nat g t st _ (.const (h : Int)) (inputRow h k s t j ch) h hr
    (int32_cast h hhb) (by unfold inputAddress at haddr; omega)
  have htx := eval_mod_nat g t st (.ivar 0) (.const (s : Int)) t s hi (int32_cast s hsb) hs
  have hjx := eval_mod_nat g t st (.ivar 1) (.const (k : Int)) j k hj (int32_cast k hkb) hk
  have hsum := eval_add_nat g t st _ _ (inputRow h k s t j ch*h) (t%s) hrm htx
    (by unfold inputAddress at haddr; omega)
  exact eval_add_nat g t st _ _ (inputRow h k s t j ch*h+t%s) (j%k) hsum hjx (by omega)

def denseChannel (k : Nat) : Index := .div (.ivar 1) (.const ((k*k : Nat) : Int))
def depthChannel (s : Nat) : Index := .div (.ivar 0) (.const ((s*s : Nat) : Int))

def denseProfile (cin cout h k : Nat) (hc : 0<cin) (ho : 0<cout) (hk : 0<k) (hkh : k≤h)
    (ha : (cin*h)*h<2147483648) (hb : cout*(cin*(k*k))<2147483648)
    (hn : cout*(side h k*side h k)<2147483648) : LarkDot.Profile := by
  let s := side h k
  have hs : 0<s := by dsimp [s,side]; omega
  have hshape : s+k=h+1 := by dsimp [s,side]; omega
  have hkk := k_bound cin (k*k) hc (k_bound cout (cin*(k*k)) ho hb)
  have hss := k_bound cout (s*s) ho hn
  exact {
    n := cout*(s*s), k := cin*(k*k), aSize := (cin*h)*h, bSize := cout*(cin*(k*k)),
    aIndex := inputIndex (denseChannel k) h k s,
    bIndex := leftIndex (s*s) (cin*(k*k)),
    aAddress := fun t j => inputAddress h k s t j (j/(k*k)),
    bAddress := fun t j => leftAddress (s*s) (cin*(k*k)) t j,
    aBound := fun t j _ hj => input_bound cin h k s t j (j/(k*k)) hk hs hshape
      ((Nat.div_lt_iff_lt_mul (Nat.mul_pos hk hk)).mpr hj),
    bBound := fun t j ht hj => left_bound cout (s*s) (cin*(k*k)) t j (Nat.mul_pos hs hs) ht hj,
    aEval := fun _ g t j st hi hij _ hj => input_eval g cin h k s t j (j/(k*k)) (denseChannel k)
      st hi hij (eval_div_nat g t st (.ivar 1) (.const ((k*k : Nat) : Int)) j (k*k) hij
        (int32_cast (k*k) hkk) (Nat.mul_pos hk hk)) hk hs hshape
      ((Nat.div_lt_iff_lt_mul (Nat.mul_pos hk hk)).mpr hj) ha,
    bEval := fun _ g t j st hi hij ht hj => left_eval g cout (s*s) (cin*(k*k)) t j st hi hij
      ho (Nat.mul_pos hs hs) ht hj hss hb }

def depthProfile (c h k : Nat) (hc : 0<c) (hk : 0<k) (hkh : k≤h)
    (ha : (c*h)*h<2147483648) (hb : c*(k*k)<2147483648)
    (hn : c*(side h k*side h k)<2147483648) : LarkDot.Profile := by
  let s := side h k
  have hs : 0<s := by dsimp [s,side]; omega
  have hshape : s+k=h+1 := by dsimp [s,side]; omega
  have hkk := k_bound c (k*k) hc hb
  have hss := k_bound c (s*s) hc hn
  exact {
    n := c*(s*s), k := k*k, aSize := (c*h)*h, bSize := c*(k*k),
    aIndex := inputIndex (depthChannel s) h k s,
    bIndex := leftIndex (s*s) (k*k),
    aAddress := fun t j => inputAddress h k s t j (t/(s*s)),
    bAddress := fun t j => leftAddress (s*s) (k*k) t j,
    aBound := fun t j ht _ => input_bound c h k s t j (t/(s*s)) hk hs hshape
      ((Nat.div_lt_iff_lt_mul (Nat.mul_pos hs hs)).mpr ht),
    bBound := fun t j ht hj => left_bound c (s*s) (k*k) t j (Nat.mul_pos hs hs) ht hj,
    aEval := fun _ g t j st hi hij ht _ => input_eval g c h k s t j (t/(s*s)) (depthChannel s)
      st hi hij (eval_div_nat g t st (.ivar 0) (.const ((s*s : Nat) : Int)) t (s*s) hi
        (int32_cast (s*s) hss) (Nat.mul_pos hs hs)) hk hs hshape
      ((Nat.div_lt_iff_lt_mul (Nat.mul_pos hs hs)).mpr ht) ha,
    bEval := fun _ g t j st hi hij ht hj => left_eval g c (s*s) (k*k) t j st hi hij
      hc (Nat.mul_pos hs hs) ht hj hss hb }

#print axioms input_eval
#print axioms denseProfile
#print axioms depthProfile
end LarkConvolution
