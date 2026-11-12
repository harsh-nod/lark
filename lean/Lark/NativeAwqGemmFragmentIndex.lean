import Lark.NativeAwqGemmMatrixProgram

/-! Every signed intermediate of the source's native operand load indices. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

theorem eval_fragment_lane_parts (p : Shape) (t : Nat) (s : State α)
    (hi : s.indices t 0=some ((laneId t : Nat) : Int)) :
    evalIndex (geometry p) t s (.div (v 0) (c 16))=some ((laneId t/16 : Nat) : Int) ∧
      evalIndex (geometry p) t s (.mod (v 0) (c 16))=some ((laneId t%16 : Nat) : Int) :=
  ⟨eval_nat_div (geometry p) t (laneId t) 16 s (v 0) hi (by decide) (by decide),
    eval_nat_mod (geometry p) t (laneId t) 16 s (v 0) hi (by decide) (by decide)⟩

theorem eval_a_fragment (p : Shape) (t half e : Nat) (s : State α) (hh : half<2) (he : e<4)
    (hi : s.indices t 0=some ((laneId t : Nat) : Int)) :
    evalIndex (geometry p) t s (aFragmentIndex half e)=some ((aFragment (laneId t) half e : Nat) : Int) := by
  have parts := eval_fragment_lane_parts p t s hi
  have bound := a_fragment_bound (laneId t) half e (lane_bound t) hh he
  unfold aFragment at bound
  have row := eval_nat_mul (geometry p) t (laneId t%16) 40 s _ (c 40) parts.2
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have halfTerm := eval_nat_const (geometry p) t (half*16) s (by omega)
  have rowHalf := eval_nat_add (geometry p) t ((laneId t%16)*40) (half*16) s _ _ row halfTerm (by omega)
  have divTerm := eval_nat_mul (geometry p) t (laneId t/16) 4 s _ (c 4) parts.1
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have base := eval_nat_add (geometry p) t ((laneId t%16)*40+half*16) ((laneId t/16)*4) s _ _ rowHalf divTerm (by omega)
  exact eval_nat_add (geometry p) t ((laneId t%16)*40+half*16+(laneId t/16)*4) e s _ _ base
    (eval_nat_const _ _ _ _ (by omega)) (by omega)

theorem eval_b_fragment (p : Shape) (t half bank e : Nat) (s : State α)
    (hh : half<2) (hb : bank<banks p) (he : e<4)
    (hi : s.indices t 0=some ((laneId t : Nat) : Int)) :
    evalIndex (geometry p) t s (bFragmentIndex p half bank e)=some ((bFragment p (laneId t) half bank e : Nat) : Int) := by
  have parts := eval_fragment_lane_parts p t s hi
  have hl := lane_bound t
  have rowBound : half*16+(laneId t/16)*4+e<32 := by omega
  have sharedBound := b_fragment_bound p (laneId t) half bank e hl hh hb he
  have bound : (half*16+(laneId t/16)*4+e)*(tileN p+8)+bank*16+laneId t%16<2147483648 := by
    unfold bFragment at sharedBound
    rcases tile_cases p with hn | hn <;> rw [hn] at sharedBound ⊢ <;> omega
  have halfTerm := eval_nat_const (geometry p) t (half*16) s (by omega)
  have divTerm := eval_nat_mul (geometry p) t (laneId t/16) 4 s _ (c 4) parts.1
    (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have halfDiv := eval_nat_add (geometry p) t (half*16) ((laneId t/16)*4) s _ _ halfTerm divTerm (by omega)
  have row := eval_nat_add (geometry p) t (half*16+(laneId t/16)*4) e s _ _ halfDiv
    (eval_nat_const _ _ _ _ (by omega)) (by omega)
  have strideBound : tileN p+8<2147483648 := by rcases tile_cases p with hn | hn <;> omega
  have rowStride := eval_nat_mul (geometry p) t (half*16+(laneId t/16)*4+e) (tileN p+8) s _ _ row
    (eval_nat_const _ _ _ _ strideBound) (by omega)
  have bankTerm := eval_nat_const (geometry p) t (bank*16) s (by omega)
  have rowBank := eval_nat_add (geometry p) t ((half*16+(laneId t/16)*4+e)*(tileN p+8)) (bank*16)
    s _ _ rowStride bankTerm (by omega)
  exact eval_nat_add (geometry p) t ((half*16+(laneId t/16)*4+e)*(tileN p+8)+bank*16) (laneId t%16)
    s _ _ rowBank parts.2 bound

#print axioms eval_fragment_lane_parts
#print axioms eval_a_fragment
#print axioms eval_b_fragment
end LarkNativeAwqGemm
