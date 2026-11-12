import Lark.NativeAwqGemmMemory

/-! Every signed index operation of the source's guarded A-staging stores. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

structure AIndices (p : Shape) (tile t e : Nat) (s : State α) : Prop where
  setup : SetupIndices p t s
  k : s.indices t 13=some (tile : Int)
  element : s.indices t 14=some (e : Int)

theorem a_indices_of_indices (p : Shape) (tile t e : Nat) (s next : State α)
    (h : AIndices p tile t e s) (hi : next.indices=s.indices) : AIndices p tile t e next := by
  exact {
    setup := setup_of_indices p t s next h.setup hi
    k := by rw [hi]; exact h.k
    element := by rw [hi]; exact h.element }

theorem a_indices_set_element (p : Shape) (tile t e next pc : Nat) (s : State α)
    (h : AIndices p tile t e s) :
    AIndices p tile t next (setIndex s t 14 (next : Int) pc) := by
  exact {
    setup := setIndex_setup p t 14 pc (next : Int) s h.setup (by decide)
    k := by simpa [setIndex,advance] using h.k
    element := by simp [setIndex,advance] }

theorem input_col_component (t e : Nat) : inputCol t+e=aStoreCol (laneId t) e := by
  simp [inputCol,aStoreCol]

theorem shared_a_component (t e : Nat) : sharedABase t+e=aStoreAddress (laneId t) e := by
  simp [sharedABase,aStoreAddress,aStoreCol,Nat.add_assoc]

theorem eval_a_stage (p : Shape) (tile t e : Nat) (s : State α)
    (he : e<8) (h : AIndices p tile t e s) :
    evalIndex (geometry p) t s aStageIndex=some ((aStoreAddress (laneId t) e : Nat) : Int) := by
  have bound := a_store_bound (laneId t) e (lane_bound t) he
  have sourceBound : sharedABase t+e<2147483648 := by rw [shared_a_component]; omega
  have result := eval_nat_add (geometry p) t (sharedABase t) e s (v 8) (v 14)
    h.setup.aBase h.element sourceBound
  simpa only [shared_a_component] using result

theorem a_input_component_bound (t e : Nat) (he : e<8) : inputCol t+e<32 := by
  rw [input_col_component]
  exact (a_store_coordinates (laneId t) e (lane_bound t) he).2

theorem eval_a_global (p : Shape) (tile t e : Nat) (s : State α)
    (hr : inputRow p t<p.m) (hk : tile<p.k/32) (he : e<8) (h : AIndices p tile t e s) :
    evalIndex (geometry p) t s (aGlobalIndex p)=
      some ((aGlobal p (inputRow p t) tile (inputCol t+e) : Nat) : Int) := by
  have signed := a_global_int32 p (inputRow p t) tile (inputCol t+e) hr hk (a_input_component_bound t e he)
  have bound : inputRow p t*p.k+tile*32+inputCol t+e<2147483648 := by
    simpa only [aGlobal,Nat.add_assoc] using signed
  have row := eval_nat_mul (geometry p) t (inputRow p t) p.k s (v 6) (c p.k)
    h.setup.aRow (eval_nat_const _ _ _ _ (scalar_parameter_bounds p).2.1) (by omega)
  have chunk := eval_nat_mul (geometry p) t tile 32 s (v 13) (c 32)
    h.k (eval_nat_const _ _ _ _ (by decide)) (by omega)
  have first := eval_nat_add (geometry p) t (inputRow p t*p.k) (tile*32) s _ _ row chunk (by omega)
  have column := eval_nat_add (geometry p) t (inputRow p t*p.k+tile*32) (inputCol t) s _ (v 7)
    first h.setup.aCol (by omega)
  have result := eval_nat_add (geometry p) t (inputRow p t*p.k+tile*32+inputCol t) e s _ (v 14)
    column h.element bound
  simpa only [aGlobalIndex,aGlobal,Nat.add_assoc] using result

theorem eval_a_increment (p : Shape) (tile t e : Nat) (s : State α)
    (he : e<8) (h : AIndices p tile t e s) :
    evalIndex (geometry p) t s (.add (v 14) (c 1))=some ((e+1 : Nat) : Int) :=
  eval_nat_add (geometry p) t e 1 s (v 14) (c 1) h.element
    (eval_nat_const _ _ _ _ (by decide)) (by omega)

theorem staging_site (p : Shape) (i : Nat) (hi : i<23) :
    (program p)[16+4*banks p+i]?=(stagingInstructions p)[i]? := by
  unfold program
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (l₁ := initialInstructions p) (i := 16+4*banks p+i)
    (by rw [initial_length]; omega)]
  rw [initial_length,show 16+4*banks p+i-(16+4*banks p)=i by omega]
  exact List.getElem?_append_left (l₁ := stagingInstructions p) (i := i) (by rw [staging_length]; exact hi)

theorem a_store_site (p : Shape) : (program p)[firstBarrier p+4]?=
    some (.scalar (.store .shared 0 aStageIndex (.load .global 0 (aGlobalIndex p)))) := by
  rw [show firstBarrier p+4=16+4*banks p+3 by unfold firstBarrier; omega,staging_site p 3 (by decide)]
  rfl

theorem a_zero_store_site (p : Shape) : (program p)[firstBarrier p+9]?=
    some (.scalar (.store .shared 0 aStageIndex (.un .toHalf (.lit 0 1)))) := by
  rw [show firstBarrier p+9=16+4*banks p+8 by unfold firstBarrier; omega,staging_site p 8 (by decide)]
  rfl

#print axioms a_indices_of_indices
#print axioms a_indices_set_element
#print axioms input_col_component
#print axioms shared_a_component
#print axioms eval_a_stage
#print axioms a_input_component_bound
#print axioms eval_a_global
#print axioms eval_a_increment
#print axioms staging_site
#print axioms a_store_site
#print axioms a_zero_store_site
end LarkNativeAwqGemm
