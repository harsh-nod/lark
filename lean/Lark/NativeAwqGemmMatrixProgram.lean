import Lark.NativeAwqGemmStagingTiles

/-! Exact scalar-load and native MFMA sites in both unchanged matrix passes. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

theorem blocks_length (f : Nat → List α) (n width : Nat) (hf : ∀ b, (f b).length=width) :
    ((List.range n).flatMap f).length=n*width := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,
      List.append_nil,List.length_append,ih,hf,Nat.succ_mul]

theorem blocks_site (f : Nat → List α) (n width b i : Nat)
    (hf : ∀ b, (f b).length=width) (hb : b<n) (hi : i<width) :
    ((List.range n).flatMap f)[b*width+i]?=(f b)[i]? := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]
    by_cases before : b<n
    · rw [List.getElem?_append_left (l₁ := (List.range n).flatMap f) (by
        rw [blocks_length f n width hf]
        exact dense_bound n width b i before hi)]
      exact ih before
    · have same : b=n := by omega
      subst b
      rw [List.getElem?_append_right (l₁ := (List.range n).flatMap f) (by rw [blocks_length f n width hf]; omega)]
      rw [blocks_length f n width hf,show n*width+i-n*width=i by omega]

def matrixBank (p : Shape) (half bank : Nat) : List Instruction :=
  (List.range 4).map (fun e => put (rightBase p half bank+e) (.load .shared 1 (bFragmentIndex p half bank e))) ++
    [.mfma (bank*4) (leftBase p half) (rightBase p half bank) (bank*4)]

def passPC (p : Shape) (half : Nat) : Nat := middleBarrier p+1+half*(4+5*banks p)
def matrixPC (p : Shape) (half bank : Nat) : Nat := passPC p half+8+5*bank

theorem matrix_bank_length (p : Shape) (half bank : Nat) : (matrixBank p half bank).length=5 := by
  simp [matrixBank]

theorem matrix_pass_length (p : Shape) (half : Nat) : (matrixPass p half).length=4+5*banks p := by
  change ((List.range 4).map (fun e => put (leftBase p half+e) (.load .shared 0 (aFragmentIndex half e))) ++
    (List.range (banks p)).flatMap (matrixBank p half)).length=_
  rw [List.length_append,blocks_length (matrixBank p half) (banks p) 5 (matrix_bank_length p half)]
  simp [Nat.mul_comm]

theorem matrix_pass_site (p : Shape) (half i : Nat) (hh : half<2) (hi : i<4+5*banks p) :
    (program p)[passPC p half+i]?=(matrixPass p half)[i]? := by
  have halves : half=0 ∨ half=1 := by omega
  rcases halves with hh | hh <;> subst half
  · unfold program
    simp only [List.append_assoc]
    rw [List.getElem?_append_right (l₁ := initialInstructions p)
      (by rw [initial_length]; unfold passPC middleBarrier; omega)]
    rw [initial_length,show passPC p 0+i-(16+4*banks p)=23+i by unfold passPC middleBarrier; omega]
    rw [List.getElem?_append_right (l₁ := stagingInstructions p) (by rw [staging_length]; omega)]
    rw [staging_length,show 23+i-23=i by omega]
    exact List.getElem?_append_left (by rw [matrix_pass_length]; exact hi)
  · unfold program
    simp only [List.append_assoc]
    rw [List.getElem?_append_right (l₁ := initialInstructions p)
      (by rw [initial_length]; unfold passPC middleBarrier; omega)]
    rw [initial_length,show passPC p 1+i-(16+4*banks p)=23+(4+5*banks p)+i by unfold passPC middleBarrier; omega]
    rw [List.getElem?_append_right (l₁ := stagingInstructions p) (by rw [staging_length]; omega)]
    rw [staging_length,show 23+(4+5*banks p)+i-23=(4+5*banks p)+i by omega]
    rw [List.getElem?_append_right (l₁ := matrixPass p 0) (by rw [matrix_pass_length]; omega)]
    rw [matrix_pass_length,show (4+5*banks p)+i-(4+5*banks p)=i by omega]
    exact List.getElem?_append_left (by rw [matrix_pass_length]; exact hi)

theorem matrix_a_site (p : Shape) (half e : Nat) (hh : half<2) (he : e<4) :
    (program p)[passPC p half+e]?=some (put (leftBase p half+e) (.load .shared 0 (aFragmentIndex half e))) := by
  rw [matrix_pass_site p half e hh (by omega)]
  simp [matrixPass,List.getElem?_append,he]

theorem matrix_b_site (p : Shape) (half bank e : Nat) (hh : half<2) (hb : bank<banks p) (he : e<4) :
    (program p)[passPC p half+4+5*bank+e]?=
      some (put (rightBase p half bank+e) (.load .shared 1 (bFragmentIndex p half bank e))) := by
  have bound : 4+5*bank+e<4+5*banks p := by omega
  rw [show passPC p half+4+5*bank+e=passPC p half+(4+5*bank+e) by omega,matrix_pass_site p half _ hh bound]
  change (((List.range 4).map (fun e => put (leftBase p half+e) (.load .shared 0 (aFragmentIndex half e)))) ++
    (List.range (banks p)).flatMap (matrixBank p half))[4+5*bank+e]?=_
  rw [List.getElem?_append_right (by simp only [List.length_map,List.length_range]; omega)]
  simp only [List.length_map,List.length_range]
  rw [show 4+5*bank+e-4=bank*5+e by omega,
    blocks_site (matrixBank p half) (banks p) 5 bank e (matrix_bank_length p half) hb (by omega)]
  simp [matrixBank,List.getElem?_append,he]

theorem matrix_instruction_site (p : Shape) (half bank : Nat) (hh : half<2) (hb : bank<banks p) :
    (program p)[matrixPC p half bank]?=
      some (.mfma (bank*4) (leftBase p half) (rightBase p half bank) (bank*4)) := by
  have bound : 4+5*bank+4<4+5*banks p := by omega
  rw [show matrixPC p half bank=passPC p half+(4+5*bank+4) by unfold matrixPC; omega,
    matrix_pass_site p half _ hh bound]
  change (((List.range 4).map (fun e => put (leftBase p half+e) (.load .shared 0 (aFragmentIndex half e)))) ++
    (List.range (banks p)).flatMap (matrixBank p half))[4+5*bank+4]?=_
  rw [List.getElem?_append_right (by simp only [List.length_map,List.length_range]; omega)]
  simp only [List.length_map,List.length_range]
  rw [show 4+5*bank+4-4=bank*5+4 by omega,
    blocks_site (matrixBank p half) (banks p) 5 bank 4 (matrix_bank_length p half) hb (by decide)]
  simp [matrixBank,List.getElem?_append]

#print axioms blocks_length
#print axioms blocks_site
#print axioms matrix_bank_length
#print axioms matrix_pass_length
#print axioms matrix_pass_site
#print axioms matrix_a_site
#print axioms matrix_b_site
#print axioms matrix_instruction_site
end LarkNativeAwqGemm
