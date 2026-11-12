import Lark.NativeAwqGemmMatrixIteration

/-! Exact K-counter, back-edge, guarded output and halt sites of the
unchanged complete source program. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false

def kTailPC (p : Shape) : Nat := 47+14*banks p
def outPC (p : Shape) (q : Nat) : Nat := outputPC p+2*q

theorem post_matrix_site (p : Shape) (i : Nat) :
    (program p)[kTailPC p+i]?=
      ([increment 13,jump (whilePC p)]++outputInstructions p++[.scalar .halt])[i]? := by
  unfold program
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (l₁ := initialInstructions p)
    (by rw [initial_length]; unfold kTailPC; omega)]
  rw [initial_length,show kTailPC p+i-(16+4*banks p)=23+2*(4+5*banks p)+i by unfold kTailPC; omega]
  rw [List.getElem?_append_right (l₁ := stagingInstructions p) (by rw [staging_length]; omega)]
  rw [staging_length,show 23+2*(4+5*banks p)+i-23=2*(4+5*banks p)+i by omega]
  rw [List.getElem?_append_right (l₁ := matrixPass p 0) (by rw [matrix_pass_length]; omega)]
  rw [matrix_pass_length,show 2*(4+5*banks p)+i-(4+5*banks p)=(4+5*banks p)+i by omega]
  rw [List.getElem?_append_right (l₁ := matrixPass p 1) (by rw [matrix_pass_length]; omega)]
  rw [matrix_pass_length,show (4+5*banks p)+i-(4+5*banks p)=i by omega]

theorem k_increment_site (p : Shape) : (program p)[kTailPC p]?=some (ix 13 (.add (v 13) (c 1))) := by
  have site := post_matrix_site p 0
  simpa only [Nat.add_zero] using site

theorem k_back_edge_site (p : Shape) : (program p)[kTailPC p+1]?=some (jump (whilePC p)) := by
  rw [post_matrix_site]
  rfl

def outputPair (p : Shape) (bank e : Nat) : List Instruction :=
  [branch (.lt (v (9+e)) (c p.m)) (outputPC p+bank*8+e*2+2),
    .scalar (.store .global 2 (outputIndex p bank e) (.un .toHalf (.reg (bank*4+e))))]

def outputBank (p : Shape) (bank : Nat) : List Instruction :=
  (List.range 4).flatMap (outputPair p bank)

theorem output_pair_length (p : Shape) (bank e : Nat) : (outputPair p bank e).length=2 := rfl

theorem output_bank_length (p : Shape) (bank : Nat) : (outputBank p bank).length=8 :=
  blocks_length (outputPair p bank) 4 2 (output_pair_length p bank)

theorem output_instructions_length (p : Shape) : (outputInstructions p).length=8*banks p := by
  change ((List.range (banks p)).flatMap (outputBank p)).length=_
  rw [blocks_length (outputBank p) (banks p) 8 (output_bank_length p)]
  omega

theorem output_pair_site (p : Shape) (bank e i : Nat) (hb : bank<banks p) (he : e<4) (hi : i<2) :
    (program p)[outputPC p+bank*8+e*2+i]?=(outputPair p bank e)[i]? := by
  rw [show outputPC p+bank*8+e*2+i=kTailPC p+(2+bank*8+e*2+i) by unfold outputPC kTailPC; omega,
    post_matrix_site]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (l₁ := [increment 13,jump (whilePC p)]) (by simp only [List.length_cons,List.length_nil]; omega)]
  simp only [List.length_cons,List.length_nil]
  rw [show 2+bank*8+e*2+i-(1+(1+0))=bank*8+(e*2+i) by omega]
  rw [List.getElem?_append_left (l₁ := outputInstructions p) (by rw [output_instructions_length]; omega)]
  change ((List.range (banks p)).flatMap (outputBank p))[bank*8+(e*2+i)]?=_
  rw [blocks_site (outputBank p) (banks p) 8 bank (e*2+i) (output_bank_length p) hb (by omega)]
  exact blocks_site (outputPair p bank) 4 2 e i (output_pair_length p bank) he hi

theorem output_guard_site (p : Shape) (q : Nat) (hq : q<4*banks p) :
    (program p)[outPC p q]?=
      some (branch (.lt (v (9+q%4)) (c p.m)) (outPC p (q+1))) := by
  have hb : q/4<banks p := by omega
  have he : q%4<4 := Nat.mod_lt _ (by decide)
  have site := output_pair_site p (q/4) (q%4) 0 hb he (by decide)
  have pc : outputPC p+q/4*8+q%4*2+0=outPC p q := by unfold outPC; omega
  have next : outputPC p+q/4*8+q%4*2+2=outPC p (q+1) := by unfold outPC; omega
  rw [pc] at site
  simpa only [outputPair,List.getElem?_cons_zero,next] using site

theorem output_store_site (p : Shape) (q : Nat) (hq : q<4*banks p) :
    (program p)[outPC p q+1]?=
      some (.scalar (.store .global 2 (outputIndex p (q/4) (q%4)) (.un .toHalf (.reg q)))) := by
  have hb : q/4<banks p := by omega
  have he : q%4<4 := Nat.mod_lt _ (by decide)
  have site := output_pair_site p (q/4) (q%4) 1 hb he (by decide)
  have pc : outputPC p+q/4*8+q%4*2+1=outPC p q+1 := by unfold outPC; omega
  have reg : q/4*4+q%4=q := by omega
  rw [pc] at site
  simpa only [outputPair,List.getElem?_cons_succ,List.getElem?_cons_zero,reg] using site

theorem output_halt_site (p : Shape) : (program p)[haltPC p]?=some (.scalar .halt) := by
  rw [show haltPC p=kTailPC p+(2+8*banks p) by unfold haltPC kTailPC; omega,post_matrix_site]
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (l₁ := [increment 13,jump (whilePC p)]) (by simp)]
  simp only [List.length_cons,List.length_nil]
  rw [show 2+8*banks p-(1+(1+0))=8*banks p by omega,
    List.getElem?_append_right (l₁ := outputInstructions p) (by rw [output_instructions_length]; omega)]
  rw [output_instructions_length,Nat.sub_self]
  rfl

#print axioms post_matrix_site
#print axioms k_increment_site
#print axioms k_back_edge_site
#print axioms output_pair_length
#print axioms output_bank_length
#print axioms output_instructions_length
#print axioms output_pair_site
#print axioms output_guard_site
#print axioms output_store_site
#print axioms output_halt_site
end LarkNativeAwqGemm
