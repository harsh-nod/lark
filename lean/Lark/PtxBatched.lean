import Lark.PtxMatrix

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- Exact original-size 32-batch compiled source. These initial lemmas bind the
program data and full-shape address arithmetic. Complete instruction execution,
reference extraction and race theorems are still needed. -/
namespace LarkPtxBatched
open LarkNonlinear LarkPtxPointwise
open LarkPtxDot (Machine setPointer setIndex32 blockId_step shiftLeft_step add32_step unsigned32)
open LarkPtxMatrix
namespace Bmm

def program : List LarkPtxMatrix.Instruction := [(.base (.parameter (10) (0))), (.base (.parameter (11) (1))), (.base (.parameter (9) (2))), (.base (.toGlobal (18) (11))), (.base (.toGlobal (17) (10))), (.base (.blockId (1))), (.shiftRightSigned32 5 1 31), (.shiftRightUnsigned32 6 5 17), (.base (.addSigned32 (7) (1) (.reg (6)))), (.shiftRightSigned32 8 7 15), (.base (.shiftLeft32 (9) (8) (14))), (.shiftRightUnsigned32 10 5 23), (.base (.addSigned32 (11) (1) (.reg (10)))), (.shiftRightSigned32 12 11 9), (.shiftRightSigned32 13 11 31), (.shiftRightUnsigned32 14 13 26), (.base (.addSigned32 (15) (12) (.reg (14)))), (.andBits32 16 15 (.imm (16777152))), (.subSigned32 17 12 (.reg (16))), (.base (.shiftLeft32 (18) (17) (8))), (.andBits32 19 11 (.imm (-512))), (.subSigned32 20 1 (.reg (19))), (.base (.shiftLeft32 (21) (8) (17))), (.base (.addSigned32 (22) (20) (.reg (21)))), (.base (.addSigned32 (23) (9) (.reg (18)))), (.base (.mulWideSigned32 (3) (22) (2))), (.base (.mulWideSigned32 (4) (23) (2))), (.base (.literalFloat (68) (0) (1))), (.base (.literal32 (24) (0))), (.base (.addSigned64 (12) (17) (.reg (4)))), (.base (.loadHalf (1) (12) (0))), (.base (.fromHalf (4) (1))), (.base (.addSigned64 (13) (18) (.reg (3)))), (.base (.loadHalf (2) (13) (0))), (.base (.fromHalf (5) (2))), (.base (.binaryFloat (36) .mul (4) (5))), (.base (.binaryFloat (37) .add (68) (36))), (.base (.loadHalf (3) (12) (2))), (.base (.fromHalf (6) (3))), (.base (.loadHalf (4) (13) (1024))), (.base (.fromHalf (7) (4))), (.base (.binaryFloat (38) .mul (6) (7))), (.base (.binaryFloat (39) .add (37) (38))), (.base (.loadHalf (5) (12) (4))), (.base (.fromHalf (8) (5))), (.base (.loadHalf (6) (13) (2048))), (.base (.fromHalf (9) (6))), (.base (.binaryFloat (40) .mul (8) (9))), (.base (.binaryFloat (41) .add (39) (40))), (.base (.loadHalf (7) (12) (6))), (.base (.fromHalf (10) (7))), (.base (.loadHalf (8) (13) (3072))), (.base (.fromHalf (11) (8))), (.base (.binaryFloat (42) .mul (10) (11))), (.base (.binaryFloat (43) .add (41) (42))), (.base (.loadHalf (9) (12) (8))), (.base (.fromHalf (12) (9))), (.base (.loadHalf (10) (13) (4096))), (.base (.fromHalf (13) (10))), (.base (.binaryFloat (44) .mul (12) (13))), (.base (.binaryFloat (45) .add (43) (44))), (.base (.loadHalf (11) (12) (10))), (.base (.fromHalf (14) (11))), (.base (.loadHalf (12) (13) (5120))), (.base (.fromHalf (15) (12))), (.base (.binaryFloat (46) .mul (14) (15))), (.base (.binaryFloat (47) .add (45) (46))), (.base (.loadHalf (13) (12) (12))), (.base (.fromHalf (16) (13))), (.base (.loadHalf (14) (13) (6144))), (.base (.fromHalf (17) (14))), (.base (.binaryFloat (48) .mul (16) (17))), (.base (.binaryFloat (49) .add (47) (48))), (.base (.loadHalf (15) (12) (14))), (.base (.fromHalf (18) (15))), (.base (.loadHalf (16) (13) (7168))), (.base (.fromHalf (19) (16))), (.base (.binaryFloat (50) .mul (18) (19))), (.base (.binaryFloat (51) .add (49) (50))), (.base (.loadHalf (17) (12) (16))), (.base (.fromHalf (20) (17))), (.base (.loadHalf (18) (13) (8192))), (.base (.fromHalf (21) (18))), (.base (.binaryFloat (52) .mul (20) (21))), (.base (.binaryFloat (53) .add (51) (52))), (.base (.loadHalf (19) (12) (18))), (.base (.fromHalf (22) (19))), (.base (.loadHalf (20) (13) (9216))), (.base (.fromHalf (23) (20))), (.base (.binaryFloat (54) .mul (22) (23))), (.base (.binaryFloat (55) .add (53) (54))), (.base (.loadHalf (21) (12) (20))), (.base (.fromHalf (24) (21))), (.base (.loadHalf (22) (13) (10240))), (.base (.fromHalf (25) (22))), (.base (.binaryFloat (56) .mul (24) (25))), (.base (.binaryFloat (57) .add (55) (56))), (.base (.loadHalf (23) (12) (22))), (.base (.fromHalf (26) (23))), (.base (.loadHalf (24) (13) (11264))), (.base (.fromHalf (27) (24))), (.base (.binaryFloat (58) .mul (26) (27))), (.base (.binaryFloat (59) .add (57) (58))), (.base (.loadHalf (25) (12) (24))), (.base (.fromHalf (28) (25))), (.base (.loadHalf (26) (13) (12288))), (.base (.fromHalf (29) (26))), (.base (.binaryFloat (60) .mul (28) (29))), (.base (.binaryFloat (61) .add (59) (60))), (.base (.loadHalf (27) (12) (26))), (.base (.fromHalf (30) (27))), (.base (.loadHalf (28) (13) (13312))), (.base (.fromHalf (31) (28))), (.base (.binaryFloat (62) .mul (30) (31))), (.base (.binaryFloat (63) .add (61) (62))), (.base (.loadHalf (29) (12) (28))), (.base (.fromHalf (32) (29))), (.base (.loadHalf (30) (13) (14336))), (.base (.fromHalf (33) (30))), (.base (.binaryFloat (64) .mul (32) (33))), (.base (.binaryFloat (65) .add (63) (64))), (.base (.loadHalf (31) (12) (30))), (.base (.fromHalf (34) (31))), (.base (.loadHalf (32) (13) (15360))), (.base (.fromHalf (35) (32))), (.base (.binaryFloat (66) .mul (34) (35))), (.base (.binaryFloat (68) .add (65) (66))), (.base (.addSigned64 (18) (18) (.imm (16384)))), (.base (.addSigned64 (17) (17) (.imm (32)))), (.base (.addSigned32 (24) (24) (.imm (16)))), (.base (.compareNeSigned32 (1) (24) (.imm (256)))), (.base (.branch (1) (29))), (.base (.toGlobal (14) (9))), (.base (.toHalf (33) (68))), (.base (.mulWideSigned32 (15) (1) (2))), (.base (.addSigned64 (16) (14) (.reg (15)))), (.base (.storeHalf (16) (0) (33))), (.base (.ret))]

theorem program_length : program.length = 138 := by decide

theorem program_branch : program[131]? = some (.base (.branch 1 29)) := by decide

theorem program_ret : program[137]? = some (.base .ret) := by decide

theorem clear_low6 (n : Nat) (hn : n < 16777216) :
    n &&& 16777152 = (n / 64) * 64 := by
  have hd : (n &&& 16777152) / 64 = n / 64 := by
    have hdiv : n / 64 < 262144 := by omega
    change (n &&& 16777152) / 2^6 = n / 64
    rw [Nat.and_div_two_pow]
    change n / 64 &&& (2^18-1) = n / 64
    exact Nat.and_two_pow_sub_one_of_lt_two_pow hdiv
  have hm : (n &&& 16777152) % 64 = 0 := by
    change (n &&& 16777152) % 2^6 = 0
    rw [Nat.and_mod_two_pow]
    change n % 64 &&& 0 = 0
    simp
  have hs := Nat.mod_add_div (n &&& 16777152) 64
  rw [hm, hd] at hs
  omega

theorem row_decomposition (t : Nat) :
    t / 32768 * 64 + (t / 512) % 64 = t / 512 := by omega

def aIndex (t k : Nat) : Nat := t / 32768 * 16384 + ((t / 512) % 64) * 256 + k
def bIndex (t k : Nat) : Nat := t / 32768 * 131072 + k * 512 + t % 512

theorem aIndex_flat (t k : Nat) : aIndex t k = (t / 512) * 256 + k := by
  unfold aIndex
  have h := row_decomposition t
  omega

theorem coordinates_bounds (t : Nat) (ht : t < 1048576) :
    t / 32768 < 32 ∧ (t / 512) % 64 < 64 ∧ t % 512 < 512 ∧
    t / 32768 * 16384 + ((t / 512) % 64) * 256 < 524288 ∧
    t / 32768 * 131072 + t % 512 < 4194304 := by omega

theorem input_indices_valid (t k : Nat) (ht : t < 1048576) (hk : k < 256) :
    aIndex t k < 524288 ∧ bIndex t k < 4194304 := by
  rw [aIndex_flat]
  unfold bIndex
  omega

def layout : Layout :=
  ⟨[⟨.input, 32*64*256⟩, ⟨.input, 32*256*512⟩, ⟨.output, 32*64*512⟩], [], []⟩
def geometry : Geometry := ⟨1048576, 1, 32⟩

def start (s : State α) : Machine α := { registers := { base := s } }
def parameterA (s : State α) : Machine α := setPointer (start s) 10 ⟨0, 0, false⟩
def parameterB (s : State α) : Machine α := setPointer (parameterA s) 11 ⟨1, 0, false⟩
def parameters (s : State α) : Machine α := setPointer (parameterB s) 9 ⟨2, 0, false⟩
def globalB (s : State α) : Machine α := setPointer (parameters s) 18 ⟨1, 0, true⟩
def globals (s : State α) : Machine α := setPointer (globalB s) 17 ⟨0, 0, true⟩
def indexed (t : Nat) (s : State α) : Machine α := setIndex32 (globals s) 1 (t : Int)
def signed (t : Nat) (s : State α) : Machine α := setIndex32 (indexed t s) 5 0
def batchCorrected (t : Nat) (s : State α) : Machine α := setIndex32 (signed t s) 6 0
def batchAdjusted (t : Nat) (s : State α) : Machine α := setIndex32 (batchCorrected t s) 7 (t : Int)
def batchNumber (t : Nat) (s : State α) : Machine α :=
  setIndex32 (batchAdjusted t s) 8 ((t/32768 : Nat) : Int)
def batchAOffset (t : Nat) (s : State α) : Machine α :=
  setIndex32 (batchNumber t s) 9 ((t/32768*16384 : Nat) : Int)
def rowCorrected (t : Nat) (s : State α) : Machine α := setIndex32 (batchAOffset t s) 10 0
def rowAdjusted (t : Nat) (s : State α) : Machine α := setIndex32 (rowCorrected t s) 11 (t : Int)
def globalRow (t : Nat) (s : State α) : Machine α :=
  setIndex32 (rowAdjusted t s) 12 ((t/512 : Nat) : Int)

theorem parameters_execute (ops : Ops α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (start s) (parameters s) :=
  .next (by rfl) (.next (by rfl) (.next (by rfl) (.refl _)))

theorem globals_execute (ops : Ops α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (parameters s) (globals s) :=
  .next (by rfl) (.next (by rfl) (.refl _))

theorem index_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 1048576) :
    Steps ops layout geometry t program (globals s) (indexed t s) := by
  have hb : 0 < geometry.block ∧ t / geometry.block < 4294967296 := by
    simp only [geometry, Nat.div_one]; omega
  have e := blockId_step ops layout geometry t 1 (globals s) hb
  have e' : execute ops layout geometry t (.base (.blockId 1)) (globals s) =
      some (indexed t s) := by
    simpa only [base_step, geometry, Nat.div_one] using e
  apply one_step
  rw [transition_at ops layout geometry t program (globals s) (.base (.blockId 1)) (by rfl) (by rfl)]
  exact e'

theorem sign_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 1048576) :
    Steps ops layout geometry t program (indexed t s) (signed t s) := by
  have hb : signed32 (t : Int) := by unfold signed32; omega
  have e := signed_right_step ops layout geometry t 5 1 31 (t : Int) (indexed t s) (by rfl) hb
  have hp : (2 : Int)^min 31 32 = 2147483648 := by decide
  have hz : (t : Int) / 2147483648 = 0 := by omega
  rw [hp, hz] at e
  apply one_step
  rw [transition_at ops layout geometry t program (indexed t s) (.shiftRightSigned32 5 1 31)
    (by rfl) (by rfl)]
  exact e

theorem batch_correction_execute (ops : Ops α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (signed t s) (batchCorrected t s) :=
  .next (by rfl) (.refl _)

theorem batch_adjust_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 1048576) :
    Steps ops layout geometry t program (batchCorrected t s) (batchAdjusted t s) := by
  have hb : signed32 (t : Int) ∧ signed32 0 ∧ signed32 ((t : Int)+0) := by
    unfold signed32; omega
  have e := add32_step ops layout geometry t 7 1 (.reg 6) (batchCorrected t s) (t : Int) 0
    (by rfl) (by rfl) hb
  simp only [Int.add_zero] at e
  apply one_step
  rw [transition_at ops layout geometry t program (batchCorrected t s) (.base (.addSigned32 7 1 (.reg 6)))
    (by rfl) (by rfl), base_step]
  exact e

theorem batch_number_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 1048576) :
    Steps ops layout geometry t program (batchAdjusted t s) (batchNumber t s) := by
  have hb : signed32 (t : Int) := by unfold signed32; omega
  have e := signed_right_step ops layout geometry t 8 7 15 (t : Int) (batchAdjusted t s) (by rfl) hb
  have hp : (2 : Int)^min 15 32 = 32768 := by decide
  have he : (t : Int)/32768 = ((t/32768 : Nat) : Int) := by omega
  rw [hp, he] at e
  apply one_step
  rw [transition_at ops layout geometry t program (batchAdjusted t s) (.shiftRightSigned32 8 7 15)
    (by rfl) (by rfl)]
  exact e

theorem batch_a_offset_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 1048576) :
    Steps ops layout geometry t program (batchNumber t s) (batchAOffset t s) := by
  have hr : t/32768 < 32 := by omega
  have hb : unsigned32 ((t/32768 : Nat) : Int) := by unfold unsigned32; omega
  have e := shiftLeft_step ops layout geometry t 9 8 14 (batchNumber t s)
    ((t/32768 : Nat) : Int) (by rfl) hb
  have hp : (2 : Int)^min 14 32 = 16384 := by decide
  have he : (((t/32768 : Nat) : Int)*16384) % 4294967296 = ((t/32768*16384 : Nat) : Int) := by
    simp only [Int.natCast_mul]; omega
  rw [hp, he] at e
  apply one_step
  rw [transition_at ops layout geometry t program (batchNumber t s) (.base (.shiftLeft32 9 8 14))
    (by rfl) (by rfl), base_step]
  exact e

theorem row_correction_execute (ops : Ops α) (t : Nat) (s : State α) :
    Steps ops layout geometry t program (batchAOffset t s) (rowCorrected t s) :=
  .next (by rfl) (.refl _)

theorem row_adjust_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 1048576) :
    Steps ops layout geometry t program (rowCorrected t s) (rowAdjusted t s) := by
  have hb : signed32 (t : Int) ∧ signed32 0 ∧ signed32 ((t : Int)+0) := by
    unfold signed32; omega
  have e := add32_step ops layout geometry t 11 1 (.reg 10) (rowCorrected t s) (t : Int) 0
    (by rfl) (by rfl) hb
  simp only [Int.add_zero] at e
  apply one_step
  rw [transition_at ops layout geometry t program (rowCorrected t s) (.base (.addSigned32 11 1 (.reg 10)))
    (by rfl) (by rfl), base_step]
  exact e

theorem global_row_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 1048576) :
    Steps ops layout geometry t program (rowAdjusted t s) (globalRow t s) := by
  have hb : signed32 (t : Int) := by unfold signed32; omega
  have e := signed_right_step ops layout geometry t 12 11 9 (t : Int) (rowAdjusted t s) (by rfl) hb
  have hp : (2 : Int)^min 9 32 = 512 := by decide
  have he : (t : Int)/512 = ((t/512 : Nat) : Int) := by omega
  rw [hp, he] at e
  apply one_step
  rw [transition_at ops layout geometry t program (rowAdjusted t s) (.shiftRightSigned32 12 11 9)
    (by rfl) (by rfl)]
  exact e

theorem prefix_rows_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 1048576) :
    Steps ops layout geometry t program (start s) (globalRow t s) := by
  apply steps_trans _ _ _ _ _ _ _ _ (parameters_execute ops t s)
  apply steps_trans _ _ _ _ _ _ _ _ (globals_execute ops t s)
  apply steps_trans _ _ _ _ _ _ _ _ (index_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (sign_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (batch_correction_execute ops t s)
  apply steps_trans _ _ _ _ _ _ _ _ (batch_adjust_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (batch_number_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (batch_a_offset_execute ops t s ht)
  apply steps_trans _ _ _ _ _ _ _ _ (row_correction_execute ops t s)
  exact steps_trans _ _ _ _ _ _ _ _ (row_adjust_execute ops t s ht) (global_row_execute ops t s ht)

theorem prefix_rows_pc (t : Nat) (s : State α) : (globalRow t s).pc = 14 := rfl
theorem prefix_rows_base (t : Nat) (s : State α) : (globalRow t s).registers.base = s := rfl

end Bmm
end LarkPtxBatched

#print axioms LarkPtxBatched.Bmm.program_length
#print axioms LarkPtxBatched.Bmm.program_branch
#print axioms LarkPtxBatched.Bmm.program_ret
#print axioms LarkPtxBatched.Bmm.clear_low6
#print axioms LarkPtxBatched.Bmm.row_decomposition
#print axioms LarkPtxBatched.Bmm.aIndex_flat
#print axioms LarkPtxBatched.Bmm.coordinates_bounds
#print axioms LarkPtxBatched.Bmm.input_indices_valid
#print axioms LarkPtxBatched.Bmm.prefix_rows_execute
#print axioms LarkPtxBatched.Bmm.prefix_rows_pc
#print axioms LarkPtxBatched.Bmm.prefix_rows_base
