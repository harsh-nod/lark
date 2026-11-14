import Lark.PtxFeedForwardUp

/- Finite initialization for the unchanged full-size FFN down-stage program.
   All 171 instructions are retained. This component proves only the real
   47-instruction prologue, with original grid 16384 and scalar interpretation. -/
namespace LarkPtxMatrix
open LarkNonlinear LarkPtxPointwise LarkPtxDot
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem bits32_negative256 : bits32 (-256) = 4294967040 := by decide

theorem clear_low8 (n : Nat) (hn : n < 4294967296) :
    n &&& 4294967040 = (n / 256) * 256 := by
  have hd : (n &&& 4294967040) / 256 = n / 256 := by
    have hdiv : n / 256 < 16777216 := by omega
    change (n &&& 4294967040) / 2^8 = n / 256
    rw [Nat.and_div_two_pow]
    change n / 256 &&& (2^24-1) = n / 256
    exact Nat.and_two_pow_sub_one_of_lt_two_pow hdiv
  have hm : (n &&& 4294967040) % 256 = 0 := by
    change (n &&& 4294967040) % 2^8 = 0
    rw [Nat.and_mod_two_pow]
    change n % 256 &&& 0 = 0
    simp
  have hs := Nat.mod_add_div (n &&& 4294967040) 256
  rw [hm, hd] at hs
  omega

namespace FfnDown

def program : List Instruction := [
  (.base (.parameter (25) (0))),
  (.base (.parameter (26) (1))),
  (.base (.parameter (24) (2))),
  (.base (.toGlobal (48) (26))),
  (.base (.toGlobal (47) (25))),
  (.base (.blockId (1))),
  (.shiftRightSigned32 5 1 31),
  (.shiftRightUnsigned32 6 5 24),
  (.base (.addSigned32 (7) (1) (.reg (6)))),
  (.andBits32 8 7 (.imm (-256))),
  (.subSigned32 9 1 (.reg (8))),
  (.base (.addSigned32 (10) (9) (.imm (3840)))),
  (.mulWideUnsigned32 3 10 2),
  (.base (.shiftLeft32 (11) (7) (2))),
  (.andBits32 12 11 (.imm (-1024))),
  (.base (.addSigned32 (13) (9) (.imm (3584)))),
  (.mulWideUnsigned32 4 13 2),
  (.base (.addSigned32 (14) (9) (.imm (3328)))),
  (.mulWideUnsigned32 5 14 2),
  (.base (.addSigned32 (15) (9) (.imm (3072)))),
  (.mulWideUnsigned32 6 15 2),
  (.base (.addSigned32 (16) (9) (.imm (2816)))),
  (.mulWideUnsigned32 7 16 2),
  (.base (.addSigned32 (17) (9) (.imm (2560)))),
  (.mulWideUnsigned32 8 17 2),
  (.base (.addSigned32 (18) (9) (.imm (2304)))),
  (.mulWideUnsigned32 9 18 2),
  (.base (.addSigned32 (19) (9) (.imm (2048)))),
  (.mulWideUnsigned32 10 19 2),
  (.base (.addSigned32 (20) (9) (.imm (1792)))),
  (.mulWideUnsigned32 11 20 2),
  (.base (.addSigned32 (21) (9) (.imm (1536)))),
  (.mulWideUnsigned32 12 21 2),
  (.base (.addSigned32 (22) (9) (.imm (1280)))),
  (.mulWideUnsigned32 13 22 2),
  (.base (.addSigned32 (23) (9) (.imm (1024)))),
  (.mulWideUnsigned32 14 23 2),
  (.base (.addSigned32 (24) (9) (.imm (768)))),
  (.mulWideUnsigned32 15 24 2),
  (.base (.addSigned32 (25) (9) (.imm (512)))),
  (.mulWideUnsigned32 16 25 2),
  (.base (.mulWideSigned32 (17) (9) (2))),
  (.base (.addSigned32 (26) (9) (.imm (256)))),
  (.mulWideUnsigned32 18 26 2),
  (.base (.mulWideSigned32 (19) (12) (2))),
  (.base (.literalFloat (68) (0) (1))),
  (.base (.literal32 (27) (0))),
  (.base (.addSigned64 (27) (47) (.reg (19)))),
  (.base (.loadHalf (1) (27) (0))),
  (.base (.fromHalf (4) (1))),
  (.base (.addSigned64 (28) (48) (.reg (17)))),
  (.base (.loadHalf (2) (28) (0))),
  (.base (.fromHalf (5) (2))),
  (.base (.binaryFloat (36) .mul (4) (5))),
  (.base (.binaryFloat (37) .add (68) (36))),
  (.base (.loadHalf (3) (27) (2))),
  (.base (.fromHalf (6) (3))),
  (.base (.addSigned64 (29) (48) (.reg (18)))),
  (.base (.loadHalf (4) (29) (0))),
  (.base (.fromHalf (7) (4))),
  (.base (.binaryFloat (38) .mul (6) (7))),
  (.base (.binaryFloat (39) .add (37) (38))),
  (.base (.loadHalf (5) (27) (4))),
  (.base (.fromHalf (8) (5))),
  (.base (.addSigned64 (30) (48) (.reg (16)))),
  (.base (.loadHalf (6) (30) (0))),
  (.base (.fromHalf (9) (6))),
  (.base (.binaryFloat (40) .mul (8) (9))),
  (.base (.binaryFloat (41) .add (39) (40))),
  (.base (.loadHalf (7) (27) (6))),
  (.base (.fromHalf (10) (7))),
  (.base (.addSigned64 (31) (48) (.reg (15)))),
  (.base (.loadHalf (8) (31) (0))),
  (.base (.fromHalf (11) (8))),
  (.base (.binaryFloat (42) .mul (10) (11))),
  (.base (.binaryFloat (43) .add (41) (42))),
  (.base (.loadHalf (9) (27) (8))),
  (.base (.fromHalf (12) (9))),
  (.base (.addSigned64 (32) (48) (.reg (14)))),
  (.base (.loadHalf (10) (32) (0))),
  (.base (.fromHalf (13) (10))),
  (.base (.binaryFloat (44) .mul (12) (13))),
  (.base (.binaryFloat (45) .add (43) (44))),
  (.base (.loadHalf (11) (27) (10))),
  (.base (.fromHalf (14) (11))),
  (.base (.addSigned64 (33) (48) (.reg (13)))),
  (.base (.loadHalf (12) (33) (0))),
  (.base (.fromHalf (15) (12))),
  (.base (.binaryFloat (46) .mul (14) (15))),
  (.base (.binaryFloat (47) .add (45) (46))),
  (.base (.loadHalf (13) (27) (12))),
  (.base (.fromHalf (16) (13))),
  (.base (.addSigned64 (34) (48) (.reg (12)))),
  (.base (.loadHalf (14) (34) (0))),
  (.base (.fromHalf (17) (14))),
  (.base (.binaryFloat (48) .mul (16) (17))),
  (.base (.binaryFloat (49) .add (47) (48))),
  (.base (.loadHalf (15) (27) (14))),
  (.base (.fromHalf (18) (15))),
  (.base (.addSigned64 (35) (48) (.reg (11)))),
  (.base (.loadHalf (16) (35) (0))),
  (.base (.fromHalf (19) (16))),
  (.base (.binaryFloat (50) .mul (18) (19))),
  (.base (.binaryFloat (51) .add (49) (50))),
  (.base (.loadHalf (17) (27) (16))),
  (.base (.fromHalf (20) (17))),
  (.base (.addSigned64 (36) (48) (.reg (10)))),
  (.base (.loadHalf (18) (36) (0))),
  (.base (.fromHalf (21) (18))),
  (.base (.binaryFloat (52) .mul (20) (21))),
  (.base (.binaryFloat (53) .add (51) (52))),
  (.base (.loadHalf (19) (27) (18))),
  (.base (.fromHalf (22) (19))),
  (.base (.addSigned64 (37) (48) (.reg (9)))),
  (.base (.loadHalf (20) (37) (0))),
  (.base (.fromHalf (23) (20))),
  (.base (.binaryFloat (54) .mul (22) (23))),
  (.base (.binaryFloat (55) .add (53) (54))),
  (.base (.loadHalf (21) (27) (20))),
  (.base (.fromHalf (24) (21))),
  (.base (.addSigned64 (38) (48) (.reg (8)))),
  (.base (.loadHalf (22) (38) (0))),
  (.base (.fromHalf (25) (22))),
  (.base (.binaryFloat (56) .mul (24) (25))),
  (.base (.binaryFloat (57) .add (55) (56))),
  (.base (.loadHalf (23) (27) (22))),
  (.base (.fromHalf (26) (23))),
  (.base (.addSigned64 (39) (48) (.reg (7)))),
  (.base (.loadHalf (24) (39) (0))),
  (.base (.fromHalf (27) (24))),
  (.base (.binaryFloat (58) .mul (26) (27))),
  (.base (.binaryFloat (59) .add (57) (58))),
  (.base (.loadHalf (25) (27) (24))),
  (.base (.fromHalf (28) (25))),
  (.base (.addSigned64 (40) (48) (.reg (6)))),
  (.base (.loadHalf (26) (40) (0))),
  (.base (.fromHalf (29) (26))),
  (.base (.binaryFloat (60) .mul (28) (29))),
  (.base (.binaryFloat (61) .add (59) (60))),
  (.base (.loadHalf (27) (27) (26))),
  (.base (.fromHalf (30) (27))),
  (.base (.addSigned64 (41) (48) (.reg (5)))),
  (.base (.loadHalf (28) (41) (0))),
  (.base (.fromHalf (31) (28))),
  (.base (.binaryFloat (62) .mul (30) (31))),
  (.base (.binaryFloat (63) .add (61) (62))),
  (.base (.loadHalf (29) (27) (28))),
  (.base (.fromHalf (32) (29))),
  (.base (.addSigned64 (42) (48) (.reg (4)))),
  (.base (.loadHalf (30) (42) (0))),
  (.base (.fromHalf (33) (30))),
  (.base (.binaryFloat (64) .mul (32) (33))),
  (.base (.binaryFloat (65) .add (63) (64))),
  (.base (.loadHalf (31) (27) (30))),
  (.base (.fromHalf (34) (31))),
  (.base (.addSigned64 (43) (48) (.reg (3)))),
  (.base (.loadHalf (32) (43) (0))),
  (.base (.fromHalf (35) (32))),
  (.base (.binaryFloat (66) .mul (34) (35))),
  (.base (.binaryFloat (68) .add (65) (66))),
  (.base (.addSigned64 (48) (48) (.imm (8192)))),
  (.base (.addSigned64 (47) (47) (.imm (32)))),
  (.base (.addSigned32 (27) (27) (.imm (16)))),
  (.base (.compareNeSigned32 (1) (27) (.imm (1024)))),
  (.base (.branch (1) (47))),
  (.base (.toGlobal (44) (24))),
  (.base (.toHalf (33) (68))),
  (.base (.mulWideSigned32 (45) (1) (2))),
  (.base (.addSigned64 (46) (44) (.reg (45)))),
  (.base (.storeHalf (46) (0) (33))),
  (.base (.ret))]

def layout : Layout :=
  ⟨[⟨.input, 64*1024⟩, ⟨.input, 1024*256⟩, ⟨.output, 64*256⟩], [], []⟩
def geometry : Geometry := ⟨16384, 1, 32⟩
def start (s : State α) : Machine α := { registers := { base := s } }
def prefix0 (_ops : Ops α) (_t : Nat) (s : State α) : Machine α := start s

def prefix1 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setPointer (prefix0 ops t s) 25 ⟨0, 0, false⟩

def prefix2 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setPointer (prefix1 ops t s) 26 ⟨1, 0, false⟩

def prefix3 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setPointer (prefix2 ops t s) 24 ⟨2, 0, false⟩

def prefix4 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setPointer (prefix3 ops t s) 48 ⟨1, 0, true⟩

def prefix5 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setPointer (prefix4 ops t s) 47 ⟨0, 0, true⟩

def prefix6 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix5 ops t s) 1 (t : Int)

def prefix7 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix6 ops t s) 5 0

def prefix8 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix7 ops t s) 6 0

def prefix9 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix8 ops t s) 7 ((t : Nat) : Int)

def prefix10 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix9 ops t s) 8 ((t/256*256 : Nat) : Int)

def prefix11 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix10 ops t s) 9 ((t%256 : Nat) : Int)

def prefix12 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix11 ops t s) 10 ((t%256+3840 : Nat) : Int)

def prefix13 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix12 ops t s) 3 (((t%256+3840)*2 : Nat) : Int)

def prefix14 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix13 ops t s) 11 ((t*4 : Nat) : Int)

def prefix15 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix14 ops t s) 12 ((t/256*1024 : Nat) : Int)

def prefix16 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix15 ops t s) 13 ((t%256+3584 : Nat) : Int)

def prefix17 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix16 ops t s) 4 (((t%256+3584)*2 : Nat) : Int)

def prefix18 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix17 ops t s) 14 ((t%256+3328 : Nat) : Int)

def prefix19 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix18 ops t s) 5 (((t%256+3328)*2 : Nat) : Int)

def prefix20 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix19 ops t s) 15 ((t%256+3072 : Nat) : Int)

def prefix21 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix20 ops t s) 6 (((t%256+3072)*2 : Nat) : Int)

def prefix22 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix21 ops t s) 16 ((t%256+2816 : Nat) : Int)

def prefix23 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix22 ops t s) 7 (((t%256+2816)*2 : Nat) : Int)

def prefix24 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix23 ops t s) 17 ((t%256+2560 : Nat) : Int)

def prefix25 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix24 ops t s) 8 (((t%256+2560)*2 : Nat) : Int)

def prefix26 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix25 ops t s) 18 ((t%256+2304 : Nat) : Int)

def prefix27 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix26 ops t s) 9 (((t%256+2304)*2 : Nat) : Int)

def prefix28 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix27 ops t s) 19 ((t%256+2048 : Nat) : Int)

def prefix29 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix28 ops t s) 10 (((t%256+2048)*2 : Nat) : Int)

def prefix30 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix29 ops t s) 20 ((t%256+1792 : Nat) : Int)

def prefix31 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix30 ops t s) 11 (((t%256+1792)*2 : Nat) : Int)

def prefix32 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix31 ops t s) 21 ((t%256+1536 : Nat) : Int)

def prefix33 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix32 ops t s) 12 (((t%256+1536)*2 : Nat) : Int)

def prefix34 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix33 ops t s) 22 ((t%256+1280 : Nat) : Int)

def prefix35 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix34 ops t s) 13 (((t%256+1280)*2 : Nat) : Int)

def prefix36 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix35 ops t s) 23 ((t%256+1024 : Nat) : Int)

def prefix37 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix36 ops t s) 14 (((t%256+1024)*2 : Nat) : Int)

def prefix38 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix37 ops t s) 24 ((t%256+768 : Nat) : Int)

def prefix39 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix38 ops t s) 15 (((t%256+768)*2 : Nat) : Int)

def prefix40 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix39 ops t s) 25 ((t%256+512 : Nat) : Int)

def prefix41 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix40 ops t s) 16 (((t%256+512)*2 : Nat) : Int)

def prefix42 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix41 ops t s) 17 (((t%256)*2 : Nat) : Int)

def prefix43 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix42 ops t s) 26 ((t%256+256 : Nat) : Int)

def prefix44 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix43 ops t s) 18 (((t%256+256)*2 : Nat) : Int)

def prefix45 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex64 (prefix44 ops t s) 19 (((t/256*1024)*2 : Nat) : Int)

def prefix46 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setFloat (prefix45 ops t s) 68 (ops.literal 0 1)

def prefix47 (ops : Ops α) (t : Nat) (s : State α) : Machine α :=
  setIndex32 (prefix46 ops t s) 27 0

theorem prefix_step_0 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix0 ops t s) = some (prefix1 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix0 ops t s) (.base (.parameter (25) (0))) (by rfl) (by rfl)]
  rfl

theorem prefix_step_1 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix1 ops t s) = some (prefix2 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix1 ops t s) (.base (.parameter (26) (1))) (by rfl) (by rfl)]
  rfl

theorem prefix_step_2 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix2 ops t s) = some (prefix3 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix2 ops t s) (.base (.parameter (24) (2))) (by rfl) (by rfl)]
  rfl

theorem prefix_step_3 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix3 ops t s) = some (prefix4 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix3 ops t s) (.base (.toGlobal (48) (26))) (by rfl) (by rfl)]
  rfl

theorem prefix_step_4 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix4 ops t s) = some (prefix5 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix4 ops t s) (.base (.toGlobal (47) (25))) (by rfl) (by rfl)]
  rfl

theorem prefix_step_5 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix5 ops t s) = some (prefix6 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix5 ops t s) (.base (.blockId (1))) (by rfl) (by rfl)]
  rw [base_step]
  have hb : 0 < geometry.block ∧ t / geometry.block < 4294967296 := by
    simp only [geometry, Nat.div_one]; omega
  simpa only [geometry, Nat.div_one] using blockId_step ops layout geometry t 1 (prefix5 ops t s) hb

theorem prefix_step_6 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix6 ops t s) = some (prefix7 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix6 ops t s) (.shiftRightSigned32 5 1 31) (by rfl) (by rfl)]
  have e := signed_right_step ops layout geometry t 5 1 31 ((t : Nat) : Int) (prefix6 ops t s) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  have hp : (2 : Int)^min 31 32 = 2147483648 := by decide
  have hz : (t : Int)/2147483648 = 0 := by omega
  simpa only [hp, hz] using e

theorem prefix_step_7 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix7 ops t s) = some (prefix8 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix7 ops t s) (.shiftRightUnsigned32 6 5 24) (by rfl) (by rfl)]
  have e := unsigned_right_step ops layout geometry t 6 5 24 ((0 : Nat) : Int) (prefix7 ops t s) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  exact e

theorem prefix_step_8 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix8 ops t s) = some (prefix9 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix8 ops t s) (.base (.addSigned32 (7) (1) (.reg (6)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 7 1 (.reg 6) (prefix8 ops t s)
    ((t : Nat) : Int) ((0 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_9 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix9 ops t s) = some (prefix10 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix9 ops t s) (.andBits32 8 7 (.imm (-256))) (by rfl) (by rfl)]
  have e := and_step ops layout geometry t 8 7 (.imm (-256))
    ((t : Nat) : Int) (-256) (prefix9 ops t s) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  have hx : bits32 ((t : Nat) : Int) = t := by
    unfold bits32
    have he : ((t : Nat) : Int)%4294967296 = ((t : Nat) : Int) := by
      try simp only [Int.natCast_mul]
      omega
    rw [he]
    rfl
  rw [hx, bits32_negative256, clear_low8 (t) (by omega)] at e
  exact e

theorem prefix_step_10 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix10 ops t s) = some (prefix11 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix10 ops t s) (.subSigned32 9 1 (.reg (8))) (by rfl) (by rfl)]
  have e := sub_step ops layout geometry t 9 1 (.reg 8) (t : Int)
    ((t/256*256 : Nat) : Int) (prefix10 ops t s) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  have he : (t : Int)-((t/256*256 : Nat) : Int) = ((t%256 : Nat) : Int) := by
    simp only [Int.natCast_mul]; omega
  simpa only [he] using e

theorem prefix_step_11 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix11 ops t s) = some (prefix12 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix11 ops t s) (.base (.addSigned32 (10) (9) (.imm (3840)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 10 9 (.imm 3840) (prefix11 ops t s)
    ((t%256 : Nat) : Int) ((3840 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_12 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix12 ops t s) = some (prefix13 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix12 ops t s) (.mulWideUnsigned32 3 10 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 3 10 2 ((t%256+3840 : Nat) : Int) (prefix12 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_13 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix13 ops t s) = some (prefix14 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix13 ops t s) (.base (.shiftLeft32 (11) (7) (2))) (by rfl) (by rfl)]
  rw [base_step]
  have e := shiftLeft_step ops layout geometry t 11 7 2 (prefix13 ops t s) (t : Int)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  have hp : (2 : Int)^min 2 32 = 4 := by decide
  have he : ((t : Int)*4)%4294967296 = ((t*4 : Nat) : Int) := by
    simp only [Int.natCast_mul]; omega
  simpa only [hp, he] using e

theorem prefix_step_14 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix14 ops t s) = some (prefix15 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix14 ops t s) (.andBits32 12 11 (.imm (-1024))) (by rfl) (by rfl)]
  have e := and_step ops layout geometry t 12 11 (.imm (-1024))
    ((t*4 : Nat) : Int) (-1024) (prefix14 ops t s) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  have hx : bits32 ((t*4 : Nat) : Int) = t*4 := by
    unfold bits32
    have he : ((t*4 : Nat) : Int)%4294967296 = ((t*4 : Nat) : Int) := by
      try simp only [Int.natCast_mul]
      omega
    rw [he]
    rfl
  rw [hx, bits32_negative1024, clear_low10 (t*4) (by omega)] at e
  have hd : t*4/1024 = t/256 := by omega
  rw [hd] at e
  exact e

theorem prefix_step_15 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix15 ops t s) = some (prefix16 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix15 ops t s) (.base (.addSigned32 (13) (9) (.imm (3584)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 13 9 (.imm 3584) (prefix15 ops t s)
    ((t%256 : Nat) : Int) ((3584 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_16 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix16 ops t s) = some (prefix17 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix16 ops t s) (.mulWideUnsigned32 4 13 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 4 13 2 ((t%256+3584 : Nat) : Int) (prefix16 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_17 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix17 ops t s) = some (prefix18 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix17 ops t s) (.base (.addSigned32 (14) (9) (.imm (3328)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 14 9 (.imm 3328) (prefix17 ops t s)
    ((t%256 : Nat) : Int) ((3328 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_18 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix18 ops t s) = some (prefix19 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix18 ops t s) (.mulWideUnsigned32 5 14 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 5 14 2 ((t%256+3328 : Nat) : Int) (prefix18 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_19 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix19 ops t s) = some (prefix20 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix19 ops t s) (.base (.addSigned32 (15) (9) (.imm (3072)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 15 9 (.imm 3072) (prefix19 ops t s)
    ((t%256 : Nat) : Int) ((3072 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_20 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix20 ops t s) = some (prefix21 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix20 ops t s) (.mulWideUnsigned32 6 15 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 6 15 2 ((t%256+3072 : Nat) : Int) (prefix20 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_21 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix21 ops t s) = some (prefix22 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix21 ops t s) (.base (.addSigned32 (16) (9) (.imm (2816)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 16 9 (.imm 2816) (prefix21 ops t s)
    ((t%256 : Nat) : Int) ((2816 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_22 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix22 ops t s) = some (prefix23 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix22 ops t s) (.mulWideUnsigned32 7 16 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 7 16 2 ((t%256+2816 : Nat) : Int) (prefix22 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_23 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix23 ops t s) = some (prefix24 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix23 ops t s) (.base (.addSigned32 (17) (9) (.imm (2560)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 17 9 (.imm 2560) (prefix23 ops t s)
    ((t%256 : Nat) : Int) ((2560 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_24 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix24 ops t s) = some (prefix25 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix24 ops t s) (.mulWideUnsigned32 8 17 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 8 17 2 ((t%256+2560 : Nat) : Int) (prefix24 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_25 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix25 ops t s) = some (prefix26 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix25 ops t s) (.base (.addSigned32 (18) (9) (.imm (2304)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 18 9 (.imm 2304) (prefix25 ops t s)
    ((t%256 : Nat) : Int) ((2304 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_26 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix26 ops t s) = some (prefix27 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix26 ops t s) (.mulWideUnsigned32 9 18 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 9 18 2 ((t%256+2304 : Nat) : Int) (prefix26 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_27 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix27 ops t s) = some (prefix28 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix27 ops t s) (.base (.addSigned32 (19) (9) (.imm (2048)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 19 9 (.imm 2048) (prefix27 ops t s)
    ((t%256 : Nat) : Int) ((2048 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_28 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix28 ops t s) = some (prefix29 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix28 ops t s) (.mulWideUnsigned32 10 19 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 10 19 2 ((t%256+2048 : Nat) : Int) (prefix28 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_29 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix29 ops t s) = some (prefix30 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix29 ops t s) (.base (.addSigned32 (20) (9) (.imm (1792)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 20 9 (.imm 1792) (prefix29 ops t s)
    ((t%256 : Nat) : Int) ((1792 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_30 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix30 ops t s) = some (prefix31 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix30 ops t s) (.mulWideUnsigned32 11 20 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 11 20 2 ((t%256+1792 : Nat) : Int) (prefix30 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_31 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix31 ops t s) = some (prefix32 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix31 ops t s) (.base (.addSigned32 (21) (9) (.imm (1536)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 21 9 (.imm 1536) (prefix31 ops t s)
    ((t%256 : Nat) : Int) ((1536 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_32 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix32 ops t s) = some (prefix33 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix32 ops t s) (.mulWideUnsigned32 12 21 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 12 21 2 ((t%256+1536 : Nat) : Int) (prefix32 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_33 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix33 ops t s) = some (prefix34 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix33 ops t s) (.base (.addSigned32 (22) (9) (.imm (1280)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 22 9 (.imm 1280) (prefix33 ops t s)
    ((t%256 : Nat) : Int) ((1280 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_34 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix34 ops t s) = some (prefix35 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix34 ops t s) (.mulWideUnsigned32 13 22 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 13 22 2 ((t%256+1280 : Nat) : Int) (prefix34 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_35 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix35 ops t s) = some (prefix36 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix35 ops t s) (.base (.addSigned32 (23) (9) (.imm (1024)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 23 9 (.imm 1024) (prefix35 ops t s)
    ((t%256 : Nat) : Int) ((1024 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_36 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix36 ops t s) = some (prefix37 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix36 ops t s) (.mulWideUnsigned32 14 23 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 14 23 2 ((t%256+1024 : Nat) : Int) (prefix36 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_37 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix37 ops t s) = some (prefix38 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix37 ops t s) (.base (.addSigned32 (24) (9) (.imm (768)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 24 9 (.imm 768) (prefix37 ops t s)
    ((t%256 : Nat) : Int) ((768 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_38 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix38 ops t s) = some (prefix39 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix38 ops t s) (.mulWideUnsigned32 15 24 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 15 24 2 ((t%256+768 : Nat) : Int) (prefix38 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_39 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix39 ops t s) = some (prefix40 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix39 ops t s) (.base (.addSigned32 (25) (9) (.imm (512)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 25 9 (.imm 512) (prefix39 ops t s)
    ((t%256 : Nat) : Int) ((512 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_40 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix40 ops t s) = some (prefix41 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix40 ops t s) (.mulWideUnsigned32 16 25 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 16 25 2 ((t%256+512 : Nat) : Int) (prefix40 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_41 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix41 ops t s) = some (prefix42 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix41 ops t s) (.base (.mulWideSigned32 (17) (9) (2))) (by rfl) (by rfl)]
  rw [base_step]
  have e := wide_step ops layout geometry t 17 9 2 ((t%256 : Nat) : Int) (prefix41 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_42 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix42 ops t s) = some (prefix43 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix42 ops t s) (.base (.addSigned32 (26) (9) (.imm (256)))) (by rfl) (by rfl)]
  rw [base_step]
  have e := add32_step ops layout geometry t 26 9 (.imm 256) (prefix42 ops t s)
    ((t%256 : Nat) : Int) ((256 : Nat) : Int) (by rfl) (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [Int.natCast_add, Int.add_zero] using e

theorem prefix_step_43 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix43 ops t s) = some (prefix44 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix43 ops t s) (.mulWideUnsigned32 18 26 2) (by rfl) (by rfl)]
  have e := unsigned_wide_step ops layout geometry t 18 26 2 ((t%256+256 : Nat) : Int) (prefix43 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold unsigned32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_44 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix44 ops t s) = some (prefix45 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix44 ops t s) (.base (.mulWideSigned32 (19) (12) (2))) (by rfl) (by rfl)]
  rw [base_step]
  have e := wide_step ops layout geometry t 19 12 2 ((t/256*1024 : Nat) : Int) (prefix44 ops t s)
    (by rfl) (by
    have hc : t%256 < 256 := Nat.mod_lt _ (by decide)
    have hr : t/256 < 64 := by omega
    unfold signed32 signed64
    try simp only [Int.natCast_add, Int.natCast_mul]
    omega)
  simpa only [setIndex64, Int.natCast_mul] using e

theorem prefix_step_45 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix45 ops t s) = some (prefix46 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix45 ops t s) (.base (.literalFloat (68) (0) (1))) (by rfl) (by rfl)]
  rw [base_step]
  exact zero_float_step ops layout geometry t 68 (prefix45 ops t s)

theorem prefix_step_46 (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    transition ops layout geometry t program (prefix46 ops t s) = some (prefix47 ops t s) := by
  rw [transition_at ops layout geometry t program (prefix46 ops t s) (.base (.literal32 (27) (0))) (by rfl) (by rfl)]
  rw [base_step]
  exact zero_index_step ops layout geometry t 27 (prefix46 ops t s)

def initialized (ops : Ops α) (t : Nat) (s : State α) : Machine α := prefix47 ops t s

theorem prologue_execute (ops : Ops α) (t : Nat) (s : State α) (ht : t < 16384) :
    Steps ops layout geometry t program (start s) (initialized ops t s) := by
  exact .next (prefix_step_0 ops t s ht) (.next (prefix_step_1 ops t s ht) (.next (prefix_step_2 ops t s ht) (.next (prefix_step_3 ops t s ht) (.next (prefix_step_4 ops t s ht) (.next (prefix_step_5 ops t s ht) (.next (prefix_step_6 ops t s ht) (.next (prefix_step_7 ops t s ht) (.next (prefix_step_8 ops t s ht) (.next (prefix_step_9 ops t s ht) (.next (prefix_step_10 ops t s ht) (.next (prefix_step_11 ops t s ht) (.next (prefix_step_12 ops t s ht) (.next (prefix_step_13 ops t s ht) (.next (prefix_step_14 ops t s ht) (.next (prefix_step_15 ops t s ht) (.next (prefix_step_16 ops t s ht) (.next (prefix_step_17 ops t s ht) (.next (prefix_step_18 ops t s ht) (.next (prefix_step_19 ops t s ht) (.next (prefix_step_20 ops t s ht) (.next (prefix_step_21 ops t s ht) (.next (prefix_step_22 ops t s ht) (.next (prefix_step_23 ops t s ht) (.next (prefix_step_24 ops t s ht) (.next (prefix_step_25 ops t s ht) (.next (prefix_step_26 ops t s ht) (.next (prefix_step_27 ops t s ht) (.next (prefix_step_28 ops t s ht) (.next (prefix_step_29 ops t s ht) (.next (prefix_step_30 ops t s ht) (.next (prefix_step_31 ops t s ht) (.next (prefix_step_32 ops t s ht) (.next (prefix_step_33 ops t s ht) (.next (prefix_step_34 ops t s ht) (.next (prefix_step_35 ops t s ht) (.next (prefix_step_36 ops t s ht) (.next (prefix_step_37 ops t s ht) (.next (prefix_step_38 ops t s ht) (.next (prefix_step_39 ops t s ht) (.next (prefix_step_40 ops t s ht) (.next (prefix_step_41 ops t s ht) (.next (prefix_step_42 ops t s ht) (.next (prefix_step_43 ops t s ht) (.next (prefix_step_44 ops t s ht) (.next (prefix_step_45 ops t s ht) (.next (prefix_step_46 ops t s ht) (.refl _)))))))))))))))))))))))))))))))))))))))))))))))

theorem initialized_pc (ops : Ops α) (t : Nat) (s : State α) :
    (initialized ops t s).pc = 47 := rfl
theorem initialized_base (ops : Ops α) (t : Nat) (s : State α) :
    (initialized ops t s).registers.base = s := rfl

end FfnDown
#print axioms FfnDown.prologue_execute
#print axioms FfnDown.initialized_pc
#print axioms FfnDown.initialized_base
end LarkPtxMatrix
