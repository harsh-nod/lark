import Lark.PtxBatched

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- Single-instruction initialization witnesses keep intermediate machine states
opaque. Their Steps proofs execute the original program; no loop or instruction
summary is assumed. This module is under development, not a kernel certificate. -/
namespace LarkPtxBatched.Bmm.Init
open LarkNonlinear LarkPtxPointwise
open LarkPtxDot (Machine setPointer setIndex32 setFloat unsigned32)
open LarkPtxMatrix (Steps setIndex64)

structure Frame (t : Nat) (base : State α) (s : Machine α) : Prop where
  active : s.registers.stopped = false
  memory : s.registers.base = base
  index : s.registers.i32 1 = some (t : Int)
  batch : s.registers.i32 8 = some ((t/32768 : Nat) : Int)
  batchA : s.registers.i32 9 = some ((t/32768*16384 : Nat) : Int)
  lane : s.registers.i32 11 = some (t : Int)
  row : s.registers.i32 12 = some ((t/512 : Nat) : Int)
  a : s.registers.pointer 17 = some ⟨0, 0, true⟩
  b : s.registers.pointer 18 = some ⟨1, 0, true⟩
  out : s.registers.pointer 9 = some ⟨2, 0, false⟩

theorem prefix_frame (t : Nat) (base : State α) : Frame t base (globalRow t base) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem frame32 (t : Nat) (base : State α) (s : Machine α) (d : Nat) (v : Int)
    (h : Frame t base s) (hd : d ≠ 1 ∧ d ≠ 8 ∧ d ≠ 9 ∧ d ≠ 11 ∧ d ≠ 12) :
    Frame t base (setIndex32 s d v) := by
  rcases hd with ⟨h1, h8, h9, h11, h12⟩
  refine ⟨h.active, h.memory, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [LarkPtxDot.setIndex32_i32, if_neg (Ne.symm h1)] using h.index
  · simpa only [LarkPtxDot.setIndex32_i32, if_neg (Ne.symm h8)] using h.batch
  · simpa only [LarkPtxDot.setIndex32_i32, if_neg (Ne.symm h9)] using h.batchA
  · simpa only [LarkPtxDot.setIndex32_i32, if_neg (Ne.symm h11)] using h.lane
  · simpa only [LarkPtxDot.setIndex32_i32, if_neg (Ne.symm h12)] using h.row
  · simpa only [LarkPtxMatrix.setIndex32_pointer] using h.a
  · simpa only [LarkPtxMatrix.setIndex32_pointer] using h.b
  · simpa only [LarkPtxMatrix.setIndex32_pointer] using h.out

theorem frame64 (t : Nat) (base : State α) (s : Machine α) (d : Nat) (v : Int)
    (h : Frame t base s) (hd : d ≠ 17 ∧ d ≠ 18 ∧ d ≠ 9) :
    Frame t base (setIndex64 s d v) := by
  rcases hd with ⟨ha, hb, ho⟩
  refine ⟨h.active, h.memory, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [LarkPtxMatrix.setIndex64_i32] using h.index
  · simpa only [LarkPtxMatrix.setIndex64_i32] using h.batch
  · simpa only [LarkPtxMatrix.setIndex64_i32] using h.batchA
  · simpa only [LarkPtxMatrix.setIndex64_i32] using h.lane
  · simpa only [LarkPtxMatrix.setIndex64_i32] using h.row
  · simpa only [LarkPtxMatrix.setIndex64_pointer, if_neg (Ne.symm ha)] using h.a
  · simpa only [LarkPtxMatrix.setIndex64_pointer, if_neg (Ne.symm hb)] using h.b
  · simpa only [LarkPtxMatrix.setIndex64_pointer, if_neg (Ne.symm ho)] using h.out

theorem frame_float (t : Nat) (base : State α) (s : Machine α) (d : Nat) (v : α)
    (h : Frame t base s) : Frame t base (setFloat s d v) := by
  have hi (r : Nat) : (setFloat s d v).registers.i32 r = s.registers.i32 r := by
    simp [LarkPtxDot.setFloat, LarkPtxDot.advance, putScalar, putValue, Registers.i32]
  refine ⟨h.active, h.memory, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [hi] using h.index
  · simpa only [hi] using h.batch
  · simpa only [hi] using h.batchA
  · simpa only [hi] using h.lane
  · simpa only [hi] using h.row
  · simpa only [LarkPtxDot.setFloat_pointer] using h.a
  · simpa only [LarkPtxDot.setFloat_pointer] using h.b
  · simpa only [LarkPtxDot.setFloat_pointer] using h.out

def Result (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (pc : Nat) (update : Machine α → Machine α) : Prop :=
  ∃ next, Steps ops layout geometry t program s next ∧ Frame t base next ∧
    next.pc = pc+1 ∧ next = update s

theorem instruction_step (ops : Ops α) (t pc : Nat) (s next : Machine α)
    (ins : LarkPtxMatrix.Instruction) (hpc : s.pc = pc) (hs : s.registers.stopped = false)
    (hi : program[pc]? = some ins)
    (he : LarkPtxMatrix.execute ops layout geometry t ins s = some next) :
    Steps ops layout geometry t program s next := by
  apply LarkPtxMatrix.one_step
  rw [LarkPtxMatrix.transition_at ops layout geometry t program s ins hs (by rw [hpc]; exact hi)]
  exact he

theorem produce32 (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (pc d : Nat) (v : Int) (ins : LarkPtxMatrix.Instruction)
    (h : Frame t base s) (hpc : s.pc = pc) (hi : program[pc]? = some ins)
    (he : LarkPtxMatrix.execute ops layout geometry t ins s = some (setIndex32 s d v))
    (hd : d ≠ 1 ∧ d ≠ 8 ∧ d ≠ 9 ∧ d ≠ 11 ∧ d ≠ 12) :
    Result ops t base s pc (fun m => setIndex32 m d v) := by
  refine ⟨setIndex32 s d v, instruction_step ops t pc s _ ins hpc h.active hi he,
    frame32 t base s d v h hd, ?_, rfl⟩
  change s.pc+1 = pc+1
  rw [hpc]

theorem produce64 (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (pc d : Nat) (v : Int) (ins : LarkPtxMatrix.Instruction)
    (h : Frame t base s) (hpc : s.pc = pc) (hi : program[pc]? = some ins)
    (he : LarkPtxMatrix.execute ops layout geometry t ins s = some (setIndex64 s d v))
    (hd : d ≠ 17 ∧ d ≠ 18 ∧ d ≠ 9) :
    Result ops t base s pc (fun m => setIndex64 m d v) := by
  refine ⟨setIndex64 s d v, instruction_step ops t pc s _ ins hpc h.active hi he,
    frame64 t base s d v h hd, ?_, rfl⟩
  change s.pc+1 = pc+1
  rw [hpc]

theorem produce_float (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (pc d : Nat) (v : α) (ins : LarkPtxMatrix.Instruction)
    (h : Frame t base s) (hpc : s.pc = pc) (hi : program[pc]? = some ins)
    (he : LarkPtxMatrix.execute ops layout geometry t ins s = some (setFloat s d v)) :
    Result ops t base s pc (fun m => setFloat m d v) := by
  refine ⟨setFloat s d v, instruction_step ops t pc s _ ins hpc h.active hi he,
    frame_float t base s d v h, ?_, rfl⟩
  change s.pc+1 = pc+1
  rw [hpc]

theorem row_sign (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 14) (ht : t < 1048576) :
    Result ops t base s 14 (fun m => setIndex32 m 13 0) := by
  have hb : signed32 (t : Int) := by unfold signed32; omega
  have e := LarkPtxMatrix.signed_right_step ops layout geometry t 13 11 31
    (t : Int) s h.lane hb
  have hp : (2 : Int)^min 31 32 = 2147483648 := by decide
  have hz : (t : Int)/2147483648 = 0 := by omega
  rw [hp, hz] at e
  exact produce32 ops t base s 14 13 0 (.shiftRightSigned32 13 11 31)
    h hpc (by rfl) e (by decide)

theorem row_correction (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 15) (h13 : s.registers.i32 13 = some 0) :
    Result ops t base s 15 (fun m => setIndex32 m 14 0) := by
  have e := LarkPtxMatrix.unsigned_right_step ops layout geometry t 14 13 26
    0 s h13 (by decide)
  have hz : (0 : Int)/(2 : Int)^min 26 32 = 0 := by decide
  rw [hz] at e
  exact produce32 ops t base s 15 14 0 (.shiftRightUnsigned32 14 13 26)
    h hpc (by rfl) e (by decide)

theorem prefix16_execute (ops : Ops α) (t : Nat) (base : State α) (ht : t < 1048576) :
    ∃ final, Steps ops layout geometry t program (start base) final ∧ Frame t base final ∧
      final.pc = 16 ∧ final.registers.i32 14 = some 0 := by
  obtain ⟨s15, first, f15, pc15, eq15⟩ :=
    row_sign ops t base (globalRow t base) (prefix_frame t base) (prefix_rows_pc t base) ht
  have r13 : s15.registers.i32 13 = some 0 := by rw [eq15]; simp
  obtain ⟨s16, second, f16, pc16, eq16⟩ := row_correction ops t base s15 f15 pc15 r13
  refine ⟨s16, ?_, f16, pc16, ?_⟩
  · exact LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ (prefix_rows_execute ops t base ht)
      (LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ first second)
  · rw [eq16]; simp

theorem row_adjust (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 16) (ht : t < 1048576)
    (h14 : s.registers.i32 14 = some 0) :
    Result ops t base s 16 (fun m => setIndex32 m 15 ((t/512 : Nat) : Int)) := by
  have hb : signed32 ((t/512 : Nat) : Int) ∧ signed32 0 ∧
      signed32 (((t/512 : Nat) : Int)+0) := by unfold signed32; omega
  have e := LarkPtxDot.add32_step ops layout geometry t 15 12 (.reg 14) s
    ((t/512 : Nat) : Int) 0 h.row h14 hb
  simp only [Int.add_zero] at e
  exact produce32 ops t base s 16 15 ((t/512 : Nat) : Int) (.base (.addSigned32 15 12 (.reg 14)))
    h hpc (by rfl) e (by decide)

theorem row_mask (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 17) (ht : t < 1048576)
    (h15 : s.registers.i32 15 = some ((t/512 : Nat) : Int)) :
    Result ops t base s 17 (fun m => setIndex32 m 16 ((t/512/64*64 : Nat) : Int)) := by
  have hb : unsigned32 ((t/512 : Nat) : Int) ∧ signed32 16777152 := by
    unfold unsigned32 signed32; omega
  have e := LarkPtxMatrix.and_step ops layout geometry t 16 15 (.imm 16777152)
    ((t/512 : Nat) : Int) 16777152 s h15 (by rfl) hb
  have hbits : LarkPtxMatrix.bits32 ((t/512 : Nat) : Int) = t/512 := by
    unfold LarkPtxMatrix.bits32
    have he : ((t/512 : Nat) : Int) % 4294967296 = ((t/512 : Nat) : Int) := by omega
    rw [he]; simp
  have hmask : LarkPtxMatrix.bits32 16777152 = 16777152 := by decide
  rw [hbits, hmask, clear_low6 (t/512) (by omega)] at e
  exact produce32 ops t base s 17 16 ((t/512/64*64 : Nat) : Int) (.andBits32 16 15 (.imm 16777152))
    h hpc (by rfl) e (by decide)

theorem local_row (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 18) (ht : t < 1048576)
    (h16 : s.registers.i32 16 = some ((t/512/64*64 : Nat) : Int)) :
    Result ops t base s 18 (fun m => setIndex32 m 17 (((t/512)%64 : Nat) : Int)) := by
  have hb : signed32 ((t/512 : Nat) : Int) ∧ signed32 ((t/512/64*64 : Nat) : Int) ∧
      signed32 (((t/512 : Nat) : Int)-((t/512/64*64 : Nat) : Int)) := by
    unfold signed32; simp only [Int.natCast_mul]; omega
  have e := LarkPtxMatrix.sub_step ops layout geometry t 17 12 (.reg 16)
    ((t/512 : Nat) : Int) ((t/512/64*64 : Nat) : Int) s h.row h16 hb
  have he : ((t/512 : Nat) : Int)-((t/512/64*64 : Nat) : Int) = (((t/512)%64 : Nat) : Int) := by
    simp only [Int.natCast_mul]; omega
  rw [he] at e
  exact produce32 ops t base s 18 17 (((t/512)%64 : Nat) : Int) (.subSigned32 17 12 (.reg 16))
    h hpc (by rfl) e (by decide)

theorem local_a_offset (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 19)
    (h17 : s.registers.i32 17 = some (((t/512)%64 : Nat) : Int)) :
    Result ops t base s 19 (fun m => setIndex32 m 18 (((t/512)%64*256 : Nat) : Int)) := by
  have hb : unsigned32 (((t/512)%64 : Nat) : Int) := by unfold unsigned32; omega
  have e := LarkPtxDot.shiftLeft_step ops layout geometry t 18 17 8 s
    (((t/512)%64 : Nat) : Int) h17 hb
  have hp : (2 : Int)^min 8 32 = 256 := by decide
  have he : ((((t/512)%64 : Nat) : Int)*256) % 4294967296 = (((t/512)%64*256 : Nat) : Int) := by
    simp only [Int.natCast_mul]; omega
  rw [hp, he] at e
  exact produce32 ops t base s 19 18 (((t/512)%64*256 : Nat) : Int) (.base (.shiftLeft32 18 17 8))
    h hpc (by rfl) e (by decide)

theorem column_mask (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 20) (ht : t < 1048576) :
    Result ops t base s 20 (fun m => setIndex32 m 19 ((t/512*512 : Nat) : Int)) := by
  have hb : unsigned32 (t : Int) ∧ signed32 (-512) := by unfold unsigned32 signed32; omega
  have e := LarkPtxMatrix.and_step ops layout geometry t 19 11 (.imm (-512))
    (t : Int) (-512) s h.lane (by rfl) hb
  have hbits : LarkPtxMatrix.bits32 (t : Int) = t := by
    unfold LarkPtxMatrix.bits32
    have he : (t : Int) % 4294967296 = (t : Int) := by omega
    rw [he]; simp
  rw [hbits, LarkPtxMatrix.bits32_negative512, LarkPtxMatrix.clear_low9 t (by omega)] at e
  exact produce32 ops t base s 20 19 ((t/512*512 : Nat) : Int) (.andBits32 19 11 (.imm (-512)))
    h hpc (by rfl) e (by decide)

theorem prefix21_execute (ops : Ops α) (t : Nat) (base : State α) (ht : t < 1048576) :
    ∃ final, Steps ops layout geometry t program (start base) final ∧ Frame t base final ∧
      final.pc = 21 ∧
      final.registers.i32 18 = some (((t/512)%64*256 : Nat) : Int) ∧
      final.registers.i32 19 = some ((t/512*512 : Nat) : Int) := by
  obtain ⟨s16, first, f16, pc16, r14⟩ := prefix16_execute ops t base ht
  obtain ⟨s17, e17, f17, pc17, eq17⟩ := row_adjust ops t base s16 f16 pc16 ht r14
  have r15 : s17.registers.i32 15 = some ((t/512 : Nat) : Int) := by rw [eq17]; simp
  obtain ⟨s18, e18, f18, pc18, eq18⟩ := row_mask ops t base s17 f17 pc17 ht r15
  have r16 : s18.registers.i32 16 = some ((t/512/64*64 : Nat) : Int) := by rw [eq18]; simp
  obtain ⟨s19, e19, f19, pc19, eq19⟩ := local_row ops t base s18 f18 pc18 ht r16
  have r17 : s19.registers.i32 17 = some (((t/512)%64 : Nat) : Int) := by rw [eq19]; simp
  obtain ⟨s20, e20, f20, pc20, eq20⟩ := local_a_offset ops t base s19 f19 pc19 r17
  have r18 : s20.registers.i32 18 = some (((t/512)%64*256 : Nat) : Int) := by rw [eq20]; simp
  obtain ⟨s21, e21, f21, pc21, eq21⟩ := column_mask ops t base s20 f20 pc20 ht
  refine ⟨s21, ?_, f21, pc21, ?_, ?_⟩
  · exact LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ first
      (LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ e17
        (LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ e18
          (LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ e19
            (LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ e20 e21))))
  · rw [eq21]; simpa using r18
  · rw [eq21]; simp

end LarkPtxBatched.Bmm.Init

#print axioms LarkPtxBatched.Bmm.Init.prefix_frame
#print axioms LarkPtxBatched.Bmm.Init.frame32
#print axioms LarkPtxBatched.Bmm.Init.frame64
#print axioms LarkPtxBatched.Bmm.Init.frame_float
#print axioms LarkPtxBatched.Bmm.Init.produce32
#print axioms LarkPtxBatched.Bmm.Init.produce64
#print axioms LarkPtxBatched.Bmm.Init.produce_float
#print axioms LarkPtxBatched.Bmm.Init.row_sign
#print axioms LarkPtxBatched.Bmm.Init.row_correction
#print axioms LarkPtxBatched.Bmm.Init.prefix16_execute
#print axioms LarkPtxBatched.Bmm.Init.row_adjust
#print axioms LarkPtxBatched.Bmm.Init.row_mask
#print axioms LarkPtxBatched.Bmm.Init.local_row
#print axioms LarkPtxBatched.Bmm.Init.local_a_offset
#print axioms LarkPtxBatched.Bmm.Init.column_mask
#print axioms LarkPtxBatched.Bmm.Init.prefix21_execute
