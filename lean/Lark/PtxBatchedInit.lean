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

theorem column (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 21) (ht : t < 1048576)
    (h19 : s.registers.i32 19 = some ((t/512*512 : Nat) : Int)) :
    Result ops t base s 21 (fun m => setIndex32 m 20 ((t%512 : Nat) : Int)) := by
  have hb : signed32 (t : Int) ∧ signed32 ((t/512*512 : Nat) : Int) ∧
      signed32 ((t : Int)-((t/512*512 : Nat) : Int)) := by
    unfold signed32; simp only [Int.natCast_mul]; omega
  have e := LarkPtxMatrix.sub_step ops layout geometry t 20 1 (.reg 19)
    (t : Int) ((t/512*512 : Nat) : Int) s h.index h19 hb
  have he : (t : Int)-((t/512*512 : Nat) : Int) = ((t%512 : Nat) : Int) := by
    simp only [Int.natCast_mul]; omega
  rw [he] at e
  exact produce32 ops t base s 21 20 ((t%512 : Nat) : Int) (.subSigned32 20 1 (.reg 19))
    h hpc (by rfl) e (by decide)

theorem batch_b_offset (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 22) (ht : t < 1048576) :
    Result ops t base s 22 (fun m => setIndex32 m 21 ((t/32768*131072 : Nat) : Int)) := by
  have hb : unsigned32 ((t/32768 : Nat) : Int) := by unfold unsigned32; omega
  have e := LarkPtxDot.shiftLeft_step ops layout geometry t 21 8 17 s
    ((t/32768 : Nat) : Int) h.batch hb
  have hp : (2 : Int)^min 17 32 = 131072 := by decide
  have he : (((t/32768 : Nat) : Int)*131072) % 4294967296 =
      ((t/32768*131072 : Nat) : Int) := by
    simp only [Int.natCast_mul]; omega
  rw [hp, he] at e
  exact produce32 ops t base s 22 21 ((t/32768*131072 : Nat) : Int)
    (.base (.shiftLeft32 21 8 17)) h hpc (by rfl) e (by decide)

theorem b_base_offset (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 23) (ht : t < 1048576)
    (h20 : s.registers.i32 20 = some ((t%512 : Nat) : Int))
    (h21 : s.registers.i32 21 = some ((t/32768*131072 : Nat) : Int)) :
    Result ops t base s 23 (fun m => setIndex32 m 22 ((bIndex t 0 : Nat) : Int)) := by
  have hb : signed32 ((t%512 : Nat) : Int) ∧ signed32 ((t/32768*131072 : Nat) : Int) ∧
      signed32 (((t%512 : Nat) : Int)+((t/32768*131072 : Nat) : Int)) := by
    unfold signed32; simp only [Int.natCast_mul]; omega
  have e := LarkPtxDot.add32_step ops layout geometry t 22 20 (.reg 21) s
    ((t%512 : Nat) : Int) ((t/32768*131072 : Nat) : Int) h20 h21 hb
  have he : ((t%512 : Nat) : Int)+((t/32768*131072 : Nat) : Int) =
      ((bIndex t 0 : Nat) : Int) := by simp [bIndex]; omega
  rw [he] at e
  exact produce32 ops t base s 23 22 ((bIndex t 0 : Nat) : Int)
    (.base (.addSigned32 22 20 (.reg 21))) h hpc (by rfl) e (by decide)

theorem a_base_offset (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 24) (ht : t < 1048576)
    (h18 : s.registers.i32 18 = some (((t/512)%64*256 : Nat) : Int)) :
    Result ops t base s 24 (fun m => setIndex32 m 23 ((aIndex t 0 : Nat) : Int)) := by
  have hb : signed32 ((t/32768*16384 : Nat) : Int) ∧
      signed32 (((t/512)%64*256 : Nat) : Int) ∧
      signed32 (((t/32768*16384 : Nat) : Int)+(((t/512)%64*256 : Nat) : Int)) := by
    unfold signed32; simp only [Int.natCast_mul]; omega
  have e := LarkPtxDot.add32_step ops layout geometry t 23 9 (.reg 18) s
    ((t/32768*16384 : Nat) : Int) (((t/512)%64*256 : Nat) : Int) h.batchA h18 hb
  have he : ((t/32768*16384 : Nat) : Int)+(((t/512)%64*256 : Nat) : Int) =
      ((aIndex t 0 : Nat) : Int) := by simp [aIndex]
  rw [he] at e
  exact produce32 ops t base s 24 23 ((aIndex t 0 : Nat) : Int)
    (.base (.addSigned32 23 9 (.reg 18))) h hpc (by rfl) e (by decide)

theorem b_wide_offset (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 25) (ht : t < 1048576)
    (h22 : s.registers.i32 22 = some ((bIndex t 0 : Nat) : Int)) :
    Result ops t base s 25 (fun m => setIndex64 m 3 (((bIndex t 0 : Nat) : Int)*2)) := by
  have hb : signed32 ((bIndex t 0 : Nat) : Int) ∧ signed32 2 ∧
      signed64 (((bIndex t 0 : Nat) : Int)*2) := by
    have bounds := input_indices_valid t 0 ht (by decide)
    unfold signed32 signed64; omega
  have e := LarkPtxDot.wide_step ops layout geometry t 3 22 2
    ((bIndex t 0 : Nat) : Int) s h22 hb
  exact produce64 ops t base s 25 3 (((bIndex t 0 : Nat) : Int)*2)
    (.base (.mulWideSigned32 3 22 2)) h hpc (by rfl) e (by decide)

theorem a_wide_offset (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 26) (ht : t < 1048576)
    (h23 : s.registers.i32 23 = some ((aIndex t 0 : Nat) : Int)) :
    Result ops t base s 26 (fun m => setIndex64 m 4 (((aIndex t 0 : Nat) : Int)*2)) := by
  have hb : signed32 ((aIndex t 0 : Nat) : Int) ∧ signed32 2 ∧
      signed64 (((aIndex t 0 : Nat) : Int)*2) := by
    have bounds := input_indices_valid t 0 ht (by decide)
    unfold signed32 signed64; omega
  have e := LarkPtxDot.wide_step ops layout geometry t 4 23 2
    ((aIndex t 0 : Nat) : Int) s h23 hb
  exact produce64 ops t base s 26 4 (((aIndex t 0 : Nat) : Int)*2)
    (.base (.mulWideSigned32 4 23 2)) h hpc (by rfl) e (by decide)

theorem zero_accumulator (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 27) :
    Result ops t base s 27 (fun m => setFloat m 68 (ops.literal 0 1)) := by
  exact produce_float ops t base s 27 68 (ops.literal 0 1) (.base (.literalFloat 68 0 1))
    h hpc (by rfl) (LarkPtxMatrix.zero_float_step ops layout geometry t 68 s)

theorem zero_counter (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 28) :
    Result ops t base s 28 (fun m => setIndex32 m 24 0) := by
  exact produce32 ops t base s 28 24 0 (.base (.literal32 24 0))
    h hpc (by rfl) (LarkPtxMatrix.zero_index_step ops layout geometry t 24 s) (by decide)

structure Ready (ops : Ops α) (t : Nat) (base : State α) (s : Machine α) : Prop where
  frame : Frame t base s
  pc : s.pc = 29
  bOffset : s.registers.i64 3 = some (((bIndex t 0 : Nat) : Int)*2)
  aOffset : s.registers.i64 4 = some (((aIndex t 0 : Nat) : Int)*2)
  accumulator : s.registers.scalar 68 = some (ops.literal 0 1)
  counter : s.registers.i32 24 = some 0

theorem prefix29_execute (ops : Ops α) (t : Nat) (base : State α) (ht : t < 1048576) :
    ∃ final, Steps ops layout geometry t program (start base) final ∧ Ready ops t base final := by
  obtain ⟨s21, first, f21, pc21, r18, r19⟩ := prefix21_execute ops t base ht
  obtain ⟨s22, e22, f22, pc22, eq22⟩ := column ops t base s21 f21 pc21 ht r19
  have r20 : s22.registers.i32 20 = some ((t%512 : Nat) : Int) := by rw [eq22]; simp
  have a22 : s22.registers.i32 18 = some (((t/512)%64*256 : Nat) : Int) := by
    rw [eq22]; simpa using r18
  obtain ⟨s23, e23, f23, pc23, eq23⟩ := batch_b_offset ops t base s22 f22 pc22 ht
  have r21 : s23.registers.i32 21 = some ((t/32768*131072 : Nat) : Int) := by rw [eq23]; simp
  have col23 : s23.registers.i32 20 = some ((t%512 : Nat) : Int) := by rw [eq23]; simpa using r20
  have a23 : s23.registers.i32 18 = some (((t/512)%64*256 : Nat) : Int) := by
    rw [eq23]; simpa using a22
  obtain ⟨s24, e24, f24, pc24, eq24⟩ := b_base_offset ops t base s23 f23 pc23 ht col23 r21
  have r22 : s24.registers.i32 22 = some ((bIndex t 0 : Nat) : Int) := by rw [eq24]; simp
  have a24 : s24.registers.i32 18 = some (((t/512)%64*256 : Nat) : Int) := by
    rw [eq24]; simpa using a23
  obtain ⟨s25, e25, f25, pc25, eq25⟩ := a_base_offset ops t base s24 f24 pc24 ht a24
  have r23 : s25.registers.i32 23 = some ((aIndex t 0 : Nat) : Int) := by rw [eq25]; simp
  have b25 : s25.registers.i32 22 = some ((bIndex t 0 : Nat) : Int) := by rw [eq25]; simpa using r22
  obtain ⟨s26, e26, f26, pc26, eq26⟩ := b_wide_offset ops t base s25 f25 pc25 ht b25
  have r3 : s26.registers.i64 3 = some (((bIndex t 0 : Nat) : Int)*2) := by rw [eq26]; simp
  have a26 : s26.registers.i32 23 = some ((aIndex t 0 : Nat) : Int) := by rw [eq26]; simpa using r23
  obtain ⟨s27, e27, f27, pc27, eq27⟩ := a_wide_offset ops t base s26 f26 pc26 ht a26
  have r4 : s27.registers.i64 4 = some (((aIndex t 0 : Nat) : Int)*2) := by rw [eq27]; simp
  have b27 : s27.registers.i64 3 = some (((bIndex t 0 : Nat) : Int)*2) := by rw [eq27]; simpa using r3
  obtain ⟨s28, e28, f28, pc28, eq28⟩ := zero_accumulator ops t base s27 f27 pc27
  have acc : s28.registers.scalar 68 = some (ops.literal 0 1) := by rw [eq28]; simp
  have b28 : s28.registers.i64 3 = some (((bIndex t 0 : Nat) : Int)*2) := by rw [eq28]; simpa using b27
  have a28 : s28.registers.i64 4 = some (((aIndex t 0 : Nat) : Int)*2) := by rw [eq28]; simpa using r4
  obtain ⟨s29, e29, f29, pc29, eq29⟩ := zero_counter ops t base s28 f28 pc28
  refine ⟨s29, ?_, f29, pc29, ?_, ?_, ?_, ?_⟩
  · exact LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ first
      (LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ e22
        (LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ e23
          (LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ e24
            (LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ e25
              (LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ e26
                (LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ e27
                  (LarkPtxMatrix.steps_trans _ _ _ _ _ _ _ _ e28 e29)))))))
  · rw [eq29]; simpa using b28
  · rw [eq29]; simpa using a28
  · rw [eq29]; simpa using acc
  · rw [eq29]; simp

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
#print axioms LarkPtxBatched.Bmm.Init.column
#print axioms LarkPtxBatched.Bmm.Init.batch_b_offset
#print axioms LarkPtxBatched.Bmm.Init.b_base_offset
#print axioms LarkPtxBatched.Bmm.Init.a_base_offset
#print axioms LarkPtxBatched.Bmm.Init.b_wide_offset
#print axioms LarkPtxBatched.Bmm.Init.a_wide_offset
#print axioms LarkPtxBatched.Bmm.Init.zero_accumulator
#print axioms LarkPtxBatched.Bmm.Init.zero_counter
#print axioms LarkPtxBatched.Bmm.Init.prefix29_execute
