import Lark.PtxLinear

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

/- Original-size Linear initialization. Actual instruction sequences, guarded
   address arithmetic and frame preservation; no instruction/loop summary is
   assumed. This is development evidence, not a complete kernel certificate. -/
namespace LarkPtxLinear.Linear.Init
open LarkNonlinear LarkPtxPointwise
open LarkPtxDot (Machine setPointer setIndex32 setFloat unsigned32 add32_step
  setIndex32_i32 setFloat_pointer setIndex32_pc setFloat_pc setFloat_stopped wide_step)
open LarkPtxMatrix (setIndex64 setIndex64_i32 setIndex32_i64 setIndex64_i64
  setIndex64_pc setIndex64_base setIndex32_base setPointer_base
  setIndex64_stopped setIndex32_stopped setPointer_i64 setIndex64_pointer
  setIndex32_pointer setFloat_i64 setFloat_i32 zero_float_step zero_index_step
  unsigned_wide_step)

structure Frame (t : Nat) (base : State α) (s : Machine α) : Prop where
  active : s.registers.stopped = false
  memory : s.registers.base = base
  thread : s.registers.i32 1 = some (t : Int)
  row : s.registers.i32 9 = some ((t/512*256 : Nat) : Int)
  column : s.registers.i32 11 = some ((t%512 : Nat) : Int)
  a : s.registers.pointer 52 = some ⟨0, 0, true⟩
  b : s.registers.pointer 53 = some ⟨1, 0, true⟩
  out : s.registers.pointer 3 = some ⟨3, 0, true⟩
  bias : s.registers.pointer 26 = some ⟨2, 0, false⟩

theorem prefix_frame (t : Nat) (base : State α) : Frame t base (coordinates t base) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem frame32 (t : Nat) (base : State α) (s : Machine α) (d : Nat) (v : Int)
    (h : Frame t base s) (hd : d ≠ 1 ∧ d ≠ 9 ∧ d ≠ 11) :
    Frame t base (setIndex32 s d v) := by
  rcases hd with ⟨h1, h9, h11⟩
  refine ⟨h.active, h.memory, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [setIndex32_i32, if_neg (Ne.symm h1)] using h.thread
  · simpa only [setIndex32_i32, if_neg (Ne.symm h9)] using h.row
  · simpa only [setIndex32_i32, if_neg (Ne.symm h11)] using h.column
  · simpa only [setIndex32_pointer] using h.a
  · simpa only [setIndex32_pointer] using h.b
  · simpa only [setIndex32_pointer] using h.out
  · simpa only [setIndex32_pointer] using h.bias

theorem frame64 (t : Nat) (base : State α) (s : Machine α) (d : Nat) (v : Int)
    (h : Frame t base s) (hd : d ≠ 52 ∧ d ≠ 53 ∧ d ≠ 3 ∧ d ≠ 26) :
    Frame t base (setIndex64 s d v) := by
  rcases hd with ⟨ha, hb, ho, hc⟩
  refine ⟨h.active, h.memory, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [setIndex64_i32] using h.thread
  · simpa only [setIndex64_i32] using h.row
  · simpa only [setIndex64_i32] using h.column
  · simpa only [setIndex64_pointer, if_neg (Ne.symm ha)] using h.a
  · simpa only [setIndex64_pointer, if_neg (Ne.symm hb)] using h.b
  · simpa only [setIndex64_pointer, if_neg (Ne.symm ho)] using h.out
  · simpa only [setIndex64_pointer, if_neg (Ne.symm hc)] using h.bias

theorem frame_float (t : Nat) (base : State α) (s : Machine α) (d : Nat) (v : α)
    (h : Frame t base s) : Frame t base (setFloat s d v) := by
  refine ⟨h.active, h.memory, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [setFloat_i32] using h.thread
  · simpa only [setFloat_i32] using h.row
  · simpa only [setFloat_i32] using h.column
  · simpa only [setFloat_pointer] using h.a
  · simpa only [setFloat_pointer] using h.b
  · simpa only [setFloat_pointer] using h.out
  · simpa only [setFloat_pointer] using h.bias

def addressPair (j t : Nat) (s : Machine α) : Machine α :=
  setIndex64 (setIndex32 s (12+j) ((t%512+(15-j)*512 : Nat) : Int))
    (4+j) (((t%512+(15-j)*512)*2 : Nat) : Int)

theorem program_pair : ∀ (j : Fin 14),
    program[15+2*j.val]? = some (.base (.base (.addSigned32 (12+j.val) 11
      (.imm (((15-j.val)*512 : Nat) : Int))))) ∧
    program[16+2*j.val]? = some (.base (.mulWideUnsigned32 (4+j.val) (12+j.val) 2)) := by decide

theorem address_pair_execute (ops : Ops α) (t j : Nat) (s : Machine α)
    (hj : j < 14) (hpc : s.pc = 15+2*j) (hs : s.registers.stopped = false)
    (hc : s.registers.i32 11 = some ((t%512 : Nat) : Int)) :
    Steps ops layout geometry t program s (addressPair j t s) := by
  have hcol : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hoff : (15-j)*512 ≤ 7680 := by omega
  have hb : signed32 ((t%512 : Nat) : Int) ∧ signed32 (((15-j)*512 : Nat) : Int) ∧
      signed32 (((t%512 : Nat) : Int)+(((15-j)*512 : Nat) : Int)) := by
    unfold signed32; omega
  have e1 := add32_step ops layout geometry t (12+j) 11 (.imm (((15-j)*512 : Nat) : Int))
    s ((t%512 : Nat) : Int) (((15-j)*512 : Nat) : Int) hc (by rfl) hb
  have e1' : LarkPtxDot.execute ops layout geometry t
      (.addSigned32 (12+j) 11 (.imm (((15-j)*512 : Nat) : Int))) s =
      some (setIndex32 s (12+j) ((t%512+(15-j)*512 : Nat) : Int)) := by
    simpa only [Int.natCast_add] using e1
  have h1 : Steps ops layout geometry t program s
      (setIndex32 s (12+j) ((t%512+(15-j)*512 : Nat) : Int)) := by
    apply one_step
    rw [transition_at ops layout geometry t program s
      (.base (.base (.addSigned32 (12+j) 11 (.imm (((15-j)*512 : Nat) : Int))))) hs
      (by rw [hpc]; exact (program_pair ⟨j, hj⟩).1), dot_step]
    exact e1'
  have hw : unsigned32 ((t%512+(15-j)*512 : Nat) : Int) ∧ unsigned32 2 ∧
      signed64 (((t%512+(15-j)*512 : Nat) : Int)*2) := by
    unfold unsigned32 signed64; simp only [Int.natCast_add]; omega
  have e2 := unsigned_wide_step ops layout geometry t (4+j) (12+j) 2
    ((t%512+(15-j)*512 : Nat) : Int)
    (setIndex32 s (12+j) ((t%512+(15-j)*512 : Nat) : Int)) (by simp) hw
  have e2' : execute ops layout geometry t (.base (.mulWideUnsigned32 (4+j) (12+j) 2))
      (setIndex32 s (12+j) ((t%512+(15-j)*512 : Nat) : Int)) =
      some (addressPair j t s) := by
    simpa only [addressPair, setIndex64, Int.natCast_mul] using e2
  apply steps_trans _ _ _ _ _ _ _ _ h1
  apply one_step
  rw [transition_at ops layout geometry t program
    (setIndex32 s (12+j) ((t%512+(15-j)*512 : Nat) : Int))
    (.base (.mulWideUnsigned32 (4+j) (12+j) 2))
    (by change s.registers.stopped = false; exact hs)]
  · exact e2'
  · change program[s.pc+1]? = _
    rw [hpc]
    have he : 15+2*j+1 = 16+2*j := by omega
    rw [he]
    exact (program_pair ⟨j, hj⟩).2

def addressPairs (t : Nat) (s : State α) : Nat → Machine α
  | 0 => coordinates t s
  | j+1 => addressPair j t (addressPairs t s j)

theorem addressPairs_pc (t j : Nat) (s : State α) :
    (addressPairs t s j).pc = 15+2*j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change ((addressPairs t s j).pc+1)+1 = 15+2*(j+1)
      omega

theorem addressPairs_stopped (t j : Nat) (s : State α) :
    (addressPairs t s j).registers.stopped = false := by
  induction j with
  | zero => rfl
  | succ j ih =>
      change (addressPairs t s j).registers.stopped = false
      exact ih

theorem addressPairs_column (t j : Nat) (s : State α) :
    (addressPairs t s j).registers.i32 11 = some ((t%512 : Nat) : Int) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [addressPairs, addressPair, setIndex64_i32, setIndex32_i32]
      rw [if_neg (by omega)]
      exact ih

theorem addressPairs_execute (ops : Ops α) (t j : Nat) (s : State α)
    (ht : t < 32768) (hj : j ≤ 14) :
    Steps ops layout geometry t program (start s) (addressPairs t s j) := by
  induction j with
  | zero => exact coordinates_execute ops t s ht
  | succ j ih =>
      have hp := ih (by omega)
      have hn := address_pair_execute ops t j (addressPairs t s j) (by omega)
        (addressPairs_pc t j s) (addressPairs_stopped t j s) (addressPairs_column t j s)
      exact steps_trans _ _ _ _ _ _ _ _ hp hn

theorem addressPairs_row_offset (t j : Nat) (s : State α) :
    (addressPairs t s j).registers.i32 9 = some ((t/512*256 : Nat) : Int) := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [addressPairs, addressPair, setIndex64_i32, setIndex32_i32]
      rw [if_neg (by omega)]
      exact ih

theorem addressPairs_base (t j : Nat) (s : State α) :
    (addressPairs t s j).registers.base = s := by
  induction j with
  | zero => exact coordinates_base t s
  | succ j ih =>
      simpa only [addressPairs, addressPair, setIndex64_base, setIndex32_base] using ih

theorem addressPairs_i64 (t n r : Nat) (s : State α) (hn : n ≤ 14) :
    (addressPairs t s n).registers.i64 r =
      if 4 ≤ r ∧ r < 4+n then some (((t%512+(19-r)*512)*2 : Nat) : Int)
      else (coordinates t s).registers.i64 r := by
  induction n with
  | zero => simp only [addressPairs, Nat.add_zero, if_neg (by omega : ¬(4 ≤ r ∧ r < 4))]
  | succ n ih =>
      simp only [addressPairs, addressPair, setIndex64_i64, setIndex32_i64]
      by_cases he : r = 4+n
      · subst r
        rw [if_pos rfl, if_pos (by omega)]
        have hs : 19-(4+n) = 15-n := by omega
        rw [hs]
      · rw [if_neg he, ih (by omega)]
        have hs : (4 ≤ r ∧ r < 4+(n+1)) ↔ (4 ≤ r ∧ r < 4+n) := by omega
        simp only [hs]
theorem addressPairs_frame (t j : Nat) (base : State α) (hj : j ≤ 14) :
    Frame t base (addressPairs t base j) := by
  induction j with
  | zero => exact prefix_frame t base
  | succ j ih =>
      have prev := ih (by omega)
      unfold addressPairs addressPair
      apply frame64
      · apply frame32
        · exact prev
        · omega
      · omega

def columnSigned (t : Nat) (s : Machine α) : Machine α :=
  setIndex64 s 18 ((t%512 : Nat) : Int)

def columnWide (t : Nat) (s : Machine α) : Machine α :=
  setIndex64 (columnSigned t s) 19 ((t%512*2 : Nat) : Int)
def nextColumn (t : Nat) (s : Machine α) : Machine α :=
  setIndex32 (columnWide t s) 26 ((t%512+512 : Nat) : Int)
def nextWide (t : Nat) (s : Machine α) : Machine α :=
  setIndex64 (nextColumn t s) 20 (((t%512+512)*2 : Nat) : Int)
def matrixWide (t : Nat) (s : Machine α) : Machine α :=
  setIndex64 (nextWide t s) 21 (((t/512*256)*2 : Nat) : Int)
def zeroAccumulator (ops : Ops α) (t : Nat) (s : Machine α) : Machine α :=
  setFloat (matrixWide t s) 69 (ops.literal 0 1)
def initializedSuffix (ops : Ops α) (t : Nat) (s : Machine α) : Machine α :=
  setIndex32 (zeroAccumulator ops t s) 27 0

theorem column_signed_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (hpc : s.pc = 43) (hs : s.registers.stopped = false)
    (hcol : s.registers.i32 11 = some ((t%512 : Nat) : Int)) :
    Steps ops layout geometry t program s (columnSigned t s) := by
  have hc : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hb : signed32 ((t%512 : Nat) : Int) := by unfold signed32; omega
  have e := signExtend32_step ops layout geometry t 18 11 ((t%512 : Nat) : Int) s hcol hb
  apply one_step
  rw [transition_at ops layout geometry t program s (.signExtend32 18 11)
    hs (by rw [hpc]; rfl)]
  exact e

theorem column_wide_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (hpc : s.pc = 43) (hs : s.registers.stopped = false)
    (hcol : s.registers.i32 11 = some ((t%512 : Nat) : Int)) :
    Steps ops layout geometry t program (columnSigned t s) (columnWide t s) := by
  have hc : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hb : signed32 ((t%512 : Nat) : Int) ∧ signed32 2 ∧
      signed64 (((t%512 : Nat) : Int)*2) := by unfold signed32 signed64; omega
  have hcol' : (columnSigned t s).registers.i32 11 = some ((t%512 : Nat) : Int) := by
    simpa only [columnSigned, setIndex64_i32] using hcol
  have e := LarkPtxDot.wide_step ops layout geometry t 19 11 2 ((t%512 : Nat) : Int)
    (columnSigned t s) hcol' hb
  have e' : LarkPtxDot.execute ops layout geometry t (.mulWideSigned32 19 11 2)
      (columnSigned t s) = some (columnWide t s) := by
    simpa only [columnWide, columnSigned, setIndex64, Int.natCast_mul] using e
  have hp : (columnSigned t s).pc = 44 := by simp only [columnSigned, setIndex64_pc, hpc]
  apply one_step
  rw [transition_at ops layout geometry t program (columnSigned t s)
    (.base (.base (.mulWideSigned32 19 11 2)))
    (by simpa only [columnSigned, setIndex64_stopped] using hs) (by rw [hp]; rfl), dot_step]
  exact e'

#print axioms LarkPtxLinear.Linear.Init.column_wide_execute

theorem next_column_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (hpc : s.pc = 43) (hs : s.registers.stopped = false)
    (hcol : s.registers.i32 11 = some ((t%512 : Nat) : Int)) :
    Steps ops layout geometry t program (columnWide t s) (nextColumn t s) := by
  have hc : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hb : signed32 ((t%512 : Nat) : Int) ∧ signed32 512 ∧
      signed32 (((t%512 : Nat) : Int)+512) := by unfold signed32; omega
  have hx : (columnWide t s).registers.i32 11 = some ((t%512 : Nat) : Int) := by
    simpa only [columnWide, columnSigned, setIndex64_i32] using hcol
  have e := add32_step ops layout geometry t 26 11 (.imm 512) (columnWide t s)
    ((t%512 : Nat) : Int) 512 hx (by rfl) hb
  have e' : LarkPtxDot.execute ops layout geometry t (.addSigned32 26 11 (.imm 512))
      (columnWide t s) = some (nextColumn t s) := by
    simpa only [nextColumn, Int.natCast_add] using e
  have hp : (columnWide t s).pc = 45 := by
    simp only [columnWide, columnSigned, setIndex64_pc, hpc]
  apply one_step
  rw [transition_at ops layout geometry t program (columnWide t s)
    (.base (.base (.addSigned32 26 11 (.imm 512))))
    (by simpa only [columnWide, columnSigned, setIndex64_stopped] using hs) (by rw [hp]; rfl), dot_step]
  exact e'

#print axioms LarkPtxLinear.Linear.Init.next_column_execute

theorem next_wide_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (hpc : s.pc = 43) (hs : s.registers.stopped = false) :
    Steps ops layout geometry t program (nextColumn t s) (nextWide t s) := by
  have hc : t%512 < 512 := Nat.mod_lt _ (by decide)
  have hb : unsigned32 ((t%512+512 : Nat) : Int) ∧ unsigned32 2 ∧
      signed64 (((t%512+512 : Nat) : Int)*2) := by
    unfold unsigned32 signed64; simp only [Int.natCast_add]; omega
  have e := unsigned_wide_step ops layout geometry t 20 26 2 ((t%512+512 : Nat) : Int)
    (nextColumn t s) (by simp [nextColumn]) hb
  have e' : execute ops layout geometry t (.base (.mulWideUnsigned32 20 26 2)) (nextColumn t s) =
      some (nextWide t s) := by
    simpa only [nextWide, setIndex64, Int.natCast_mul] using e
  have hp : (nextColumn t s).pc = 46 := by
    simp only [nextColumn, columnWide, columnSigned, setIndex32_pc, setIndex64_pc, hpc]
  apply one_step
  rw [transition_at ops layout geometry t program (nextColumn t s) (.base (.mulWideUnsigned32 20 26 2))
    (by simpa only [nextColumn, columnWide, columnSigned, setIndex32_stopped, setIndex64_stopped] using hs)
    (by rw [hp]; rfl)]
  exact e'

#print axioms LarkPtxLinear.Linear.Init.next_wide_execute

theorem matrix_wide_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (ht : t < 32768) (hpc : s.pc = 43) (hs : s.registers.stopped = false)
    (hrow : s.registers.i32 9 = some ((t/512*256 : Nat) : Int)) :
    Steps ops layout geometry t program (nextWide t s) (matrixWide t s) := by
  have hr : t/512 < 64 := by omega
  have hb : signed32 ((t/512*256 : Nat) : Int) ∧ signed32 2 ∧
      signed64 (((t/512*256 : Nat) : Int)*2) := by
    unfold signed32 signed64; simp only [Int.natCast_mul]; omega
  have hx : (nextWide t s).registers.i32 9 = some ((t/512*256 : Nat) : Int) := by
    simpa only [nextWide, nextColumn, columnWide, columnSigned, setIndex64_i32, setIndex32_i32] using hrow
  have e := wide_step ops layout geometry t 21 9 2 ((t/512*256 : Nat) : Int) (nextWide t s) hx hb
  have e' : LarkPtxDot.execute ops layout geometry t (.mulWideSigned32 21 9 2) (nextWide t s) =
      some (matrixWide t s) := by
    simpa only [matrixWide, setIndex64, Int.natCast_mul] using e
  have hp : (nextWide t s).pc = 47 := by
    simp only [nextWide, nextColumn, columnWide, columnSigned, setIndex32_pc, setIndex64_pc, hpc]
  apply one_step
  rw [transition_at ops layout geometry t program (nextWide t s) (.base (.base (.mulWideSigned32 21 9 2)))
    (by simpa only [nextWide, nextColumn, columnWide, columnSigned, setIndex32_stopped, setIndex64_stopped] using hs)
    (by rw [hp]; rfl), dot_step]
  exact e'

#print axioms LarkPtxLinear.Linear.Init.matrix_wide_execute

theorem zero_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (hpc : s.pc = 43) (hs : s.registers.stopped = false) :
    Steps ops layout geometry t program (matrixWide t s) (zeroAccumulator ops t s) := by
  have hp : (matrixWide t s).pc = 48 := by
    simp only [matrixWide, nextWide, nextColumn, columnWide, columnSigned, setIndex32_pc, setIndex64_pc, hpc]
  have hstop : (matrixWide t s).registers.stopped = false := by
    simpa only [matrixWide, nextWide, nextColumn, columnWide, columnSigned, setIndex32_stopped, setIndex64_stopped] using hs
  apply one_step
  rw [transition_at ops layout geometry t program (matrixWide t s) (.base (.base (.literalFloat 69 0 1)))
    hstop (by rw [hp]; rfl), dot_step]
  exact zero_float_step ops layout geometry t 69 (matrixWide t s)

#print axioms LarkPtxLinear.Linear.Init.zero_execute

theorem initialize_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (hpc : s.pc = 43) (hs : s.registers.stopped = false) :
    Steps ops layout geometry t program (zeroAccumulator ops t s) (initializedSuffix ops t s) := by
  have hp : (zeroAccumulator ops t s).pc = 49 := by
    simp only [zeroAccumulator, matrixWide, nextWide, nextColumn, columnWide, columnSigned,
      setFloat_pc, setIndex32_pc, setIndex64_pc, hpc]
  have hstop : (zeroAccumulator ops t s).registers.stopped = false := by
    simpa only [zeroAccumulator, matrixWide, nextWide, nextColumn, columnWide, columnSigned,
      setFloat_stopped, setIndex32_stopped, setIndex64_stopped] using hs
  apply one_step
  rw [transition_at ops layout geometry t program (zeroAccumulator ops t s) (.base (.base (.literal32 27 0)))
    hstop (by rw [hp]; rfl), dot_step]
  exact zero_index_step ops layout geometry t 27 (zeroAccumulator ops t s)

#print axioms LarkPtxLinear.Linear.Init.initialize_execute

theorem suffix_execute (ops : Ops α) (t : Nat) (s : Machine α)
    (ht : t < 32768) (hpc : s.pc = 43) (hs : s.registers.stopped = false)
    (hcol : s.registers.i32 11 = some ((t%512 : Nat) : Int))
    (hrow : s.registers.i32 9 = some ((t/512*256 : Nat) : Int)) :
    Steps ops layout geometry t program s (initializedSuffix ops t s) := by
  apply steps_trans _ _ _ _ _ _ _ _ (column_signed_execute ops t s hpc hs hcol)
  apply steps_trans _ _ _ _ _ _ _ _ (column_wide_execute ops t s hpc hs hcol)
  apply steps_trans _ _ _ _ _ _ _ _ (next_column_execute ops t s hpc hs hcol)
  apply steps_trans _ _ _ _ _ _ _ _ (next_wide_execute ops t s hpc hs)
  apply steps_trans _ _ _ _ _ _ _ _ (matrix_wide_execute ops t s ht hpc hs hrow)
  exact steps_trans _ _ _ _ _ _ _ _ (zero_execute ops t s hpc hs) (initialize_execute ops t s hpc hs)

def strideRegister (j : Nat) : Nat := if j = 0 then 19 else if j = 1 then 20 else 19-j
def bStride (t j : Nat) : Int := (((t%512+j*512)*2 : Nat) : Int)

structure Ready (ops : Ops α) (t : Nat) (base : State α) (s : Machine α) : Prop where
  frame : Frame t base s
  pc : s.pc = 50
  biasColumn : s.registers.i64 18 = some ((t%512 : Nat) : Int)
  rowWide : s.registers.i64 21 = some (((t/512*256)*2 : Nat) : Int)
  strides : ∀ j, j < 16 → s.registers.i64 (strideRegister j) = some (bStride t j)
  counter : s.registers.i32 27 = some 0
  accumulator : s.registers.scalar 69 = some (ops.literal 0 1)

theorem suffix_frame (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) : Frame t base (initializedSuffix ops t s) := by
  have h18 : Frame t base (columnSigned t s) := frame64 _ _ _ _ _ h (by decide)
  have h19 : Frame t base (columnWide t s) := frame64 _ _ _ _ _ h18 (by decide)
  have h26 : Frame t base (nextColumn t s) := frame32 _ _ _ _ _ h19 (by decide)
  have h20 : Frame t base (nextWide t s) := frame64 _ _ _ _ _ h26 (by decide)
  have h21 : Frame t base (matrixWide t s) := frame64 _ _ _ _ _ h20 (by decide)
  have h69 : Frame t base (zeroAccumulator ops t s) := frame_float _ _ _ _ _ h21
  exact frame32 _ _ _ _ _ h69 (by decide)

theorem suffix_pc (ops : Ops α) (t : Nat) (s : Machine α) (hpc : s.pc = 43) :
    (initializedSuffix ops t s).pc = 50 := by
  simp only [initializedSuffix, zeroAccumulator, matrixWide, nextWide, nextColumn,
    columnWide, columnSigned, setIndex32_pc, setFloat_pc, setIndex64_pc, hpc]

theorem suffix_i64 (ops : Ops α) (t r : Nat) (s : Machine α) :
    (initializedSuffix ops t s).registers.i64 r =
      if r = 21 then some (((t/512*256)*2 : Nat) : Int)
      else if r = 20 then some (((t%512+512)*2 : Nat) : Int)
      else if r = 19 then some ((t%512*2 : Nat) : Int)
      else if r = 18 then some ((t%512 : Nat) : Int)
      else s.registers.i64 r := by
  simp only [initializedSuffix, zeroAccumulator, matrixWide, nextWide, nextColumn,
    columnWide, columnSigned, setIndex32_i64, setFloat_i64, setIndex64_i64]

theorem suffix_counter (ops : Ops α) (t : Nat) (s : Machine α) :
    (initializedSuffix ops t s).registers.i32 27 = some 0 := by
  simp only [initializedSuffix, setIndex32_i32, if_pos rfl, ite_true]

theorem suffix_accumulator (ops : Ops α) (t : Nat) (s : Machine α) :
    (initializedSuffix ops t s).registers.scalar 69 = some (ops.literal 0 1) := by
  change (setFloat (matrixWide t s) 69 (ops.literal 0 1)).registers.scalar 69 = _
  simp only [LarkPtxDot.setFloat_scalar, if_pos rfl, ite_true]

theorem suffix_ready (ops : Ops α) (t : Nat) (base : State α) (s : Machine α)
    (h : Frame t base s) (hpc : s.pc = 43)
    (hstrides : ∀ j, 2 ≤ j → j < 16 → s.registers.i64 (19-j) = some (bStride t j)) :
    Ready ops t base (initializedSuffix ops t s) := by
  refine ⟨suffix_frame ops t base s h, suffix_pc ops t s hpc, ?_, ?_, ?_,
    suffix_counter ops t s, suffix_accumulator ops t s⟩
  · simp only [suffix_i64, if_neg (by decide : 18 ≠ 21),
      if_neg (by decide : 18 ≠ 20), if_neg (by decide : 18 ≠ 19), if_pos rfl, ite_true]
  · simp only [suffix_i64, if_pos rfl, ite_true]
  · intro j hj
    by_cases h0 : j = 0
    · subst j
      simp only [strideRegister, if_pos rfl, suffix_i64,
        if_neg (by decide : 19 ≠ 21), if_neg (by decide : 19 ≠ 20), bStride]
      rfl
    · by_cases h1 : j = 1
      · subst j
        simp only [strideRegister, if_neg (by decide : 1 ≠ 0), if_pos rfl,
          suffix_i64, if_neg (by decide : 20 ≠ 21), bStride]
        rfl
      · simp only [strideRegister, if_neg h0, if_neg h1, suffix_i64,
          if_neg (by omega : 19-j ≠ 21), if_neg (by omega : 19-j ≠ 20),
          if_neg (by omega : 19-j ≠ 19), if_neg (by omega : 19-j ≠ 18)]
        exact hstrides j (by omega) hj

theorem prefix43_strides (t j : Nat) (base : State α) (hj0 : 2 ≤ j) (hj : j < 16) :
    (addressPairs t base 14).registers.i64 (19-j) = some (bStride t j) := by
  rw [addressPairs_i64 t 14 (19-j) base (by decide), if_pos (by omega)]
  have he : 19-(19-j) = j := by omega
  rw [he]
  rfl

theorem prologue_ready (ops : Ops α) (t : Nat) (base : State α) (ht : t < 32768) :
    ∃ final, Steps ops layout geometry t program (start base) final ∧ Ready ops t base final := by
  have initialPrefix : ∃ mid, Steps ops layout geometry t program (start base) mid ∧
      Frame t base mid ∧ mid.pc = 43 ∧
      (∀ j, 2 ≤ j → j < 16 → mid.registers.i64 (19-j) = some (bStride t j)) := by
    refine ⟨addressPairs t base 14, addressPairs_execute ops t 14 base ht (by decide),
      addressPairs_frame t 14 base (by decide), ?_, ?_⟩
    · exact addressPairs_pc t 14 base
    · exact fun j h0 hj => prefix43_strides t j base h0 hj
  obtain ⟨mid, first, frame, pc43, strides⟩ := initialPrefix
  refine ⟨initializedSuffix ops t mid, ?_, suffix_ready ops t base mid frame pc43 strides⟩
  exact steps_trans _ _ _ _ _ _ _ _ first
    (suffix_execute ops t mid ht pc43 frame.active frame.column frame.row)


end LarkPtxLinear.Linear.Init

#print axioms LarkPtxLinear.Linear.Init.prefix_frame
#print axioms LarkPtxLinear.Linear.Init.frame32
#print axioms LarkPtxLinear.Linear.Init.frame64
#print axioms LarkPtxLinear.Linear.Init.frame_float
#print axioms LarkPtxLinear.Linear.Init.program_pair
#print axioms LarkPtxLinear.Linear.Init.address_pair_execute
#print axioms LarkPtxLinear.Linear.Init.addressPairs_pc
#print axioms LarkPtxLinear.Linear.Init.addressPairs_stopped
#print axioms LarkPtxLinear.Linear.Init.addressPairs_column
#print axioms LarkPtxLinear.Linear.Init.addressPairs_execute
#print axioms LarkPtxLinear.Linear.Init.addressPairs_row_offset
#print axioms LarkPtxLinear.Linear.Init.addressPairs_base
#print axioms LarkPtxLinear.Linear.Init.addressPairs_i64
#print axioms LarkPtxLinear.Linear.Init.addressPairs_frame

#print axioms LarkPtxLinear.Linear.Init.column_signed_execute
#print axioms LarkPtxLinear.Linear.Init.suffix_execute
#print axioms LarkPtxLinear.Linear.Init.suffix_frame
#print axioms LarkPtxLinear.Linear.Init.suffix_pc
#print axioms LarkPtxLinear.Linear.Init.suffix_i64
#print axioms LarkPtxLinear.Linear.Init.suffix_counter
#print axioms LarkPtxLinear.Linear.Init.suffix_accumulator
#print axioms LarkPtxLinear.Linear.Init.suffix_ready
#print axioms LarkPtxLinear.Linear.Init.prefix43_strides
#print axioms LarkPtxLinear.Linear.Init.prologue_ready
