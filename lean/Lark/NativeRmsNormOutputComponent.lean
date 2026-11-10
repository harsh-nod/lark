import Lark.NativeRmsNormOutputStore

/-! Actual eight-instruction output component cycle. The multiplication order
and final half conversion are those of the fixed frontend program.
-/
namespace LarkNativeRmsNorm
open LarkNonlinear
open LarkReduction (setReg setIndex int32_cast execute_pure_of execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def outputWeighted (ops : Ops α) (input : Nat → Nat → α) (row vector component : Nat) (inverse : α) : α :=
  ops.mul (ops.mul (ops.fromHalf (input 1 (scalarAddress row vector component))) inverse)
    (ops.fromHalf (input 2 (vector * 8 + component)))

def outputComponent (ops : Ops α) (input : Nat → Nat → α) (row vector component t : Nat)
    (inverse : α) (s : State α) : State α :=
  let x := ops.fromHalf (input 1 (scalarAddress row vector component))
  let w := ops.fromHalf (input 2 (vector * 8 + component))
  let s := advance s t 61
  let s := setReg (record s t (globalCell 1 (scalarAddress row vector component)) false) t 5 x 62
  let s := setReg (record s t (globalCell 2 (vector * 8 + component)) false) t 6 w 63
  let s := setReg s t 7 (ops.mul x inverse) 64
  let s := setReg s t 8 (outputWeighted ops input row vector component inverse) 65
  let s := outputWritten t (scalarAddress row vector component)
    (ops.toHalf (outputWeighted ops input row vector component inverse)) s
  let s := setIndex s t 8 ((component + 1 : Nat) : Int) 67
  advance s t 60

def outputInstr : Nat → LarkNonlinear.Instr
  | 0 => .branch (.lt (.ivar 8) (.const 8)) 68
  | 1 => .assign 5 (.un .fromHalf (.load .global 1 (rowIndex 7 8)))
  | 2 => .assign 6 (.un .fromHalf (.load .global 2 (columnIndex 7 8)))
  | 3 => .assign 7 (.bin .mul (.reg 5) (.reg 4))
  | 4 => .assign 8 (.bin .mul (.reg 7) (.reg 6))
  | 5 => .store .global 0 (rowIndex 7 8) (.un .toHalf (.reg 8))
  | 6 => .index 8 (.add (.ivar 8) (.const 1))
  | _ => .jump 60

theorem output_codes (n : Nat) (hn : n < 8) : program[60 + n]? = some (.scalar (outputInstr n)) := by
  have all : ∀ n : Fin 8, program[60 + n.val]? = some (.scalar (outputInstr n.val)) := by decide
  exact all ⟨n, hn⟩

theorem output_scalar_step (p : Shape) (ops : Ops α) (t pc extra : Nat) (i : LarkNonlinear.Instr)
    (s next : State α) (hc : program[pc]? = some (.scalar i)) (hp : s.pc t = pc)
    (he : execute ops (layout p) (geometry p) t i s = some next) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 1) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra next :=
  scalar_step ops _ _ _ _ _ _ _ _
    (by
      unfold LarkCollective.parked
      rewrite [hp, hc]
      cases i <;> try rfl
      all_goals simp [execute] at he)
    (by simpa only [hp] using hc) he

theorem output_component_cycle (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t extra : Nat) (inverse : α) (s : State α)
    (reads : Reads p input s) (hr : row < p.rows) (hv : vector < 2048) (hc : component < 8)
    (hi0 : s.indices t 0 = some (row : Int)) (hi7 : s.indices t 7 = some (vector : Int))
    (hi8 : s.indices t 8 = some (component : Int)) (hx : s.regs t 4 = some inverse) (hp : s.pc t = 60) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 8) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra
        (outputComponent ops input row vector component t inverse s) := by
  let x := ops.fromHalf (input 1 (scalarAddress row vector component))
  let w := ops.fromHalf (input 2 (vector * 8 + component))
  let v := outputWeighted ops input row vector component inverse
  let s1 := advance s t 61
  let s2 := setReg (record s1 t (globalCell 1 (scalarAddress row vector component)) false) t 5 x 62
  let s3 := setReg (record s2 t (globalCell 2 (vector * 8 + component)) false) t 6 w 63
  let s4 := setReg s3 t 7 (ops.mul x inverse) 64
  let s5 := setReg s4 t 8 v 65
  let s6 := outputWritten t (scalarAddress row vector component) (ops.toHalf v) s5
  let s7 := setIndex s6 t 8 ((component + 1 : Nat) : Int) 67
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 8) (.const 8)
    (component : Int) 8 hi8 (by rfl) (by omega)
  have h1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 8) (.const 8)) 68) s = some s1 := by
    simp only [execute, hg, hp, bind, pure, Option.bind]
    rfl
  have he2 := load_input p ops input t 7 8 row vector component s1 reads hi0 hi7 hi8 hr hv hc
  have h2 : execute ops (layout p) (geometry p) t
      (.assign 5 (.un .fromHalf (.load .global 1 (rowIndex 7 8)))) s1 = some s2 := by
    simp only [execute, he2, bind, pure, Option.bind]
    rewrite [show s1.pc t + 1 = 62 by simp [s1, advance]]
    rfl
  have he3 := load_weight p ops input t 7 8 vector component s2 reads hi7 hi8 hv hc
  have h3 : execute ops (layout p) (geometry p) t
      (.assign 6 (.un .fromHalf (.load .global 2 (columnIndex 7 8)))) s2 = some s3 := by
    simp only [execute, he3, bind, pure, Option.bind]
    rewrite [show s2.pc t + 1 = 63 by simp [s2, setReg, advance]]
    rfl
  have h4 := execute_pure_of ops (layout p) (geometry p) t 7 64
    (.bin .mul (.reg 5) (.reg 4)) s3 (ops.mul x inverse)
    (by simp [evalExpr, applyBinary, s3, s2, s1, setReg, record, advance, hx])
    (by simp [s3, setReg, advance])
  change execute _ _ _ _ _ s3 = some s4 at h4
  have h5 := execute_pure_of ops (layout p) (geometry p) t 8 65
    (.bin .mul (.reg 7) (.reg 6)) s4 v
    (by simp [evalExpr, applyBinary, s4, s3, setReg, record, advance, v, outputWeighted, x, w])
    (by simp [s4, setReg, advance])
  change execute _ _ _ _ _ s4 = some s5 at h5
  have h6 := output_store_eq p ops t row vector component v s5 hr hv hc hi0 hi7 hi8
    (by simp [s5, setReg, advance]) (by simp [s5, setReg, advance])
  change execute _ _ _ _ _ s5 = some s6 at h6
  have he7 := LarkReduction.eval_add_of (geometry p) t s6 (.ivar 8) (.const 1)
    (component : Int) 1 ((component + 1 : Nat) : Int) hi8 (by rfl)
    ((congrArg int32 (Int.natCast_add component 1).symm).trans (int32_cast _ (by omega)))
  have h7 := execute_index_of ops (layout p) (geometry p) t 8 67 (.add (.ivar 8) (.const 1)) s6
    ((component + 1 : Nat) : Int) he7 (by simp [s6, outputWritten, advance])
  change execute _ _ _ _ _ s6 = some s7 at h7
  have h8 : execute ops (layout p) (geometry p) t (.jump 60) s7 =
      some (outputComponent ops input row vector component t inverse s) := rfl
  rewrite [output_scalar_step p ops t 60 _ _ s s1 (output_codes 0 (by decide)) hp h1]
  rewrite [output_scalar_step p ops t 61 _ _ s1 s2 (output_codes 1 (by decide)) (by simp [s1, advance]) h2]
  rewrite [output_scalar_step p ops t 62 _ _ s2 s3 (output_codes 2 (by decide)) (by simp [s2, setReg, advance]) h3]
  rewrite [output_scalar_step p ops t 63 _ _ s3 s4 (output_codes 3 (by decide)) (by simp [s3, setReg, advance]) h4]
  rewrite [output_scalar_step p ops t 64 _ _ s4 s5 (output_codes 4 (by decide)) (by simp [s4, setReg, advance]) h5]
  rewrite [output_scalar_step p ops t 65 _ _ s5 s6 (output_codes 5 (by decide)) (by simp [s5, setReg, advance]) h6]
  rewrite [output_scalar_step p ops t 66 _ _ s6 s7 (output_codes 6 (by decide)) (by simp [s6, outputWritten, advance]) h7]
  rewrite [output_scalar_step p ops t 67 _ _ s7 _ (output_codes 7 (by decide)) (by simp [s7, setIndex, advance]) h8]
  rfl

theorem output_component_memory (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t : Nat) (inverse : α) (s : State α) (l : Location) :
    (outputComponent ops input row vector component t inverse s).memory l =
      if l = globalCell 0 (scalarAddress row vector component)
      then some (ops.toHalf (outputWeighted ops input row vector component inverse)) else s.memory l := rfl

theorem output_component_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t : Nat) (inverse : α) (s : State α) (reads : Reads p input s) :
    Reads p input (outputComponent ops input row vector component t inverse s) := by
  constructor
  · intro i hi
    rewrite [output_component_memory]
    simp only [show globalCell 1 i ≠ globalCell 0 (scalarAddress row vector component) by simp [globalCell], ↓reduceIte]
    exact reads.1 i hi
  · intro i hi
    rewrite [output_component_memory]
    simp only [show globalCell 2 i ≠ globalCell 0 (scalarAddress row vector component) by simp [globalCell], ↓reduceIte]
    exact reads.2 i hi

theorem output_component_fields (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t : Nat) (inverse : α) (s : State α) :
    (outputComponent ops input row vector component t inverse s).pc t = 60 ∧
    (outputComponent ops input row vector component t inverse s).indices t 0 = s.indices t 0 ∧
    (outputComponent ops input row vector component t inverse s).indices t 7 = s.indices t 7 ∧
    (outputComponent ops input row vector component t inverse s).indices t 8 = some ((component + 1 : Nat) : Int) ∧
    (outputComponent ops input row vector component t inverse s).regs t 4 = s.regs t 4 ∧
    (outputComponent ops input row vector component t inverse s).epochs = s.epochs := by
  simp [outputComponent, outputWritten, advance, setReg, setIndex, record]

theorem output_component_other (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t u : Nat) (inverse : α) (s : State α) (hu : u ≠ t) :
    (outputComponent ops input row vector component t inverse s).pc u = s.pc u ∧
    (outputComponent ops input row vector component t inverse s).indices u = s.indices u ∧
    (outputComponent ops input row vector component t inverse s).regs u = s.regs u := by
  simp [outputComponent, outputWritten, advance, setReg, setIndex, record, hu]

theorem output_component_trace (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t : Nat) (inverse : α) (s : State α) :
    (outputComponent ops input row vector component t inverse s).trace =
      ⟨t, globalCell 0 (scalarAddress row vector component), true, s.epochs t⟩ ::
      ⟨t, globalCell 2 (vector * 8 + component), false, s.epochs t⟩ ::
      ⟨t, globalCell 1 (scalarAddress row vector component), false, s.epochs t⟩ :: s.trace := rfl

theorem output_component_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row vector component t : Nat) (inverse : α) (s : State α)
    (hv : vector < 2048) (hc : component < 8) (ht : t = row * 1024 + vector % 1024)
    (good : ∀ a ∈ s.trace, LarkReductionFootprint.Good (traversal p) 0 a) :
    ∀ a ∈ (outputComponent ops input row vector component t inverse s).trace,
      LarkReductionFootprint.Good (traversal p) 0 a := by
  intro a ha
  rewrite [output_component_trace] at ha
  rcases List.mem_cons.mp ha with he | ha
  · subst a
    exact .output rfl rfl rfl rfl (ht.trans (output_writer p row vector component hv hc).symm)
  · rcases List.mem_cons.mp ha with he | ha
    · subst a
      exact input_access_good p s t 2 _ (by decide)
    · rcases List.mem_cons.mp ha with he | ha
      · subst a
        exact input_access_good p s t 1 _ (by decide)
      · exact good a ha

#print axioms output_component_cycle
#print axioms output_component_fields
#print axioms output_component_reads
#print axioms output_component_good
end LarkNativeRmsNorm
