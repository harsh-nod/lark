import Lark.NativeAttentionScoreStore

/-! One actual score computation from the row guard through the shared store. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex setReg execute_index_of execute_pure_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def scoreDotEntry (ops : Ops α) (t : Nat) (s : State α) : State α :=
  setIndex (setReg (advance s t 31) t 1 (ops.literal 0 1) 32) t 10 0 33
def scoreDot (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat) (s : State α) : State α :=
  scoreDotFinish t row (scoreValue ops input t qi kj row)
    (dotColumns ops input t qi kj row 0 256 (ops.literal 0 1) (scoreDotEntry ops t s))

theorem score_entry_fields (ops : Ops α) (t : Nat) (s : State α) :
    (scoreDotEntry ops t s).pc t = 33 ∧ (scoreDotEntry ops t s).indices t 10 = some 0 ∧
    (scoreDotEntry ops t s).regs t 1 = some (ops.literal 0 1) := by
  simp [scoreDotEntry, setIndex, setReg, advance]

theorem score_entry_index (ops : Ops α) (t r : Nat) (s : State α) (hr : r ≠ 10) :
    (scoreDotEntry ops t s).indices t r = s.indices t r := by
  simp [scoreDotEntry, setIndex, setReg, advance, hr]

theorem score_entry_native (ops : Ops α) (t : Nat) (s : State α) (hn : NativeIndices t s) :
    NativeIndices t (scoreDotEntry ops t s) :=
  indices_set (setReg (advance s t 31) t 1 (ops.literal 0 1) 32) t 10 33 0 (by decide) hn

theorem score_dot_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row extra : Nat) (s : State α) (hr : row < 32)
    (hq : QiReady ops input t qi s) (hk : Tiles ops input t kj s) (hn : NativeIndices t s)
    (hrow : s.indices t 9 = some (row : Int)) (hp : s.pc t = 30) :
    runLane ops (layout p) (geometry p) program t (extra + 1798) s =
      runLane ops (layout p) (geometry p) program t extra (scoreDot ops input t qi kj row s) := by
  let s1 := advance s t 31
  let s2 := setReg s1 t 1 (ops.literal 0 1) 32
  let s3 := scoreDotEntry ops t s
  let s4 := dotColumns ops input t qi kj row 0 256 (ops.literal 0 1) s3
  have hg := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 9) (.const 32)
    (row : Int) 32 hrow (by rfl) (by omega)
  have h1 := execute_branch_of ops (layout p) (geometry p) t 31 48 _ s true hg (by omega)
  have h2 := execute_pure_of ops (layout p) (geometry p) t 1 32 (.lit 0 1) s1 (ops.literal 0 1)
    (by rfl) (by simp [s1, advance])
  have h3 := execute_index_of ops (layout p) (geometry p) t 10 33 (.const 0) s2 0 (by rfl)
    (by simp [s2, setReg, advance])
  have hf := score_entry_fields ops t s
  have hn3 := score_entry_native ops t s hn
  have hrow3 := (score_entry_index ops t 9 s (by decide)).trans hrow
  have hd := dot_columns_fields ops input t qi kj row 0 256 (ops.literal 0 1) s3
  have hv : s4.regs t 1 = some (rawDotValue ops input t qi kj row) :=
    dot_columns_value ops input t qi kj row 0 256 (ops.literal 0 1) s3 hf.2.2
  have hrow4 := (dot_columns_index ops input t qi kj row 0 256 9 (ops.literal 0 1) s3 (by decide)).trans hrow3
  have hn4 := dot_columns_native ops input t qi kj row 0 256 (ops.literal 0 1) s3 hn3
  have e1 := source_step p ops t 30 (extra + 1797) _ s s1 (by rfl) hp h1
  have e2 := source_step p ops t 31 (extra + 1796) _ s1 s2 (by rfl) (by simp [s1, advance]) h2
  have e3 := source_step p ops t 32 (extra + 1795) _ s2 s3 (by rfl) (by simp [s2, setReg, advance]) h3
  have e4 := dot_columns_eq p ops input t qi kj row 0 256 (extra + 2) (ops.literal 0 1) s3
    hr (by decide) hq hk hn3 hrow3 hf.2.1 hf.2.2 hf.1
  have e5 := score_scale_store_eq p ops t row extra (rawDotValue ops input t qi kj row) s4 hr hn4 hrow4 hv hd.1
  exact e1.trans (e2.trans (e3.trans (e4.trans e5)))

theorem score_dot_fields (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat) (s : State α) :
    (scoreDot ops input t qi kj row s).pc t = 42 ∧
    (scoreDot ops input t qi kj row s).regs t 1 = some (scoreValue ops input t qi kj row) ∧
    (scoreDot ops input t qi kj row s).epochs = s.epochs := by
  have h := score_dot_finish_fields t row (scoreValue ops input t qi kj row)
    (dotColumns ops input t qi kj row 0 256 (ops.literal 0 1) (scoreDotEntry ops t s))
  have hd := dot_columns_fields ops input t qi kj row 0 256 (ops.literal 0 1) (scoreDotEntry ops t s)
  exact ⟨h.1, h.2.2.1, h.2.2.2.trans hd.2.1⟩

theorem score_dot_index (ops : Ops α) (input : Nat → Nat → α) (t qi kj row r : Nat)
    (s : State α) (hr : r ≠ 10) : (scoreDot ops input t qi kj row s).indices t r = s.indices t r := by
  have hf := score_dot_finish_fields t row (scoreValue ops input t qi kj row)
    (dotColumns ops input t qi kj row 0 256 (ops.literal 0 1) (scoreDotEntry ops t s))
  exact (congrArg (fun indices => indices t r) hf.2.1).trans
    ((dot_columns_index ops input t qi kj row 0 256 r (ops.literal 0 1) (scoreDotEntry ops t s) hr).trans
      (score_entry_index ops t r s hr))

theorem score_dot_native (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (s : State α) (hn : NativeIndices t s) : NativeIndices t (scoreDot ops input t qi kj row s) :=
  ⟨(score_dot_index ops input t qi kj row 0 s (by decide)).trans hn.1,
   (score_dot_index ops input t qi kj row 1 s (by decide)).trans hn.2.1,
   (score_dot_index ops input t qi kj row 2 s (by decide)).trans hn.2.2⟩

theorem score_dot_max_reg (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat) (s : State α) :
    (scoreDot ops input t qi kj row s).regs t 0 = s.regs t 0 := by
  have h := score_dot_finish_reg t row 0 (scoreValue ops input t qi kj row)
    (dotColumns ops input t qi kj row 0 256 (ops.literal 0 1) (scoreDotEntry ops t s)) (by decide)
  have hd := dot_columns_reg ops input t qi kj row 0 256 0 (ops.literal 0 1) (scoreDotEntry ops t s)
    (by decide) (by decide) (by decide) (by decide)
  have he : (scoreDotEntry ops t s).regs t 0 = s.regs t 0 := by simp [scoreDotEntry, setReg, setIndex, advance]
  exact h.trans (hd.trans he)

theorem score_dot_memory (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (s : State α) (l : Location) :
    (scoreDot ops input t qi kj row s).memory l = if l = sharedCell t 3 (scoreAddress t row)
      then some (scoreValue ops input t qi kj row) else s.memory l := by
  have h := score_dot_finish_memory t row (scoreValue ops input t qi kj row)
    (dotColumns ops input t qi kj row 0 256 (ops.literal 0 1) (scoreDotEntry ops t s)) l
  have hm : (dotColumns ops input t qi kj row 0 256 (ops.literal 0 1) (scoreDotEntry ops t s)).memory = s.memory :=
    (dot_columns_fields ops input t qi kj row 0 256 (ops.literal 0 1) (scoreDotEntry ops t s)).2.2
  exact h.trans (congrArg (fun memory : Location → Option α =>
    if l = sharedCell t 3 (scoreAddress t row) then some (scoreValue ops input t qi kj row) else memory l) hm)

theorem score_dot_qi (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (s : State α) (hq : QiReady ops input t qi s) : QiReady ops input t qi (scoreDot ops input t qi kj row s) := by
  intro col hc
  rw [score_dot_memory, if_neg (by simp [sharedCell])]
  exact hq col hc

theorem score_dot_tiles (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (s : State α) (hk : Tiles ops input t kj s) : Tiles ops input t kj (scoreDot ops input t qi kj row s) := by
  intro buffer hb r hr col hc
  have hb3 : buffer ≠ 3 := by omega
  rw [score_dot_memory, if_neg (by simp [sharedCell, hb3])]
  exact hk buffer hb r hr col hc

theorem score_dot_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (s : State α) (hr : Reads p input s) : Reads p input (scoreDot ops input t qi kj row s) := by
  intro b hb i hi
  rw [score_dot_memory, if_neg (by simp [globalCell, sharedCell])]
  exact hr b hb i hi

theorem score_dot_good (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (s : State α) (hr : row < 32) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) :
    TraceGood (scoreDot ops input t qi kj row s) :=
  score_dot_finish_good t row _ _ hr
    (dot_columns_good ops input t qi kj row 0 256 (ops.literal 0 1) (scoreDotEntry ops t s) (by decide) he hg)

#print axioms score_dot_eq
#print axioms score_dot_memory
#print axioms score_dot_good
end LarkNativeAttention
