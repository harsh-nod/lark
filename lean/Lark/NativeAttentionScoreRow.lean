import Lark.NativeAttentionScoreTail

/-! Complete actual source score-row iterations, including maximum updates. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def scoreRowFuel (row : Nat) : Nat := 1798 + scoreTailFuel row
def scoreRow (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (maximum : α) (s : State α) : State α :=
  scoreTail ops t row (scoreValue ops input t qi kj row) maximum (scoreDot ops input t qi kj row s)

theorem score_row_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t qi kj row extra : Nat) (maximum : α) (s : State α) (hr : row < 32)
    (hq : QiReady ops input t qi s) (hk : Tiles ops input t kj s) (hn : NativeIndices t s)
    (hrow : s.indices t 9 = some (row : Int)) (hm : s.regs t 0 = some maximum) (hp : s.pc t = 30) :
    runLane ops (layout p) (geometry p) program t (extra + scoreRowFuel row) s =
      runLane ops (layout p) (geometry p) program t extra (scoreRow ops input t qi kj row maximum s) := by
  have hf := score_dot_fields ops input t qi kj row s
  have hrow1 := (score_dot_index ops input t qi kj row 9 s (by decide)).trans hrow
  have hm1 := (score_dot_max_reg ops input t qi kj row s).trans hm
  have hsteps : extra + scoreRowFuel row = (extra + scoreTailFuel row) + 1798 := by
    unfold scoreRowFuel
    omega
  rw [hsteps, score_dot_eq p ops input t qi kj row (extra + scoreTailFuel row) s hr hq hk hn hrow hp]
  exact score_tail_eq p ops t row extra _ maximum _ hr hrow1 hf.2.1 hm1 hf.1

theorem score_row_fields (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (maximum : α) (s : State α) :
    (scoreRow ops input t qi kj row maximum s).pc t = 30 ∧
    (scoreRow ops input t qi kj row maximum s).indices t 9 = some ((row + 1 : Nat) : Int) ∧
    (scoreRow ops input t qi kj row maximum s).regs t 0 =
      some (nextMaximum ops row (scoreValue ops input t qi kj row) maximum) ∧
    (scoreRow ops input t qi kj row maximum s).epochs = s.epochs := by
  have h := score_tail_fields ops t row (scoreValue ops input t qi kj row) maximum (scoreDot ops input t qi kj row s)
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1.trans (score_dot_fields ops input t qi kj row s).2.2⟩

theorem score_row_index (ops : Ops α) (input : Nat → Nat → α) (t qi kj row r : Nat)
    (maximum : α) (s : State α) (h9 : r ≠ 9) (h10 : r ≠ 10) :
    (scoreRow ops input t qi kj row maximum s).indices t r = s.indices t r :=
  (score_tail_index ops t row r _ maximum _ h9).trans (score_dot_index ops input t qi kj row r s h10)

theorem score_row_native (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (maximum : α) (s : State α) (hn : NativeIndices t s) : NativeIndices t (scoreRow ops input t qi kj row maximum s) :=
  score_tail_native ops t row _ maximum _ (score_dot_native ops input t qi kj row s hn)

theorem score_row_memory (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (maximum : α) (s : State α) (l : Location) :
    (scoreRow ops input t qi kj row maximum s).memory l = if l = sharedCell t 3 (scoreAddress t row)
      then some (scoreValue ops input t qi kj row) else s.memory l := by
  have h := score_tail_fields ops t row (scoreValue ops input t qi kj row) maximum (scoreDot ops input t qi kj row s)
  exact (congrFun h.2.2.2.2.1 l).trans (score_dot_memory ops input t qi kj row s l)

theorem score_row_qi (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (maximum : α) (s : State α) (hq : QiReady ops input t qi s) :
    QiReady ops input t qi (scoreRow ops input t qi kj row maximum s) := by
  intro col hc
  rw [score_row_memory, if_neg (by simp [sharedCell])]
  exact hq col hc

theorem score_row_tiles (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (maximum : α) (s : State α) (hk : Tiles ops input t kj s) :
    Tiles ops input t kj (scoreRow ops input t qi kj row maximum s) := by
  intro buffer hb r hr col hc
  have hb3 : buffer ≠ 3 := by omega
  rw [score_row_memory, if_neg (by simp [sharedCell, hb3])]
  exact hk buffer hb r hr col hc

theorem score_row_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (maximum : α) (s : State α) (hr : Reads p input s) : Reads p input (scoreRow ops input t qi kj row maximum s) := by
  intro b hb i hi
  rw [score_row_memory, if_neg (by simp [globalCell, sharedCell])]
  exact hr b hb i hi

theorem score_row_good (ops : Ops α) (input : Nat → Nat → α) (t qi kj row : Nat)
    (maximum : α) (s : State α) (hr : row < 32) (he : (s.epochs t).block % 2 = 1) (hg : TraceGood s) :
    TraceGood (scoreRow ops input t qi kj row maximum s) :=
  score_tail_good ops t row _ maximum _ (score_dot_good ops input t qi kj row s hr he hg)

#print axioms score_row_eq
#print axioms score_row_memory
#print axioms score_row_good
end LarkNativeAttention
