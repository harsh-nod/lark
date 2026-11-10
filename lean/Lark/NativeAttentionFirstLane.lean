import Lark.NativeAttentionFirstLoad

/-! A proper execution prefix, not a whole-launch attention certificate:
each lane executes source setup, all output zeros and its first K/V row copy,
then parks at the actual block barrier at PC 20 using the unchanged runLane. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def firstLane (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  firstLoad ops input t (zeroInit ops t (headerState t s))

theorem first_lane_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t extra : Nat) (s : State α) (ht : t < p.groups * 32)
    (hr : Reads p input s) (hp : s.pc t = 0) :
    runLane ops (layout p) (geometry p) program t (extra + 5405) s =
      runLane ops (layout p) (geometry p) program t extra (firstLane ops input t s) := by
  let s1 := headerState t s
  let s2 := zeroInit ops t s1
  have hh := header_fields t s
  have hn2 := zero_init_native ops t s1 hh.1
  have hr1 : Reads p input s1 := by
    intro b hb i hi
    rw [show s1.memory = s.memory from hh.2.2.1]
    exact hr b hb i hi
  have hr2 := zero_init_reads p ops input t s1 hr1
  have e1 := header_eq p ops t (extra + 5402) s ht hp
  have e2 := zero_init_eq p ops t (extra + 1284) s1 ht hh.1 hh.2.1
  have e3 := first_load_eq p ops input t extra s2 ht hr2 hn2 (zero_init_fields ops t s1).1
  exact e1.trans (e2.trans e3)

theorem first_lane_fields (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    (firstLane ops input t s).pc t = 20 ∧ (firstLane ops input t s).epochs = s.epochs := by
  have hh := header_fields t s
  have hz := zero_init_fields ops t (headerState t s)
  have hl := first_load_fields ops input t (zeroInit ops t (headerState t s))
  exact ⟨hl.1, hl.2.trans (hz.2.trans hh.2.2.2.1)⟩

theorem block_parked_run (p : Shape) (ops : Ops α) (t remaining : Nat) (s : State α)
    (hp : s.pc t = 20) (hn : 0 < remaining) :
    runLane ops (layout p) (geometry p) program t remaining s = some s := by
  cases remaining with
  | zero => omega
  | succ k =>
      have hc : parked program s t = some .block := by
        unfold parked
        rw [hp]
        rfl
      simp only [runLane, hc]

theorem first_lane_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (ht : t < p.groups * 32)
    (hr : Reads p input s) (hp : s.pc t = 0) :
    runLane ops (layout p) (geometry p) program t fuel.lane s = some (firstLane ops input t s) := by
  have he := first_lane_eq p ops input t 994595 s ht hr hp
  exact he.trans (block_parked_run p ops t 994595 _ (first_lane_fields ops input t s).1 (by decide))

theorem first_lane_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (hr : Reads p input s) : Reads p input (firstLane ops input t s) := by
  have hr1 : Reads p input (headerState t s) := by
    intro b hb i hi
    rw [(header_fields t s).2.2.1]
    exact hr b hb i hi
  exact first_load_reads p ops input t _ (zero_init_reads p ops input t _ hr1)

theorem first_lane_output (ops : Ops α) (input : Nat → Nat → α) (t tile col : Nat)
    (s : State α) (hi : tile < 4) (hc : col < 256) :
    (firstLane ops input t s).memory (globalCell 0 (globalAddress t tile col)) = some (zeroValue ops) :=
  (first_load_global ops input t 0 (globalAddress t tile col) _).trans
    (zero_init_value ops t tile col (headerState t s) hi hc)

theorem first_lane_tile (ops : Ops α) (input : Nat → Nat → α) (t b col : Nat)
    (s : State α) (hb : b = 1 ∨ b = 2) (hc : col < 256) :
    (firstLane ops input t s).memory (sharedCell t b (sharedAddress t col)) =
      some (ops.fromHalf (input (b + 1) (globalAddress t 0 col))) :=
  first_load_value ops input t b col _ hb hc

theorem first_lane_good (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (he : (s.epochs t).block % 2 = 0) (hg : TraceGood s) : TraceGood (firstLane ops input t s) := by
  have hh := header_fields t s
  have hg1 : TraceGood (headerState t s) := by
    intro a ha
    exact hg a (hh.2.2.2.2 ▸ ha)
  have he2 : ((zeroInit ops t (headerState t s)).epochs t).block % 2 = 0 := by
    rw [(zero_init_fields ops t (headerState t s)).2, hh.2.2.2.1]
    exact he
  exact first_load_good ops input t _ he2 (zero_init_good ops t _ hg1)

theorem first_lane_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (he : (s.epochs t).block % 2 = 0) (hg : TraceGood s) :
    raceFree (geometry p) (firstLane ops input t s).trace = true :=
  race_free p _ (first_lane_good ops input t s he hg)

#print axioms first_lane_eq
#print axioms first_lane_run
#print axioms first_lane_output
#print axioms first_lane_tile
#print axioms first_lane_reads
#print axioms first_lane_good
#print axioms first_lane_race_free
end LarkNativeAttention
