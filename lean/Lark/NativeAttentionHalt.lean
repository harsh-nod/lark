import Lark.NativeAttentionNextBlock

/-! The source's final key increment, false guard and native block halt. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def haltLane (t : Nat) (s : State α) : State α := advance (advance (setIndex s t 5 4 89) t 13) t 90

theorem halt_lane_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (hj : s.indices t 5 = some 3) (hp : s.pc t = 88) :
    runLane ops (layout p) (geometry p) program t (extra + 3) s =
      runLane ops (layout p) (geometry p) program t extra (haltLane t s) := by
  let s1 := setIndex s t 5 4 89
  let s2 := advance s1 t 13
  have h1 := execute_index_of ops (layout p) (geometry p) t 5 89 (.add (.ivar 5) (.const 1)) s 4
    (eval_counter (geometry p) t 5 3 s hj (by decide)) (by omega)
  have hg := LarkReduction.predicate_nlt_of (geometry p) t s2 (.ivar 5) (.const 4) 4 4
    (by simp [evalIndex, s2, s1, setIndex, advance]) (by rfl) (by omega)
  have h3 := execute_branch_of ops (layout p) (geometry p) t 14 90 _ s2 false hg (by simp [s2, advance])
  exact (source_step p ops t 88 (extra + 2) _ s s1 (by rfl) hp h1).trans
    ((source_step p ops t 89 (extra + 1) (.jump 13) s1 s2 (by rfl) (by simp [s1, setIndex, advance]) (by rfl)).trans
      (source_step p ops t 13 extra _ s2 (haltLane t s) (by rfl) (by simp [s2, advance]) h3))

theorem halt_lane_fields (t : Nat) (s : State α) :
    (haltLane t s).pc t = 90 ∧ (haltLane t s).indices t 5 = some 4 ∧
    (haltLane t s).memory = s.memory ∧ (haltLane t s).epochs = s.epochs ∧ (haltLane t s).trace = s.trace := by
  simp [haltLane, setIndex, advance]

theorem halt_lane_other (t u : Nat) (s : State α) (hne : u ≠ t) :
    (haltLane t s).pc u = s.pc u ∧ (haltLane t s).indices u = s.indices u := by
  simp [haltLane, setIndex, advance, hne]

theorem halt_parked_run (p : Shape) (ops : Ops α) (t remaining : Nat) (s : State α)
    (hp : s.pc t = 90) (hn : 0 < remaining) : runLane ops (layout p) (geometry p) program t remaining s = some s := by
  cases remaining with
  | zero => omega
  | succ k =>
      have hc : parked program s t = some .halt := by unfold parked; rw [hp]; rfl
      simp only [runLane, hc]

theorem halt_lane_run (p : Shape) (ops : Ops α) (t : Nat) (s : State α)
    (hj : s.indices t 5 = some 3) (hp : s.pc t = 88) :
    runLane ops (layout p) (geometry p) program t fuel.lane s = some (haltLane t s) :=
  (halt_lane_eq p ops t 999997 s hj hp).trans (halt_parked_run p ops t 999997 _ (halt_lane_fields t s).1 (by decide))

def haltFold (ts : List Nat) (s : State α) : State α := ts.foldl (fun s t => haltLane t s) s

theorem halt_fold_frames (ts : List Nat) (s : State α) :
    (haltFold ts s).memory = s.memory ∧ (haltFold ts s).epochs = s.epochs ∧ (haltFold ts s).trace = s.trace := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons t ts ih =>
      have hf := ih (haltLane t s)
      have he := halt_lane_fields t s
      exact ⟨hf.1.trans he.2.2.1, hf.2.1.trans he.2.2.2.1, hf.2.2.trans he.2.2.2.2⟩

theorem halt_fold_other (ts : List Nat) (u : Nat) (s : State α) (hu : u ∉ ts) :
    (haltFold ts s).pc u = s.pc u ∧ (haltFold ts s).indices u = s.indices u := by
  induction ts generalizing s with
  | nil => exact ⟨rfl, rfl⟩
  | cons t ts ih =>
      have hf := ih (haltLane t s) (by intro hm; exact hu (by simp [hm]))
      have he := halt_lane_other t u s (by intro he; exact hu (by simp [he]))
      exact ⟨hf.1.trans he.1, hf.2.trans he.2⟩

theorem halt_fold_member (ts : List Nat) (t : Nat) (s : State α) (hn : ts.Nodup) (ht : t ∈ ts) :
    (haltFold ts s).pc t = 90 ∧ (haltFold ts s).indices t 5 = some 4 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have hf := halt_fold_other ts u (haltLane u s) (List.nodup_cons.mp hn).1
        have he := halt_lane_fields u s
        exact ⟨hf.1.trans he.1, (congrArg (fun indices => indices 5) hf.2).trans he.2.1⟩
      · exact ih (haltLane u s) (List.nodup_cons.mp hn).2 hm

theorem halt_fold_run (p : Shape) (ops : Ops α) (ts : List Nat) (s : State α) (hn : ts.Nodup)
    (hp : ∀ t ∈ ts, s.pc t = 88 ∧ s.indices t 5 = some 3) :
    ts.foldlM (fun s t => runLane ops (layout p) (geometry p) program t fuel.lane s) s = some (haltFold ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      rw [List.foldlM_cons, halt_lane_run p ops t s (hp t (by simp)).2 (hp t (by simp)).1]
      simp only [bind, Option.some_bind]
      apply ih _ (List.nodup_cons.mp hn).2
      intro u hu
      have hf := halt_lane_other t u s (by intro he; subst u; exact (List.nodup_cons.mp hn).1 hu)
      exact ⟨hf.1.trans (hp u (by simp [hu])).1, (congrArg (fun indices => indices 5) hf.2).trans (hp u (by simp [hu])).2⟩

theorem converged_halt (ts : List Nat) (s : State α) (hne : ts ≠ []) (hp : ∀ t ∈ ts, s.pc t = 90) :
    converged program ts s = some .halt := by
  cases ts with
  | nil => contradiction
  | cons t ts =>
      have ht := hp t (by simp)
      have hall : (t :: ts).all (fun u => s.pc u == s.pc t) = true := by
        apply List.all_eq_true.mpr
        intro u hu
        simp [hp u hu, ht]
      have hall' : (t :: ts).all (fun u => s.pc u == 90) = true := by simpa [ht] using hall
      simp only [converged, List.head?_cons, bind, pure, Option.bind, hall, ↓reduceIte, parked, ht, hall']
      rfl

def haltBlock (p : Shape) (b : Nat) (s : State α) : State α := haltFold (blockThreads (geometry p) b) s

theorem halt_block_cut (p : Shape) (b : Nat) (s : State α) :
    converged program (blockThreads (geometry p) b) (haltBlock p b s) = some .halt := by
  apply converged_halt _ _ (block_nonempty p b)
  intro t ht
  exact (halt_fold_member _ t s (block_nodup p b) ht).1

theorem halt_block_warp (p : Shape) (ops : Ops α) (b : Nat) (s : State α)
    (hp : ∀ t ∈ blockThreads (geometry p) b, s.pc t = 88 ∧ s.indices t 5 = some 3) :
    runWarp ops (layout p) (geometry p) fuel program (warpThreads (geometry p) b 0) fuel.warp s = some (haltBlock p b s) := by
  have hf := halt_fold_run p ops (blockThreads (geometry p) b) s (block_nodup p b) hp
  rw [native_warp_threads]
  change runWarp ops (layout p) (geometry p) fuel program (blockThreads (geometry p) b) 1 s = _
  rw [runWarp, hf]
  simp only [bind, Option.some_bind]
  have hc := halt_block_cut p b s
  change converged program (blockThreads (geometry p) b) (haltFold (blockThreads (geometry p) b) s) = some .halt at hc
  rw [hc]
  rfl

theorem halt_block_run (p : Shape) (ops : Ops α) (b extra : Nat) (s : State α)
    (hp : ∀ t ∈ blockThreads (geometry p) b, s.pc t = 88 ∧ s.indices t 5 = some 3) :
    runBlock ops (layout p) (geometry p) fuel program b (extra + 1) s = some (haltBlock p b s) := by
  have hcount : ((geometry p).block + (geometry p).warp - 1) / (geometry p).warp = 1 := by change (32 + 64 - 1) / 64 = 1; decide
  rw [runBlock, hcount, show List.range 1 = [0] by decide, List.foldlM_cons, halt_block_warp p ops b s hp]
  simp only [List.foldlM_nil, bind, pure, Option.some_bind]
  rw [halt_block_cut p b s]
  rfl

#print axioms halt_lane_eq
#print axioms halt_lane_run
#print axioms halt_fold_frames
#print axioms halt_fold_member
#print axioms halt_block_run
end LarkNativeAttention
