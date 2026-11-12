import Lark.NativeAwqGemmOutputLane

/-! Source-order execution of the K/output tail for all lanes. Each lane
preserves the other lanes' entry state and every accumulator snapshot. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] outputRound outputStored outputLoop outputLane tailLane

structure TailEntry (p : Shape) (tile t : Nat) (s : State α) : Prop where
  pc : s.pc t=kTailPC p
  setup : SetupIndices p t s
  k : s.indices t 13=some (tile : Int)

structure TailReady (p : Shape) (tile t : Nat) (s : State α) : Prop where
  pc : s.pc t=if tile+1<p.k/32 then firstBarrier p else haltPC p
  setup : SetupIndices p t s
  k : s.indices t 13=some ((tile+1 : Nat) : Int)

theorem tail_entry_of_thread (p : Shape) (tile t : Nat) (s next : State α)
    (h : TailEntry p tile t s) (hp : next.pc t=s.pc t) (hi : next.indices t=s.indices t) :
    TailEntry p tile t next :=
  ⟨hp.trans h.pc,setup_of_thread_indices p t s next h.setup hi,by rw [hi]; exact h.k⟩

theorem tail_ready_of_thread (p : Shape) (tile t : Nat) (s next : State α)
    (h : TailReady p tile t s) (hp : next.pc t=s.pc t) (hi : next.indices t=s.indices t) :
    TailReady p tile t next :=
  ⟨hp.trans h.pc,setup_of_thread_indices p t s next h.setup hi,by rw [hi]; exact h.k⟩

theorem tail_lane_ready (p : Shape) (ops : Ops α) (tile t : Nat) (values : Nat → α) (s : State α)
    (entry : TailEntry p tile t s) : TailReady p tile t (tailLane p ops tile t values s) :=
  ⟨tail_lane_pc p ops tile t values s,tail_lane_setup p ops tile t values s entry.setup,
    tail_lane_index p ops tile t values s⟩

def tailFold (p : Shape) (ops : Ops α) (tile : Nat) (values : Nat → Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun state t => tailLane p ops tile t (values t) state) s

theorem tail_fold_other (p : Shape) (ops : Ops α) (tile u : Nat) (values : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hu : u∉ts) :
    (tailFold p ops tile values ts s).pc u=s.pc u ∧ (tailFold p ops tile values ts s).indices u=s.indices u := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons t ts ih =>
    have different : u≠t := by intro same; exact hu (List.mem_cons.mpr (Or.inl same))
    have tail : u∉ts := by intro member; exact hu (List.mem_cons_of_mem t member)
    have rest := ih (tailLane p ops tile t (values t) s) tail
    exact ⟨rest.1.trans (tail_lane_other_pc p ops tile t u (values t) s different),
      rest.2.trans (tail_lane_other_indices p ops tile t u (values t) s different)⟩

theorem tail_fold_frames (p : Shape) (ops : Ops α) (tile : Nat) (values : Nat → Nat → α)
    (ts : List Nat) (s : State α) :
    (tailFold p ops tile values ts s).regs=s.regs ∧ (tailFold p ops tile values ts s).epochs=s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons t ts ih =>
    have one := tail_lane_frames p ops tile t (values t) s
    have rest := ih (tailLane p ops tile t (values t) s)
    exact ⟨rest.1.trans one.2.1,rest.2.trans one.2.2⟩

theorem tail_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile : Nat) (values : Nat → Nat → α) (ts : List Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (tailFold p ops tile values ts s) := by
  induction ts generalizing s with
  | nil => exact reads
  | cons t ts ih => exact ih _ (tail_lane_reads p ops input tile t (values t) s reads)

theorem tail_fold_ready (p : Shape) (ops : Ops α) (tile u : Nat) (values : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hd : ts.Nodup) (hu : u∈ts)
    (entries : ∀ t∈ts, TailEntry p tile t s) : TailReady p tile u (tailFold p ops tile values ts s) := by
  induction ts generalizing s with
  | nil => simp at hu
  | cons t ts ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    rcases List.mem_cons.mp hu with same | member
    · subst u
      have frame := tail_fold_other p ops tile t values ts (tailLane p ops tile t (values t) s) disjoint
      exact tail_ready_of_thread p tile t (tailLane p ops tile t (values t) s) _
        (tail_lane_ready p ops tile t (values t) s (entries t (by simp))) frame.1 frame.2
    · apply ih (tailLane p ops tile t (values t) s) tail member
      intro v hv
      have different : v≠t := by intro same; subst v; exact disjoint hv
      exact tail_entry_of_thread p tile v s _ (entries v (List.mem_cons_of_mem t hv))
        (tail_lane_other_pc p ops tile t v (values t) s different)
        (tail_lane_other_indices p ops tile t v (values t) s different)

theorem tail_fold_run (p : Shape) (ops : Ops α) (tile : Nat) (values : Nat → Nat → α)
    (ts : List Nat) (s : State α) (hk : tile<p.k/32) (hd : ts.Nodup)
    (entries : ∀ t∈ts, TailEntry p tile t s)
    (hr : ∀ t∈ts, ∀ q, q<4*banks p → s.regs t q=some (values t q)) :
    ts.foldlM (fun state t => LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane state) s=
      some (tailFold p ops tile values ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    have entry := entries t (by simp)
    rw [List.foldlM_cons,tail_lane_run p ops tile t (values t) s hk entry.k entry.pc entry.setup (hr t (by simp))]
    change ts.foldlM (fun state t => LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane state)
      (tailLane p ops tile t (values t) s)=some (tailFold p ops tile values ts (tailLane p ops tile t (values t) s))
    apply ih (tailLane p ops tile t (values t) s) tail
    · intro u hu
      have different : u≠t := by intro same; subst u; exact disjoint hu
      exact tail_entry_of_thread p tile u s _ (entries u (List.mem_cons_of_mem t hu))
        (tail_lane_other_pc p ops tile t u (values t) s different)
        (tail_lane_other_indices p ops tile t u (values t) s different)
    · intro u hu q hq
      rw [(tail_lane_frames p ops tile t (values t) s).2.1]
      exact hr u (List.mem_cons_of_mem t hu) q hq

#print axioms tail_entry_of_thread
#print axioms tail_ready_of_thread
#print axioms tail_lane_ready
#print axioms tail_fold_other
#print axioms tail_fold_frames
#print axioms tail_fold_reads
#print axioms tail_fold_ready
#print axioms tail_fold_run
end LarkNativeAwqGemm
