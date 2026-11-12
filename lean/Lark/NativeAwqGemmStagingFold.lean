import Lark.NativeAwqGemmStagingFrame

/-! Source-order staging through every scheduled lane. Each monadic lane
execution is identified with its combined A-then-B state transformer. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] aLoopState aRoundState aBodyState bChunksState bChunkState bChunkBody bLoopState bRoundState bBodyState

structure StagingStart (p : Shape) (tile t : Nat) (s : State α) : Prop where
  pc : s.pc t=firstBarrier p+1
  setup : SetupIndices p t s
  k : s.indices t 13=some (tile : Int)

structure StagingReady (p : Shape) (tile t : Nat) (s : State α) : Prop where
  pc : s.pc t=middleBarrier p
  outer : BOuterIndices p tile t (banks p) s

theorem staging_start_of_thread (p : Shape) (tile t : Nat) (s next : State α)
    (h : StagingStart p tile t s) (hp : next.pc t=s.pc t) (hi : next.indices t=s.indices t) :
    StagingStart p tile t next :=
  ⟨hp.trans h.pc,setup_of_thread_indices p t s next h.setup hi,by rw [hi]; exact h.k⟩

theorem staging_ready_of_thread (p : Shape) (tile t : Nat) (s next : State α)
    (h : StagingReady p tile t s) (hp : next.pc t=s.pc t) (hi : next.indices t=s.indices t) :
    StagingReady p tile t next := by
  exact {pc := hp.trans h.pc
         outer := {setup := setup_of_thread_indices p t s next h.outer.setup hi
                   k := by rw [hi]; exact h.outer.k
                   chunkIndex := by rw [hi]; exact h.outer.chunkIndex}}

theorem staging_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t : Nat) (s : State α)
    (h : StagingStart p tile t s) : StagingReady p tile t (stagingState p ops input tile t s) :=
  ⟨staging_pc p ops input tile t s,staging_indices p ops input tile t s h.setup h.k⟩

def stagingFold (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile : Nat) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun state t => stagingState p ops input tile t state) s

theorem staging_fold_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile u : Nat) (ts : List Nat) (s : State α) (hu : u∉ts) :
    (stagingFold p ops input tile ts s).pc u=s.pc u ∧ (stagingFold p ops input tile ts s).indices u=s.indices u := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons t ts ih =>
    have different : u≠t := by intro same; exact hu (List.mem_cons.mpr (Or.inl same))
    have tail : u∉ts := by intro member; exact hu (List.mem_cons_of_mem t member)
    have one := staging_other p ops input tile t u s different
    have rest := ih (stagingState p ops input tile t s) tail
    exact ⟨rest.1.trans one.1,rest.2.trans one.2⟩

theorem staging_fold_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile : Nat) (ts : List Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (stagingFold p ops input tile ts s) := by
  induction ts generalizing s with
  | nil => exact reads
  | cons t ts ih => exact ih (stagingState p ops input tile t s) (staging_reads p ops input tile t s reads)

theorem staging_fold_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile : Nat) (ts : List Nat) (s : State α) :
    (stagingFold p ops input tile ts s).regs=s.regs ∧ (stagingFold p ops input tile ts s).epochs=s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl⟩
  | cons t ts ih =>
    have one := staging_frames p ops input tile t s
    have rest := ih (stagingState p ops input tile t s)
    exact ⟨rest.1.trans one.1,rest.2.trans one.2⟩

theorem staging_fold_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile u : Nat) (ts : List Nat) (s : State α) (hd : ts.Nodup) (hu : u∈ts)
    (starts : ∀ t∈ts, StagingStart p tile t s) : StagingReady p tile u (stagingFold p ops input tile ts s) := by
  induction ts generalizing s with
  | nil => simp at hu
  | cons t ts ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    rcases List.mem_cons.mp hu with same | member
    · subst u
      have outside := staging_fold_other p ops input tile t ts (stagingState p ops input tile t s) disjoint
      exact staging_ready_of_thread p tile t (stagingState p ops input tile t s) _
        (staging_ready p ops input tile t s (starts t (by simp))) outside.1 outside.2
    · apply ih (stagingState p ops input tile t s) tail member
      intro v hv
      have different : v≠t := by intro same; subst v; exact disjoint hv
      have frame := staging_other p ops input tile t v s different
      exact staging_start_of_thread p tile v s _ (starts v (List.mem_cons_of_mem t hv)) frame.1 frame.2

theorem staging_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile : Nat) (ts : List Nat) (s : State α) (hk : tile<p.k/32) (hd : ts.Nodup)
    (reads : Reads p input s) (starts : ∀ t∈ts, StagingStart p tile t s) :
    ts.foldlM (fun state t => LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane state) s=
      some (stagingFold p ops input tile ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    have head := starts t (by simp)
    rw [List.foldlM_cons,staging_run p ops input tile t s hk head.setup head.k reads head.pc]
    change ts.foldlM (fun state t => LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane state)
      (stagingState p ops input tile t s)=some (stagingFold p ops input tile ts (stagingState p ops input tile t s))
    apply ih (stagingState p ops input tile t s) tail (staging_reads p ops input tile t s reads)
    intro u hu
    have different : u≠t := by intro same; subst u; exact disjoint hu
    have frame := staging_other p ops input tile t u s different
    exact staging_start_of_thread p tile u s _ (starts u (List.mem_cons_of_mem t hu)) frame.1 frame.2

#print axioms staging_start_of_thread
#print axioms staging_ready_of_thread
#print axioms staging_ready
#print axioms staging_fold_other
#print axioms staging_fold_reads
#print axioms staging_fold_frames
#print axioms staging_fold_ready
#print axioms staging_fold_run
end LarkNativeAwqGemm
