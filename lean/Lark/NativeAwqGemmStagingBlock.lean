import Lark.NativeAwqGemmStagingFold

/-! The actual native staging visit converges at, and resumes, the middle
block barrier. The unchanged matrix/K-loop continuation remains explicit. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] aLoopState aRoundState aBodyState bChunksState bChunkState bChunkBody bLoopState bRoundState bBodyState stagingState stagingFold

def blockStaging (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile b : Nat) (s : State α) : State α :=
  stagingFold p ops input tile (blockThreads (geometry p) b) s

theorem block_staging_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t : Nat) (s : State α) (ht : t∈blockThreads (geometry p) b)
    (starts : ∀ u∈blockThreads (geometry p) b, StagingStart p tile u s) :
    StagingReady p tile t (blockStaging p ops input tile b s) :=
  staging_fold_ready p ops input tile t _ s (block_threads_nodup p b) ht starts

theorem block_staging_converged (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (s : State α) (starts : ∀ t∈blockThreads (geometry p) b, StagingStart p tile t s) :
    LarkMFMA.converged (program p) (blockThreads (geometry p) b) (blockStaging p ops input tile b s)=some .block := by
  have head : (blockThreads (geometry p) b).head?=some (b*64) := rfl
  have headMember : b*64∈blockThreads (geometry p) b :=
    List.mem_map.mpr ⟨0,by change 0∈List.range 64; decide,rfl⟩
  have headPC := (block_staging_ready p ops input tile b (b*64) s headMember starts).pc
  have allPC : (blockThreads (geometry p) b).all
      (fun t => (blockStaging p ops input tile b s).pc t==(blockStaging p ops input tile b s).pc (b*64))=true := by
    apply List.all_eq_true.mpr
    intro t ht
    rw [(block_staging_ready p ops input tile b t s ht starts).pc,headPC]
    simp
  simp only [LarkMFMA.converged,head,bind,pure,Option.bind,allPC,ite_true]
  simp only [LarkMFMA.parked,headPC,middle_barrier_site,blockBarrier,LarkMFMA.scalarCut]

theorem block_staging_warp_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b n : Nat) (s : State α) (hk : tile<p.k/32) (reads : Reads p input s)
    (starts : ∀ t∈blockThreads (geometry p) b, StagingStart p tile t s) :
    LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p)
      (blockThreads (geometry p) b) (n+1) s=some (blockStaging p ops input tile b s) := by
  have lanes : (blockThreads (geometry p) b).foldlM
      (fun state t => LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane state) s=
        some (blockStaging p ops input tile b s) :=
    staging_fold_run p ops input tile _ s hk (block_threads_nodup p b) reads starts
  have converged := block_staging_converged p ops input tile b s starts
  simp [LarkMFMA.runWarp,lanes,converged]

def afterMiddleBarrier (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile b : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) b) .block (blockStaging p ops input tile b s)

theorem block_staging_step (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b extra : Nat) (s : State α) (hk : tile<p.k/32) (reads : Reads p input s)
    (starts : ∀ t∈blockThreads (geometry p) b, StagingStart p tile t s) :
    LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b (extra+1) s=
      LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b extra
        (afterMiddleBarrier p ops input tile b s) := by
  have warp : LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p)
      (warpThreads (geometry p) b 0) (fuel p).warp s=some (blockStaging p ops input tile b s) := by
    rw [native_warp_threads]
    have positive : 0<(fuel p).warp := by change 0<tileN p/8+1; omega
    cases h : (fuel p).warp with
    | zero => omega
    | succ n => exact block_staging_warp_run p ops input tile b n s hk reads starts
  have waves : (List.range (((geometry p).block+(geometry p).warp-1)/(geometry p).warp)).foldlM
      (fun state w => LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p)
        (warpThreads (geometry p) b w) (fuel p).warp state) s=some (blockStaging p ops input tile b s) := by
    have count : ((geometry p).block+(geometry p).warp-1)/(geometry p).warp=1 := by
      change ((64+64-1)/64 : Nat)=1
      decide
    rw [count]
    change ([0] : List Nat).foldlM
      (fun (state : State α) (w : Nat) => LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p)
        (warpThreads (geometry p) b w) (fuel p).warp state) s=some (blockStaging p ops input tile b s)
    rw [LarkMFMA.foldlM_singleton]
    exact warp
  have converged := block_staging_converged p ops input tile b s starts
  simp [LarkMFMA.runBlock,waves,converged,afterMiddleBarrier]

theorem after_first_staging_start (p : Shape) (ops : Ops α) (b t : Nat) (s : State α)
    (ht : t∈blockThreads (geometry p) b) : StagingStart p 0 t (afterFirstBarrier p ops b s) :=
  ⟨after_first_pc p ops b t s ht,after_first_setup p ops b t s ht,after_first_k p ops b t s ht⟩

theorem initial_through_staging (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (b extra : Nat) (s : State α) (hb : b<(geometry p).grid) (reads : Reads p input s)
    (hp : ∀ t∈blockThreads (geometry p) b, s.pc t=0) :
    LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b (extra+2) s=
      LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b extra
        (afterMiddleBarrier p ops input 0 b (afterFirstBarrier p ops b s)) := by
  have kPositive : 0<p.k/32 := by have kp := p.k_pos; have aligned := p.k_aligned; omega
  rw [show extra+2=(extra+1)+1 by omega,initial_block_step p ops b (extra+1) s hb hp]
  exact block_staging_step p ops input 0 b extra (afterFirstBarrier p ops b s) kPositive
    (after_first_reads p ops b s input reads) (fun t ht => after_first_staging_start p ops b t s ht)

theorem after_middle_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t : Nat) (s : State α) (ht : t∈blockThreads (geometry p) b)
    (starts : ∀ u∈blockThreads (geometry p) b, StagingStart p tile u s) :
    (afterMiddleBarrier p ops input tile b s).pc t=middleBarrier p+1 ∧
      BOuterIndices p tile t (banks p) (afterMiddleBarrier p ops input tile b s) := by
  have ready := block_staging_ready p ops input tile b t s ht starts
  constructor
  · simp only [afterMiddleBarrier,resume,List.contains_iff_mem.mpr ht,ite_true,ready.pc]
  · exact b_outer_of_indices p tile t (banks p) (blockStaging p ops input tile b s) _ ready.outer rfl

theorem after_middle_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (s : State α) (reads : Reads p input s) : Reads p input (afterMiddleBarrier p ops input tile b s) :=
  staging_fold_reads p ops input tile _ s reads

theorem after_middle_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile b : Nat) (s : State α) :
    (afterMiddleBarrier p ops input tile b s).regs=s.regs ∧
      (afterMiddleBarrier p ops input tile b s).epochs=(resume (blockThreads (geometry p) b) .block s).epochs := by
  have frames := staging_fold_frames p ops input tile (blockThreads (geometry p) b) s
  constructor
  · exact frames.1
  · funext t
    simp only [afterMiddleBarrier,resume]
    rw [show (blockStaging p ops input tile b s).epochs=s.epochs from frames.2]

#print axioms block_staging_ready
#print axioms block_staging_converged
#print axioms block_staging_warp_run
#print axioms block_staging_step
#print axioms after_first_staging_start
#print axioms initial_through_staging
#print axioms after_middle_ready
#print axioms after_middle_reads
#print axioms after_middle_frames
end LarkNativeAwqGemm
