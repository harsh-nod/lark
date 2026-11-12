import Lark.NativeAwqGemmTailFold

/-! The real final warp visit converges at either the reuse block barrier or
the original halt. No K/output continuation is replaced with a dummy halt. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}
attribute [local irreducible] outputRound outputStored outputLoop outputLane tailLane tailFold

def blockTail (p : Shape) (ops : Ops α) (tile b : Nat) (values : Nat → Nat → α) (s : State α) : State α :=
  tailFold p ops tile values (blockThreads (geometry p) b) s

theorem block_tail_ready (p : Shape) (ops : Ops α) (tile b t : Nat) (values : Nat → Nat → α)
    (s : State α) (ht : t∈blockThreads (geometry p) b)
    (entries : ∀ u∈blockThreads (geometry p) b, TailEntry p tile u s) :
    TailReady p tile t (blockTail p ops tile b values s) :=
  tail_fold_ready p ops tile t values _ s (block_threads_nodup p b) ht entries

theorem block_tail_converged (p : Shape) (ops : Ops α) (tile b : Nat) (values : Nat → Nat → α)
    (s : State α) (entries : ∀ t∈blockThreads (geometry p) b, TailEntry p tile t s) :
    LarkMFMA.converged (program p) (blockThreads (geometry p) b) (blockTail p ops tile b values s)=
      some (if tile+1<p.k/32 then .block else .halt) := by
  have head : (blockThreads (geometry p) b).head?=some (b*64) := rfl
  have member : b*64∈blockThreads (geometry p) b :=
    List.mem_map.mpr ⟨0,by change 0∈List.range 64; decide,rfl⟩
  have headPC := (block_tail_ready p ops tile b (b*64) values s member entries).pc
  have allPC : (blockThreads (geometry p) b).all
      (fun t => (blockTail p ops tile b values s).pc t==(blockTail p ops tile b values s).pc (b*64))=true := by
    apply List.all_eq_true.mpr
    intro t ht
    rw [(block_tail_ready p ops tile b t values s ht entries).pc,headPC]
    simp
  simp only [LarkMFMA.converged,head,bind,pure,Option.bind,allPC,ite_true]
  by_cases more : tile+1<p.k/32
  · simp only [LarkMFMA.parked,headPC,if_pos more,first_barrier_site,blockBarrier,LarkMFMA.scalarCut]
  · simp only [LarkMFMA.parked,headPC,if_neg more,output_halt_site]

theorem block_tail_warp_run (p : Shape) (ops : Ops α) (tile b : Nat) (values : Nat → Nat → α)
    (s : State α) (hk : tile<p.k/32)
    (entries : ∀ t∈blockThreads (geometry p) b, TailEntry p tile t s)
    (hr : ∀ t∈blockThreads (geometry p) b, ∀ q, q<4*banks p → s.regs t q=some (values t q)) :
    LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p) (blockThreads (geometry p) b) 1 s=
      some (blockTail p ops tile b values s) := by
  have lanes := tail_fold_run p ops tile values (blockThreads (geometry p) b) s hk (block_threads_nodup p b) entries hr
  change (blockThreads (geometry p) b).foldlM _ s=some (blockTail p ops tile b values s) at lanes
  have converged := block_tail_converged p ops tile b values s entries
  by_cases more : tile+1<p.k/32
  · simp [LarkMFMA.runWarp,lanes,converged,more]
  · simp [LarkMFMA.runWarp,lanes,converged,more]

theorem block_tail_frames (p : Shape) (ops : Ops α) (tile b : Nat) (values : Nat → Nat → α) (s : State α) :
    (blockTail p ops tile b values s).regs=s.regs ∧ (blockTail p ops tile b values s).epochs=s.epochs :=
  tail_fold_frames p ops tile values _ s

theorem block_tail_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b : Nat) (values : Nat → Nat → α) (s : State α) (reads : Reads p input s) :
    Reads p input (blockTail p ops tile b values s) :=
  tail_fold_reads p ops input tile values _ s reads

def nextTile (p : Shape) (ops : Ops α) (tile b : Nat) (values : Nat → Nat → α) (s : State α) : State α :=
  resume (blockThreads (geometry p) b) .block (blockTail p ops tile b values s)

theorem next_tile_start (p : Shape) (ops : Ops α) (tile b t : Nat) (values : Nat → Nat → α) (s : State α)
    (more : tile+1<p.k/32) (ht : t∈blockThreads (geometry p) b)
    (entries : ∀ u∈blockThreads (geometry p) b, TailEntry p tile u s) :
    StagingStart p (tile+1) t (nextTile p ops tile b values s) := by
  have ready := block_tail_ready p ops tile b t values s ht entries
  refine ⟨?_,setup_of_indices p t (blockTail p ops tile b values s) _ ready.setup rfl,ready.k⟩
  simp only [nextTile,resume,List.contains_iff_mem.mpr ht,ite_true,ready.pc,if_pos more]

#print axioms block_tail_ready
#print axioms block_tail_converged
#print axioms block_tail_warp_run
#print axioms block_tail_frames
#print axioms block_tail_reads
#print axioms next_tile_start
end LarkNativeAwqGemm
