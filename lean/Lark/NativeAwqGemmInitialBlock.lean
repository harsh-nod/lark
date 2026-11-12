import Lark.NativeAwqGemmInitial

/-! Actual first native warp/block visit, including all 64 lane prefixes and
the first block-barrier resumption. Remaining source execution is preserved
as a continuation of runBlock, not replaced by a separate computation. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

structure PrefixReady (p : Shape) (ops : Ops α) (t : Nat) (s : State α) : Prop where
  pc : s.pc t=firstBarrier p
  setup : SetupIndices p t s
  k : s.indices t 13=some 0
  accumulator : ∀ r, r<4*banks p → s.regs t r=some (ops.literal 0 1)

theorem prefix_ready (p : Shape) (ops : Ops α) (t : Nat) (s : State α) :
    PrefixReady p ops t (prefixState p ops t s) :=
  ⟨prefix_pc p ops t s,prefix_setup p ops t s,prefix_k p ops t s,
    fun r hr => prefix_accumulators p ops t r s hr⟩

theorem prefix_ready_of_thread (p : Shape) (ops : Ops α) (t : Nat) (s next : State α)
    (h : PrefixReady p ops t s) (hp : next.pc t=s.pc t)
    (hi : next.indices t=s.indices t) (hr : next.regs t=s.regs t) : PrefixReady p ops t next := by
  exact {
    pc := hp.trans h.pc
    setup := setup_of_thread_indices p t s next h.setup hi
    k := by rw [hi]; exact h.k
    accumulator := by intro r hb; rw [hr]; exact h.accumulator r hb }

def prefixFold (p : Shape) (ops : Ops α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => prefixState p ops t s) s

theorem prefix_fold_other (p : Shape) (ops : Ops α) (ts : List Nat) (u : Nat) (s : State α)
    (hu : u∉ts) :
    (prefixFold p ops ts s).pc u=s.pc u ∧ (prefixFold p ops ts s).indices u=s.indices u ∧
      (prefixFold p ops ts s).regs u=s.regs u := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons t ts ih =>
    have different : u≠t := by intro same; exact hu (List.mem_cons.mpr (Or.inl same))
    have tail : u∉ts := by intro member; exact hu (List.mem_cons_of_mem t member)
    have one := prefix_other p ops t u s different
    have rest := ih (prefixState p ops t s) tail
    exact ⟨rest.1.trans one.1,rest.2.1.trans one.2.1,rest.2.2.trans one.2.2⟩

theorem prefix_fold_frames (p : Shape) (ops : Ops α) (ts : List Nat) (s : State α) :
    (prefixFold p ops ts s).memory=s.memory ∧ (prefixFold p ops ts s).trace=s.trace ∧
      (prefixFold p ops ts s).epochs=s.epochs := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons t ts ih =>
    have one := prefix_frames p ops t s
    have rest := ih (prefixState p ops t s)
    exact ⟨rest.1.trans one.1,rest.2.1.trans one.2.1,rest.2.2.trans one.2.2⟩

theorem prefix_fold_ready (p : Shape) (ops : Ops α) (ts : List Nat) (u : Nat) (s : State α)
    (hd : ts.Nodup) (hu : u∈ts) : PrefixReady p ops u (prefixFold p ops ts s) := by
  induction ts generalizing s with
  | nil => simp at hu
  | cons t ts ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    rcases List.mem_cons.mp hu with same | member
    · subst u
      have outside := prefix_fold_other p ops ts t (prefixState p ops t s) disjoint
      exact prefix_ready_of_thread p ops t (prefixState p ops t s) _ (prefix_ready p ops t s)
        outside.1 outside.2.1 outside.2.2
    · exact ih (prefixState p ops t s) tail member

theorem prefix_fold_run (p : Shape) (ops : Ops α) (ts : List Nat) (s : State α)
    (hd : ts.Nodup) (ht : ∀ t∈ts, t<(geometry p).grid*64) (hp : ∀ t∈ts, s.pc t=0) :
    ts.foldlM (fun s t => LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane s) s=
      some (prefixFold p ops ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    have disjoint := (List.nodup_cons.mp hd).1
    have tail := (List.nodup_cons.mp hd).2
    have head : t∈t::ts := by simp
    rw [List.foldlM_cons,initial_prefix_run p ops t s (ht t head) (hp t head)]
    change ts.foldlM (fun s t => LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane s)
      (prefixState p ops t s)=some (prefixFold p ops ts (prefixState p ops t s))
    apply ih (prefixState p ops t s) tail
    · intro u hu
      exact ht u (List.mem_cons_of_mem t hu)
    · intro u hu
      have different : u≠t := by intro same; subst u; exact disjoint hu
      exact (prefix_other p ops t u s different).1.trans (hp u (List.mem_cons_of_mem t hu))

def blockPrefix (p : Shape) (ops : Ops α) (b : Nat) (s : State α) : State α :=
  prefixFold p ops (blockThreads (geometry p) b) s

theorem block_threads_nodup (p : Shape) (b : Nat) : (blockThreads (geometry p) b).Nodup := by
  unfold blockThreads
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (R := fun a b : Nat => a≠b) (by intro a b hab; omega) List.nodup_range

theorem block_thread_bound (p : Shape) (b t : Nat) (hb : b<(geometry p).grid)
    (ht : t∈blockThreads (geometry p) b) : t<(geometry p).grid*64 := by
  rcases List.mem_map.mp ht with ⟨lane,member,rfl⟩
  have hl := List.mem_range.mp member
  change lane<64 at hl
  change b*64+lane<(geometry p).grid*64
  omega

theorem native_warp_threads (p : Shape) (b : Nat) :
    warpThreads (geometry p) b 0=blockThreads (geometry p) b := by
  change ((List.range 64).filter (fun t => t/64==0)).map (b*64+·)=(List.range 64).map (b*64+·)
  have keep : (List.range 64).filter (fun t => t/64==0)=List.range 64 := by
    apply List.filter_eq_self.mpr
    intro t ht
    simp [Nat.div_eq_of_lt (List.mem_range.mp ht)]
  rw [keep]

theorem block_prefix_ready (p : Shape) (ops : Ops α) (b t : Nat) (s : State α)
    (ht : t∈blockThreads (geometry p) b) : PrefixReady p ops t (blockPrefix p ops b s) :=
  prefix_fold_ready p ops _ t s (block_threads_nodup p b) ht

theorem block_prefix_frames (p : Shape) (ops : Ops α) (b : Nat) (s : State α) :
    (blockPrefix p ops b s).memory=s.memory ∧ (blockPrefix p ops b s).trace=s.trace ∧
      (blockPrefix p ops b s).epochs=s.epochs := prefix_fold_frames p ops _ s

theorem block_prefix_converged (p : Shape) (ops : Ops α) (b : Nat) (s : State α) :
    LarkMFMA.converged (program p) (blockThreads (geometry p) b) (blockPrefix p ops b s)=some .block := by
  have head : (blockThreads (geometry p) b).head?=some (b*64) := rfl
  have headMember : b*64∈blockThreads (geometry p) b := by
    exact List.mem_map.mpr ⟨0,by change 0∈List.range 64; decide,rfl⟩
  have headPC := (block_prefix_ready p ops b (b*64) s headMember).pc
  have allPC : (blockThreads (geometry p) b).all
      (fun t => (blockPrefix p ops b s).pc t==(blockPrefix p ops b s).pc (b*64))=true := by
    apply List.all_eq_true.mpr
    intro t ht
    rw [(block_prefix_ready p ops b t s ht).pc,headPC]
    simp
  simp only [LarkMFMA.converged,head,bind,pure,Option.bind,allPC,ite_true]
  simp only [LarkMFMA.parked,headPC,first_barrier_site,blockBarrier,LarkMFMA.scalarCut]

theorem block_prefix_warp_run (p : Shape) (ops : Ops α) (b n : Nat) (s : State α)
    (hb : b<(geometry p).grid) (hp : ∀ t∈blockThreads (geometry p) b, s.pc t=0) :
    LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p)
      (blockThreads (geometry p) b) (n+1) s=some (blockPrefix p ops b s) := by
  have lanes : (blockThreads (geometry p) b).foldlM
      (fun s t => LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane s) s=
        some (blockPrefix p ops b s) :=
    prefix_fold_run p ops (blockThreads (geometry p) b) s (block_threads_nodup p b)
      (fun t ht => block_thread_bound p b t hb ht) hp
  have converged := block_prefix_converged p ops b s
  simp [LarkMFMA.runWarp,lanes,converged]

theorem initial_warp_run (p : Shape) (ops : Ops α) (b : Nat) (s : State α)
    (hb : b<(geometry p).grid) (hp : ∀ t∈blockThreads (geometry p) b, s.pc t=0) :
    LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p)
      (warpThreads (geometry p) b 0) (fuel p).warp s=some (blockPrefix p ops b s) := by
  have positive : 0<(fuel p).warp := by
    change 0<tileN p/8+1
    omega
  rw [native_warp_threads]
  cases h : (fuel p).warp with
  | zero => omega
  | succ n => exact block_prefix_warp_run p ops b n s hb hp

theorem initial_block_step (p : Shape) (ops : Ops α) (b extra : Nat) (s : State α)
    (hb : b<(geometry p).grid) (hp : ∀ t∈blockThreads (geometry p) b, s.pc t=0) :
    LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b (extra+1) s=
      LarkMFMA.runBlock ops (layout p) (geometry p) (fuel p) (program p) b extra
        (resume (blockThreads (geometry p) b) .block (blockPrefix p ops b s)) := by
  have waves : (List.range (((geometry p).block+(geometry p).warp-1)/(geometry p).warp)).foldlM
      (fun s w => LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p)
        (warpThreads (geometry p) b w) (fuel p).warp s) s=some (blockPrefix p ops b s) := by
    have count : ((geometry p).block+(geometry p).warp-1)/(geometry p).warp=1 := by
      change ((64+64-1)/64 : Nat)=1
      decide
    rw [count]
    change ([0] : List Nat).foldlM
      (fun (state : State α) (w : Nat) => LarkMFMA.runWarp ops (layout p) (geometry p) (fuel p) (program p)
        (warpThreads (geometry p) b w) (fuel p).warp state) s=some (blockPrefix p ops b s)
    rw [LarkMFMA.foldlM_singleton]
    exact initial_warp_run p ops b s hb hp
  have converged := block_prefix_converged p ops b s
  simp [LarkMFMA.runBlock,waves,converged]

#print axioms prefix_ready
#print axioms prefix_ready_of_thread
#print axioms prefix_fold_other
#print axioms prefix_fold_frames
#print axioms prefix_fold_ready
#print axioms prefix_fold_run
#print axioms block_threads_nodup
#print axioms block_thread_bound
#print axioms native_warp_threads
#print axioms block_prefix_ready
#print axioms block_prefix_frames
#print axioms block_prefix_converged
#print axioms block_prefix_warp_run
#print axioms initial_warp_run
#print axioms initial_block_step
end LarkNativeAwqGemm
