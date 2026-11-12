import Lark.NativeAwqGemmInitRegisters

/-! Actual initial source execution through the first block barrier.
The existing lane512 budget suffices for both 31/47-instruction paths.
No memory read, write or trace event is introduced before that barrier. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def preparedState (p : Shape) (ops : Ops α) (t : Nat) (s : State α) : State α :=
  zeroed ops t (4*banks p) (indicesState p t s)

def kStartedState (p : Shape) (ops : Ops α) (t : Nat) (s : State α) : State α :=
  setIndex (preparedState p ops t s) t 13 0 (whilePC p)

def prefixState (p : Shape) (ops : Ops α) (t : Nat) (s : State α) : State α :=
  advance (kStartedState p ops t s) t (firstBarrier p)

theorem prepared_pc (p : Shape) (ops : Ops α) (t : Nat) (s : State α) :
    (preparedState p ops t s).pc t=13+4*banks p :=
  zeroed_pc ops t (4*banks p) _ (indices_pc p t s)

theorem k_started_pc (p : Shape) (ops : Ops α) (t : Nat) (s : State α) :
    (kStartedState p ops t s).pc t=whilePC p := by simp [kStartedState,setIndex,advance]

theorem initial_prefix_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (ht : t<(geometry p).grid*64) (hp : s.pc t=0) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+(15+4*banks p)) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (prefixState p ops t s) := by
  let prepared := preparedState p ops t s
  let started := kStartedState p ops t s
  have pc : prepared.pc t=13+4*banks p := prepared_pc p ops t s
  have start := execute_index_of ops p t 13 (whilePC p) (c 0) prepared 0
    (eval_nat_const (geometry p) t 0 prepared (by decide)) (by unfold whilePC; omega)
  have kIndex : evalIndex (geometry p) t started (v 13)=some 0 := by
    simp [started,kStartedState,v,evalIndex,setIndex,advance]
  have kBound : p.k/32<2147483648 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (scalar_parameter_bounds p).2.1
  have kPositive : (0 : Int)<((p.k/32 : Nat) : Int) := by
    have h := k_minimum p
    omega
  have predicate := eval_int_lt_true (geometry p) t started (v 13) (c (p.k/32)) 0 ((p.k/32 : Nat) : Int)
    kIndex (eval_nat_const (geometry p) t (p.k/32) started kBound) kPositive
  have branchStep : execute ops (layout p) (geometry p) t
      (.branch (.lt (v 13) (c (p.k/32))) (outputPC p)) started=some (prefixState p ops t s) := by
    have step := execute_branch_true ops p t (outputPC p) (.lt (v 13) (c (p.k/32))) started predicate
    rw [k_started_pc p ops t s] at step
    simpa only [show whilePC p+1=firstBarrier p by unfold whilePC firstBarrier; omega] using step
  rewrite [show extra+(15+4*banks p)=(extra+2+4*banks p)+13 by omega,
    initial_indices_run p ops t (extra+2+4*banks p) s ht hp]
  rewrite [zeroed_run p ops t (4*banks p) (extra+2) (indicesState p t s) (by omega) (indices_pc p t s)]
  change LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+2) prepared=
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (prefixState p ops t s)
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p ops t (13+4*banks p) (extra+1) _ prepared started (k_counter_site p) pc start]
  exact scalar_step p ops t (whilePC p) extra _ started _ (initial_while_site p)
    (k_started_pc p ops t s) branchStep

theorem prefix_pc (p : Shape) (ops : Ops α) (t : Nat) (s : State α) :
    (prefixState p ops t s).pc t=firstBarrier p := by simp [prefixState,advance]

theorem prefix_parked (p : Shape) (ops : Ops α) (t : Nat) (s : State α) :
    LarkMFMA.parked (program p) (prefixState p ops t s) t=some .block := by
  simp only [LarkMFMA.parked,prefix_pc,first_barrier_site,blockBarrier,LarkMFMA.scalarCut]

theorem run_lane_parked (p : Shape) (ops : Ops α) (t n : Nat) (s : State α) (cut : LarkMFMA.Cut)
    (hn : 0<n) (hp : LarkMFMA.parked (program p) s t=some cut) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t n s=some s := by
  cases n with
  | zero => omega
  | succ n => simp only [LarkMFMA.runLane,hp]

theorem initial_prefix_run (p : Shape) (ops : Ops α) (t : Nat) (s : State α)
    (ht : t<(geometry p).grid*64) (hp : s.pc t=0) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (fuel p).lane s=
      some (prefixState p ops t s) := by
  have count : 15+4*banks p<512 := by
    rcases banks_cases p with h | h <;> omega
  change LarkMFMA.runLane ops (layout p) (geometry p) (program p) t 512 s=_
  rewrite [show 512=(512-(15+4*banks p))+(15+4*banks p) by omega,
    initial_prefix_eq p ops t (512-(15+4*banks p)) s ht hp]
  exact run_lane_parked p ops t _ _ .block (by omega) (prefix_parked p ops t s)

theorem prefix_setup (p : Shape) (ops : Ops α) (t : Nat) (s : State α) :
    SetupIndices p t (prefixState p ops t s) := by
  have base := setup_of_indices p t (indicesState p t s) (preparedState p ops t s)
    (indices_ready p t s) (zeroed_frames ops t (4*banks p) (indicesState p t s)).2.2.2
  have started := setIndex_setup p t 13 (whilePC p) 0 (preparedState p ops t s) base (by decide)
  exact setup_of_indices p t (kStartedState p ops t s) (prefixState p ops t s) started rfl

theorem prefix_k (p : Shape) (ops : Ops α) (t : Nat) (s : State α) :
    (prefixState p ops t s).indices t 13=some 0 := by
  simp [prefixState,kStartedState,setIndex,advance]

theorem prefix_accumulators (p : Shape) (ops : Ops α) (t r : Nat) (s : State α) (hr : r<4*banks p) :
    (prefixState p ops t s).regs t r=some (ops.literal 0 1) :=
  zeroed_values ops t (4*banks p) r (indicesState p t s) hr

theorem prefix_frames (p : Shape) (ops : Ops α) (t : Nat) (s : State α) :
    (prefixState p ops t s).memory=s.memory ∧ (prefixState p ops t s).trace=s.trace ∧
      (prefixState p ops t s).epochs=s.epochs := by
  have hz := zeroed_frames ops t (4*banks p) (indicesState p t s)
  have hi := indices_frames p t s
  exact ⟨hz.1.trans hi.1,hz.2.1.trans hi.2.1,hz.2.2.1.trans hi.2.2.1⟩

theorem prefix_other (p : Shape) (ops : Ops α) (t u : Nat) (s : State α) (hu : u≠t) :
    (prefixState p ops t s).pc u=s.pc u ∧ (prefixState p ops t s).indices u=s.indices u ∧
      (prefixState p ops t s).regs u=s.regs u := by
  have hz := zeroed_other ops t (4*banks p) u (indicesState p t s) hu
  have hi := indices_other p t u s hu
  have frames := zeroed_frames ops t (4*banks p) (indicesState p t s)
  constructor
  · simpa [prefixState,kStartedState,preparedState,setIndex,advance,hu] using hz.1.trans hi.1
  constructor
  · funext r
    have same := (congrFun (congrFun frames.2.2.2 u) r).trans (congrFun hi.2 r)
    simpa [prefixState,kStartedState,preparedState,setIndex,advance,hu] using same
  · exact hz.2.trans (congrFun (indices_frames p t s).2.2.2 u)

#print axioms prepared_pc
#print axioms k_started_pc
#print axioms initial_prefix_eq
#print axioms prefix_pc
#print axioms prefix_parked
#print axioms run_lane_parked
#print axioms initial_prefix_run
#print axioms prefix_setup
#print axioms prefix_k
#print axioms prefix_accumulators
#print axioms prefix_frames
#print axioms prefix_other
end LarkNativeAwqGemm
