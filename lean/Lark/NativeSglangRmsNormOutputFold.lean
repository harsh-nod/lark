import Lark.NativeSglangRmsNormOutputFrame

/-! Successful actual sequential output-lane execution with native thread
coordinates. All incoming readiness and trace classification are explicit;
successful execution does not assume a safe incoming trace.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot skipFold inactiveWaves scalePairs scaleRounds outputCopies

def laneInverse (ops : Ops α) (input : Nat → Nat → α) (t : Nat) : α :=
  blockInverseValue ops input (t/1024) (t%1024/32)
def laneOutput (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : State α :=
  outputLane ops input (t/1024) (t%1024) t (laneInverse ops input t) s

structure OutputReady (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) : Prop where
  pc : s.pc t=77
  rowIndex : s.indices t 0=some ((t/1024 : Nat) : Int)
  tidIndex : s.indices t 1=some ((t%1024 : Nat) : Int)
  warpIndex : s.indices t 3=some ((t%1024/32 : Nat) : Int)
  inputCached : InputPrefix input (t/1024) (t%1024) 16 t s
  weightCached : WeightPrefix input (t%1024) 16 t s
  shared : s.memory (partialSlot t (t%1024/32))=some (laneInverse ops input t)

theorem output_ready_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α)
    (hr : t/1024<p.rows) (ready : OutputReady ops input t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s=some (laneOutput ops input t s) :=
  output_lane_run p ops input (t/1024) (t%1024) t (laneInverse ops input t) s hr (by omega)
    ready.pc ready.rowIndex ready.tidIndex ready.warpIndex ready.shared ready.inputCached ready.weightCached

theorem output_ready_other (ops : Ops α) (input : Nat → Nat → α) (t u : Nat) (s : State α)
    (hu : u≠t) (ready : OutputReady ops input u s) :
    OutputReady ops input u (laneOutput ops input t s) := by
  dsimp only [laneOutput]
  have h := output_lane_other ops input (t/1024) (t%1024) t u (laneInverse ops input t) s hu
  exact {
    pc := h.1.trans ready.pc
    rowIndex := (congrFun h.2.1 0).trans ready.rowIndex
    tidIndex := (congrFun h.2.1 1).trans ready.tidIndex
    warpIndex := (congrFun h.2.1 3).trans ready.warpIndex
    inputCached := by
      intro k hk
      rw [output_lane_other_private ops input (t/1024) (t%1024) t u 0 k (laneInverse ops input t) s hu]
      exact ready.inputCached k hk
    weightCached := by
      intro k hk
      rw [output_lane_other_private ops input (t/1024) (t%1024) t u 1 k (laneInverse ops input t) s hu]
      exact ready.weightCached k hk
    shared := by
      rw [output_lane_shared ops input (t/1024) (t%1024) t (laneInverse ops input t) s _ rfl]
      exact ready.shared }

theorem resumed_output_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w lane : Nat) (s : State α) (reads : Reads p input s) (hw : w<16) (hl : lane<64) :
    OutputReady ops input (cohortBase row w+lane)
      (resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)) := by
  let t := cohortBase row w+lane
  let tid := w*64+lane
  let reached := resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)
  change OutputReady ops input t reached
  have ht := cohort_in_block p row w t hw ((cohort_mem row w 64 t).mpr ⟨lane,hl,rfl⟩)
  have coords := cohort_arithmetic row w lane hw hl
  have hrow : t/1024=row := coords.1
  have htid : t%1024=tid := coords.2.1
  have idx := resumed_twice_indices p ops input row t s reads ht
  have caches := resumed_twice_caches p ops input row w lane s reads hw hl
  constructor
  · exact resumed_second_block_pc p ops input row t (resumedFirstBlock p ops input row s) ht
  · exact idx.1
  · exact idx.2.1
  · exact idx.2.2.2
  · rw [hrow,htid]
    exact caches.1
  · rw [htid]
    exact caches.2
  · change reached.memory ⟨.shared,t/1024,0,t%1024/32⟩=some (blockInverseValue ops input (t/1024) (t%1024/32))
    rw [hrow,htid]
    exact resumed_twice_shared_values p ops input row (tid/32) s (by dsimp only [tid]; omega)

def outputFold (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) : State α :=
  ts.foldl (fun s t => laneOutput ops input t s) s

theorem output_fold_cons (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (ts : List Nat) (s : State α) :
    outputFold ops input (t::ts) s=outputFold ops input ts (laneOutput ops input t s) := rfl

theorem output_fold_epochs (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (outputFold ops input ts s).epochs=s.epochs := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih => exact (ih (laneOutput ops input t s)).trans (output_lane_epochs ops input (t/1024) (t%1024) t (laneInverse ops input t) s)

theorem output_fold_other (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (u : Nat)
    (s : State α) (hu : u∉ts) :
    (outputFold ops input ts s).pc u=s.pc u ∧ (outputFold ops input ts s).indices u=s.indices u ∧
    (outputFold ops input ts s).regs u=s.regs u := by
  induction ts generalizing s with
  | nil => exact ⟨rfl,rfl,rfl⟩
  | cons t ts ih =>
      have hne : u≠t := by intro he; subst u; simp at hu
      have hn : u∉ts := by intro hm; exact hu (by simp [hm])
      have h := ih (laneOutput ops input t s) hn
      have hs := output_lane_other ops input (t/1024) (t%1024) t u (laneInverse ops input t) s hne
      exact ⟨h.1.trans hs.1,h.2.1.trans hs.2.1,h.2.2.trans hs.2.2⟩

theorem output_fold_member_pc (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (t : Nat) (ht : t∈ts) : (outputFold ops input ts s).pc t=109 := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        exact (output_fold_other ops input ts u (laneOutput ops input u s) hnot).1.trans
          (output_lane_pc ops input (u/1024) (u%1024) u (laneInverse ops input u) s)
      · exact ih (laneOutput ops input u s) hnodup hm

theorem output_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (bounds : ∀ t∈ts,t/1024<p.rows) (ready : ∀ t∈ts,OutputReady ops input t s) :
    ts.foldlM (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane u) s=
      some (outputFold ops input ts s) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rw [List.foldlM_cons,output_ready_run p ops input t s (bounds t (by simp)) (ready t (by simp))]
      apply ih (laneOutput ops input t s) hnodup
      · intro u hu; exact bounds u (by simp [hu])
      · intro u hu
        have hne : u≠t := by intro he; subst u; exact hnot hu
        exact output_ready_other ops input t u s hne (ready u (by simp [hu]))

theorem output_fold_ready_other (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (u : Nat) (s : State α) (hu : u∉ts) (ready : OutputReady ops input u s) :
    OutputReady ops input u (outputFold ops input ts s) := by
  induction ts generalizing s with
  | nil => exact ready
  | cons t ts ih =>
      have hn : u∉ts := by intro hm; exact hu (by simp [hm])
      have hne : u≠t := by intro he; subst u; simp at hu
      exact ih (laneOutput ops input t s) hn (output_ready_other ops input t u s hne ready)

theorem output_fold_previous_output (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat)
    (offset : Nat) (s : State α) (outside : writer offset∉ts) :
    (outputFold ops input ts s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
      have hn : writer offset∉ts := by intro hm; exact outside (by simp [hm])
      have hne : writer offset≠t := by intro he; rw [he] at outside; simp at outside
      exact (ih (laneOutput ops input t s) hn).trans
        (output_lane_previous_output ops input (t/1024) (t%1024) t offset (laneInverse ops input t) s (by omega) (by omega) hne)

theorem output_fold_values (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (ready : ∀ t∈ts,OutputReady ops input t s) (t : Nat) (ht : t∈ts) :
    GlobalPrefix ops input (t/1024) (t%1024) 16 (laneInverse ops input t) (outputFold ops input ts s) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rw [output_fold_cons]
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        intro k hk
        have owner : writer (flatAddress (u/1024) (u%1024) k)=u := by
          dsimp only [flatAddress]
          rw [address_writer (u/1024) (u%1024) (k/8) (k%8) (by omega) (by omega) (by omega)]
          omega
        rw [output_fold_previous_output ops input ts _ _ (by rwa [owner])]
        have r := ready u (by simp)
        exact output_lane_prefix ops input (u/1024) (u%1024) u (laneInverse ops input u) s r.rowIndex r.tidIndex r.inputCached r.weightCached k hk
      · apply ih (laneOutput ops input u s) hnodup _ hm
        intro v hv
        have hne : v≠u := by intro he; subst v; exact hnot hv
        exact output_ready_other ops input u v s hne (ready v (by simp [hv]))

theorem output_fold_trace_length (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α) :
    (outputFold ops input ts s).trace.length=s.trace.length+81*ts.length := by
  induction ts generalizing s with
  | nil => simp only [outputFold,List.foldl_nil,List.length_nil,Nat.mul_zero,Nat.add_zero]
  | cons t ts ih =>
      rw [output_fold_cons,ih]
      dsimp only [laneOutput]
      rw [output_lane_trace_length]
      simp only [List.length_cons,Nat.mul_succ]
      omega

theorem output_fold_good (ops : Ops α) (input : Nat → Nat → α) (ts : List Nat) (s : State α)
    (epochs : ∀ t∈ts,(s.epochs t).block=2) (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(outputFold ops input ts s).trace,Good event := by
  induction ts generalizing s with
  | nil => exact good
  | cons t ts ih =>
      apply ih (laneOutput ops input t s)
      · intro u hu
        dsimp only [laneOutput]
        rw [output_lane_epochs]
        exact epochs u (by simp [hu])
      · exact output_lane_good ops input (t/1024) (t%1024) t (laneInverse ops input t) s (by omega) (by omega)
          (epochs t (by simp)) good

#print axioms output_ready_run
#print axioms output_ready_other
#print axioms resumed_output_ready
#print axioms output_fold_cons
#print axioms output_fold_epochs
#print axioms output_fold_other
#print axioms output_fold_member_pc
#print axioms output_fold_run
#print axioms output_fold_ready_other
#print axioms output_fold_previous_output
#print axioms output_fold_values
#print axioms output_fold_trace_length
#print axioms output_fold_good
end LarkNativeSglangRmsNorm
