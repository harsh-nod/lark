import Lark.NativeSglangRmsNormXorState

/-! Actual physical-wave preparation and first XOR snapshot, for arbitrary prior
trace. Later additions, shuffles, shared stores and barriers remain explicit.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold

def wavePrepared (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) : State α :=
  prefixFold ops input (cohortThreads row warp 64) s

def firstSnapshot (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (row warp : Nat) (s : State α) : State α :=
  shuffleUpdates 1 (xorSnapshot p row warp 64 16 (fun lane => threadSum ops input row (warp * 64 + lane)))
    (wavePrepared ops input row warp s)

theorem wave_prepared_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (reads : Reads p input s) (hl : lane < 64) :
    PrefixReady p ops input (cohortBase row warp + lane) (wavePrepared ops input row warp s) :=
  prefix_fold_member p ops input _ s (cohort_nodup row warp 64) reads _
    ((cohort_mem row warp 64 _).mpr ⟨lane,hl,rfl⟩)

theorem wave_prepared_next (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (reads : Reads p input s) :
    LarkPartitionCollective.nextCohort (program repaired) (cohortThreads row warp 64)
      (wavePrepared ops input row warp s) = some (cohortThreads row warp 64) := by
  apply cohort_next repaired row warp 64 44 _ (by decide)
  · intro lane hl; exact (wave_prepared_ready p ops input row warp lane s reads hl).pc
  · intro t ht
    simp only [LarkPartitionCollective.isShuffle,ht]
    cases repaired <;> rfl

theorem wave_first_shuffle (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp < 16) (reads : Reads p input s) :
    LarkPartitionCollective.runShuffle (geometry p) (program repaired) (cohortThreads row warp 64)
      (wavePrepared ops input row warp s) = some (firstSnapshot p ops input row warp s) := by
  apply cohort_xor_shuffle p repaired row warp 64 16 44 _ _ hw (Or.inr rfl) (by decide)
  · intro lane hl; exact (wave_prepared_ready p ops input row warp lane s reads hl).pc
  · intro lane hl
    have h := (wave_prepared_ready p ops input row warp lane s reads hl).accumulator
    have coords := cohort_arithmetic row warp lane hw hl
    simpa only [coords.1,coords.2.1] using h
  · cases repaired <;> decide

theorem wave_first_snapshot_step (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp n : Nat) (s : State α) (hr : row < p.rows) (hw : warp < 16)
    (hp : ∀ t ∈ cohortThreads row warp 64, s.pc t = 0) (reads : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (warpThreads (geometry p) row warp) (n + 1) s =
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program repaired)
      (cohortThreads row warp 64) n (firstSnapshot p ops input row warp s) := by
  rewrite [native_prefix_step p repaired ops input row warp n s hr hw hp reads]
  change continueCohort p repaired ops (cohortThreads row warp 64) n
    (wavePrepared ops input row warp s) = _
  unfold continueCohort
  rw [wave_prepared_next p repaired ops input row warp s reads]
  dsimp only
  rw [wave_first_shuffle p repaired ops input row warp s hw reads]
  rfl

theorem wave_entry_success (p : Shape) (repaired : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hr : row < p.rows) (hw : warp < 16)
    (hp : ∀ t ∈ cohortThreads row warp 64, s.pc t = 0) (reads : Reads p input s) :
    ((warpThreads (geometry p) row warp).foldlM
      (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program repaired) t fuel.lane u) s).bind
      (fun prepared => LarkPartitionCollective.runShuffle (geometry p) (program repaired)
        (cohortThreads row warp 64) prepared) = some (firstSnapshot p ops input row warp s) := by
  rw [cohort_native_threads p row warp hw,
    prefix_fold_run p repaired ops input _ s (cohort_nodup row warp 64)
      (cohort_bound p row warp 64 hr hw (by decide)) hp reads]
  simp only [Option.some_bind]
  exact wave_first_shuffle p repaired ops input row warp s hw reads

theorem wave_snapshot_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp < 16) (hl : lane < 64) (reads : Reads p input s) :
    (firstSnapshot p ops input row warp s).pc (cohortBase row warp + lane) = 45 ∧
    (firstSnapshot p ops input row warp s).regs (cohortBase row warp + lane) 0 =
      some (threadSum ops input row (warp * 64 + lane)) ∧
    (firstSnapshot p ops input row warp s).regs (cohortBase row warp + lane) 1 =
      some (threadSum ops input row (warp * 64 + xorPeer32 lane 16)) := by
  have h := xor_shuffled_fields p row warp 64 16 lane
    (fun lane => threadSum ops input row (warp * 64 + lane)) (wavePrepared ops input row warp s)
    hw (by decide) hl
  have ready := wave_prepared_ready p ops input row warp lane s reads hl
  have coords := cohort_arithmetic row warp lane hw hl
  simpa only [ready.pc,ready.accumulator,coords.1,coords.2.1] using h

theorem wave_snapshot_preserves (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) :
    (firstSnapshot p ops input row warp s).memory = (wavePrepared ops input row warp s).memory ∧
    (firstSnapshot p ops input row warp s).indices = (wavePrepared ops input row warp s).indices ∧
    (firstSnapshot p ops input row warp s).epochs = s.epochs ∧
    (firstSnapshot p ops input row warp s).trace = (wavePrepared ops input row warp s).trace := by
  exact ⟨rfl,rfl,prefix_fold_epochs ops input _ s,rfl⟩

theorem wave_snapshot_caches (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp < 16) (hl : lane < 64) (reads : Reads p input s) :
    let t := cohortBase row warp + lane
    InputPrefix input row (warp * 64 + lane) 16 t (firstSnapshot p ops input row warp s) ∧
    WeightPrefix input (warp * 64 + lane) 16 t (firstSnapshot p ops input row warp s) := by
  have ready := wave_prepared_ready p ops input row warp lane s reads hl
  have coords := cohort_arithmetic row warp lane hw hl
  have h := And.intro ready.inputs ready.weights
  unfold InputPrefix WeightPrefix
  rw [(wave_snapshot_preserves p ops input row warp s).1]
  simpa only [InputPrefix,WeightPrefix,coords.1,coords.2.1] using h

theorem wave_snapshot_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (reads : Reads p input s) :
    Reads p input (firstSnapshot p ops input row warp s) := by
  unfold Reads
  rw [(wave_snapshot_preserves p ops input row warp s).1]
  exact prefix_fold_reads p ops input _ s reads

theorem wave_snapshot_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) :
    (firstSnapshot p ops input row warp s).trace.length = s.trace.length + 5120 := by
  simpa only [cohortThreads,List.length_map,List.length_range] using
    prefix_fold_trace_length ops input (cohortThreads row warp 64) s

theorem prefix_fold_trace_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (ts : List Nat) (s : State α) (reads : Reads p input s) :
    ∃ events, (prefixFold ops input ts s).trace = events ++ s.trace ∧
      events.length = 80 * ts.length ∧ (∀ a ∈ events, Good a) := by
  induction ts generalizing s with
  | nil => exact ⟨[],by simp [prefixFold],rfl,by intro a ha; cases ha⟩
  | cons t ts ih =>
      obtain ⟨later,hlater,hlen,hgood⟩ := ih (prefixState ops input t s) (prefix_reads_frame p ops input t s reads)
      let here := (prefixState ops input t {s with trace := []}).trace
      have hhere : here.length = 80 := by
        simpa only [List.length_nil,Nat.zero_add] using
          (prefix_trace_length ops input t {s with trace := []})
      refine ⟨later ++ here,?_,?_,?_⟩
      · simp only [prefixFold,List.foldl_cons] at hlater ⊢
        rw [hlater,carried_prefix_trace,List.append_assoc]
      · simp only [List.length_append,hlen,hhere,List.length_cons]
        omega
      · intro a ha
        rcases List.mem_append.mp ha with h | h
        · exact hgood a h
        · exact carried_new_events_good p ops input t s reads a h

theorem wave_snapshot_trace_tail (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (reads : Reads p input s) :
    ∃ events, (firstSnapshot p ops input row warp s).trace = events ++ s.trace ∧
      events.length = 5120 ∧ (∀ a ∈ events, Good a) := by
  simpa only [cohortThreads,List.length_map,List.length_range] using prefix_fold_trace_tail p ops input (cohortThreads row warp 64) s reads

theorem initial_wave_snapshot_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row warp : Nat) :
    raceFree (geometry p) (firstSnapshot p ops input row warp (initial p input outside)).trace = true :=
  initial_prefix_fold_race_free p ops input outside _

#print axioms wave_prepared_ready
#print axioms wave_prepared_next
#print axioms wave_first_shuffle
#print axioms wave_first_snapshot_step
#print axioms wave_entry_success
#print axioms wave_snapshot_values
#print axioms wave_snapshot_preserves
#print axioms wave_snapshot_caches
#print axioms wave_snapshot_reads
#print axioms wave_snapshot_trace_length
#print axioms prefix_fold_trace_tail
#print axioms wave_snapshot_trace_tail
#print axioms initial_wave_snapshot_race_free
end LarkNativeSglangRmsNorm
