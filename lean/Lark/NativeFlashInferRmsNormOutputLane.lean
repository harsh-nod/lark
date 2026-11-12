import Lark.NativeFlashInferRmsNormOutputRound

/-! Actual 192-instruction output phase of any valid native lane, from PC47
through normalization and sixteen stores to halt at PC67. Whole-wave/block/grid
composition and a canonical-real reference theorem remain separate work.
-/
namespace LarkNativeFlashInferRmsNorm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def outputBeforeHalt (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α) : State α :=
  let inverse := outputInverse ops total
  let s := outputEntered ops t row total s
  let s := outputRound ops input row tid 0 t inverse s
  outputRound ops input row tid 1 t inverse s

def outputLane (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α) : State α :=
  advance (outputBeforeHalt ops input row tid t total s) t 67

theorem output_entered_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α)
    (hr : t / 1024 = row) (h0 : s.indices t 0 = some (row : Int))
    (h1 : s.indices t 1 = some (tid : Int)) (reads : OutputReads ops input row s)
    (epoch : (s.epochs t).block = 2) (good : ∀ a ∈ s.trace, Good a) :
    OutputStartReady ops input row tid 0 t (outputInverse ops total) (outputEntered ops t row total s) := by
  obtain ⟨hp,hr0,hr1,hi,hx⟩ := output_entry_fields ops t row total s
  exact {
    pc := hp, rowIndex := hr0.trans h0, tidIndex := hr1.trans h1, iterationIndex := hi, scale := hx
    reads := reads
    completed := by intro j hj; omega
    good := output_entry_good ops t row total s hr epoch good }

theorem output_before_halt_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α) (ht : tid < 1024) (he : t = row * 1024 + tid)
    (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 1 = some (tid : Int))
    (reads : OutputReads ops input row s) (epoch : (s.epochs t).block = 2)
    (good : ∀ a ∈ s.trace, Good a) :
    OutputStartReady ops input row tid 2 t (outputInverse ops total) (outputBeforeHalt ops input row tid t total s) := by
  have hr : t / 1024 = row := by omega
  have r0 := output_entered_ready ops input row tid t total s hr h0 h1 reads epoch good
  have r1 := output_round_ready p ops input row tid 0 t (outputInverse ops total)
    (outputEntered ops t row total s) ht (by decide) he r0
  exact output_round_ready p ops input row tid 1 t (outputInverse ops total) _ ht (by decide) he r1

theorem output_lane_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t extra : Nat) (total : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (he : t = row * 1024 + tid)
    (hp : s.pc t = 47) (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 1 = some (tid : Int))
    (hm : s.memory (partialSlot row 0) = some total) (reads : OutputReads ops input row s)
    (epoch : (s.epochs t).block = 2) (good : ∀ a ∈ s.trace, Good a) :
    LarkCollective.runLane ops (layout p) (geometry p) program t (extra + 192) s =
      LarkCollective.runLane ops (layout p) (geometry p) program t extra (outputLane ops input row tid t total s) := by
  have hrow : t / 1024 = row := by omega
  let inverse := outputInverse ops total
  let s0 := outputEntered ops t row total s
  let s1 := outputRound ops input row tid 0 t inverse s0
  let s2 := outputRound ops input row tid 1 t inverse s1
  have r0 := output_entered_ready ops input row tid t total s hrow h0 h1 reads epoch good
  have r1 := output_round_ready p ops input row tid 0 t inverse s0 ht (by decide) he r0
  have r2 := output_before_halt_ready p ops input row tid t total s ht he h0 h1 reads epoch good
  rewrite [show extra + 192 = (extra + 187) + 5 by omega,
    output_entry_eq p ops t row (extra + 187) total s hrow hp hm]
  rewrite [show extra + 187 = (extra + 94) + 93 by omega,
    output_round_eq p ops input row tid 0 t (extra + 94) inverse s0 hr ht (by decide) he r0]
  rewrite [show extra + 94 = (extra + 1) + 93 by omega,
    output_round_eq p ops input row tid 1 t (extra + 1) inverse s1 hr ht (by decide) he r1]
  exact output_exit_rounds_eq p ops t extra s2 r2.pc r2.iterationIndex

theorem output_lane_pc (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α) : (outputLane ops input row tid t total s).pc t = 67 := by
  simp [outputLane, advance]

theorem output_lane_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α)
    (hr : row < p.rows) (ht : tid < 1024) (he : t = row * 1024 + tid)
    (hp : s.pc t = 47) (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 1 = some (tid : Int))
    (hm : s.memory (partialSlot row 0) = some total) (reads : OutputReads ops input row s)
    (epoch : (s.epochs t).block = 2) (good : ∀ a ∈ s.trace, Good a) :
    LarkCollective.runLane ops (layout p) (geometry p) program t fuel.lane s =
      some (outputLane ops input row tid t total s) := by
  have parked : LarkCollective.parked program (outputLane ops input row tid t total s) t = some .halt := by
    simp only [LarkCollective.parked, output_lane_pc, final_halt]
  change LarkCollective.runLane ops (layout p) (geometry p) program t (320 + 192) s = _
  rewrite [output_lane_eq p ops input row tid t 320 total s hr ht he hp h0 h1 hm reads epoch good]
  simp only [LarkCollective.runLane, parked]

theorem output_lane_values (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α) (ht : tid < 1024) (he : t = row * 1024 + tid)
    (h0 : s.indices t 0 = some (row : Int)) (h1 : s.indices t 1 = some (tid : Int))
    (reads : OutputReads ops input row s) (epoch : (s.epochs t).block = 2) (good : ∀ a ∈ s.trace, Good a) :
    OutputCompleted ops input row tid (outputInverse ops total) 16 (outputLane ops input row tid t total s) ∧
    OutputReads ops input row (outputLane ops input row tid t total s) ∧
    (∀ a ∈ (outputLane ops input row tid t total s).trace, Good a) := by
  have ready := output_before_halt_ready p ops input row tid t total s ht he h0 h1 reads epoch good
  exact ⟨ready.completed, ready.reads, ready.good⟩

theorem output_lane_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (total : α) (s : State α) :
    (outputLane ops input row tid t total s).trace.length = s.trace.length + 49 := by
  simp only [outputLane, advance, outputBeforeHalt, output_round_trace_length]
  change (s.trace.length + 1) + 24 + 24 = s.trace.length + 49
  omega

theorem out_ready_lane_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid : Nat) (s : State α) (ready : OutReady p ops input row s) (ht : tid < 1024) :
    LarkCollective.runLane ops (layout p) (geometry p) program (row * 1024 + tid) fuel.lane s =
      some (outputLane ops input row tid (row * 1024 + tid) (blockSum ops input row) s) := by
  have hrow : (row * 1024 + tid) / 1024 = row := by omega
  have htid : (row * 1024 + tid) % 1024 = tid := by omega
  have inds := ready.indices tid ht
  exact output_lane_run p ops input row tid _ _ s ready.valid ht rfl (ready.pc tid ht)
    (by simpa only [hrow] using inds.1) (by simpa only [htid] using inds.2.1)
    ready.total (out_ready_reads p ops input row s ready) (ready.epoch tid ht) ready.good

theorem initial_output_lane_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (row tid : Nat) (hr : row < p.rows) (ht : tid < 1024) :
    let s := outState p ops input row (midState p ops input row (initial p input outside))
    LarkCollective.runLane ops (layout p) (geometry p) program (row * 1024 + tid) fuel.lane s =
      some (outputLane ops input row tid (row * 1024 + tid) (blockSum ops input row) s) :=
  out_ready_lane_run p ops input row tid _ (initial_out_ready p ops input outside row hr) ht

#print axioms output_entered_ready
#print axioms output_before_halt_ready
#print axioms output_lane_eq
#print axioms output_lane_pc
#print axioms output_lane_run
#print axioms output_lane_values
#print axioms output_lane_trace_length
#print axioms out_ready_lane_run
#print axioms initial_output_lane_run
end LarkNativeFlashInferRmsNorm
