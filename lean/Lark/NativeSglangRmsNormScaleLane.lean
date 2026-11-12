import Lark.NativeSglangRmsNormScaleRound
import Lark.NativeSglangRmsNormSecondBlockData

/-! From the reached second-barrier resumption through the actual inverse load
and both scaling rounds. All16 private output halves are established at PC97;
the global copy loop remains an explicit native scalar continuation.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setReg setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold firstBlockFold secondFold regAddFold inverseFold secondSnapshot skipFold inactiveWaves scalePairs scaleRounds

def outputScaleStart (t warp : Nat) (inverse : α) (s : State α) : State α :=
  setIndex (setReg (record s t (partialSlot t warp) false) t 12 inverse 78) t 16 0 79

theorem output_scale_start_eq (p : Shape) (ops : Ops α) (t warp extra : Nat) (inverse : α) (s : State α)
    (hw : warp<32) (hi : s.indices t 3=some (warp : Int))
    (hm : s.memory (partialSlot t warp)=some inverse) (hp : s.pc t=77) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+2) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra (outputScaleStart t warp inverse s) := by
  let s1 := setReg (record s t (partialSlot t warp) false) t 12 inverse 78
  have loc : location (layout p) (geometry p) t .shared 0 (warp : Int) false=some (partialSlot t warp) := by
    simp [location,layout,geometry,partialSlot,show ¬(warp : Int)<0 by omega,hw]
  have e1 : execute ops (layout p) (geometry p) t (.assign 12 (.load .shared 0 (.ivar 3))) s=some s1 := by
    simp [execute,evalExpr,evalIndex,hi,loc,hm,hp,s1,setReg,advance,record]
  have e2 := execute_index_of ops (layout p) (geometry p) t 16 79 (.const 0) s1 0 rfl (by simp [s1,setReg,advance])
  rw [scalar_step p true ops t 77 (extra+1) _ s s1 (by decide) hp e1]
  exact scalar_step p true ops t 78 extra _ s1 _ (by decide) (by simp [s1,setReg,advance]) e2

theorem output_scale_start_ready (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α)
    (h0 : s.indices t 0=some (row : Int)) (h1 : s.indices t 1=some (tid : Int))
    (cached : InputPrefix input row tid 16 t s) (weights : WeightPrefix input tid 16 t s) :
    ScaleRoundReady ops input row tid 0 t inverse (outputScaleStart t (tid/32) inverse s) := by
  exact {
    pc := by simp [outputScaleStart,setIndex,setReg,advance]
    rowIndex := by simpa [outputScaleStart,setIndex,setReg,advance,record] using h0
    tidIndex := by simpa [outputScaleStart,setIndex,setReg,advance,record] using h1
    iterationIndex := by simp [outputScaleStart,setIndex,setReg,advance]
    scale := by simp [outputScaleStart,setIndex,setReg,advance,record]
    inputCached := cached,weightCached := weights
    completed := by intro k hk; omega }

def scaledLane (ops : Ops α) (input : Nat → Nat → α) (row tid t : Nat)
    (inverse : α) (s : State α) : State α :=
  advance (scaleRounds ops input row tid t inverse 0 2 (outputScaleStart t (tid/32) inverse s)) t 97

theorem scaled_lane_eq (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid t extra : Nat) (inverse : α) (s : State α) (ht : tid<1024) (hp : s.pc t=77)
    (h0 : s.indices t 0=some (row : Int)) (h1 : s.indices t 1=some (tid : Int))
    (h3 : s.indices t 3=some ((tid/32 : Nat) : Int)) (shared : s.memory (partialSlot t (tid/32))=some inverse)
    (cached : InputPrefix input row tid 16 t s) (weights : WeightPrefix input tid 16 t s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+125) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
      (scaledLane ops input row tid t inverse s) := by
  let entry := outputScaleStart t (tid/32) inverse s
  let rounds := scaleRounds ops input row tid t inverse 0 2 entry
  have r0 := output_scale_start_ready ops input row tid t inverse s h0 h1 cached weights
  have r2 := scale_rounds_ready ops input row tid t 0 2 inverse entry r0
  rw [show extra+125=(extra+123)+2 by omega,
    output_scale_start_eq p ops t (tid/32) (extra+123) inverse s (by omega) h3 shared hp]
  rw [show extra+123=(extra+1)+61*2 by omega,
    scale_rounds_eq p ops input row tid t 0 2 (extra+1) inverse entry (by decide) r0]
  exact scale_rounds_exit_eq p ops t extra rounds r2.pc r2.iterationIndex

theorem scaled_lane_prefix (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α)
    (h0 : s.indices t 0=some (row : Int)) (h1 : s.indices t 1=some (tid : Int))
    (cached : InputPrefix input row tid 16 t s) (weights : WeightPrefix input tid 16 t s) :
    OutputPrefix ops input row tid 16 t inverse (scaledLane ops input row tid t inverse s) := by
  have r2 := scale_rounds_ready ops input row tid t 0 2 inverse (outputScaleStart t (tid/32) inverse s)
    (output_scale_start_ready ops input row tid t inverse s h0 h1 cached weights)
  exact r2.completed

theorem scaled_lane_fields (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α)
    (h0 : s.indices t 0=some (row : Int)) (h1 : s.indices t 1=some (tid : Int))
    (cached : InputPrefix input row tid 16 t s) (weights : WeightPrefix input tid 16 t s) :
    (scaledLane ops input row tid t inverse s).pc t=97 ∧
    (scaledLane ops input row tid t inverse s).indices t 0=some (row : Int) ∧
    (scaledLane ops input row tid t inverse s).indices t 1=some (tid : Int) ∧
    InputPrefix input row tid 16 t (scaledLane ops input row tid t inverse s) ∧
    WeightPrefix input tid 16 t (scaledLane ops input row tid t inverse s) := by
  have r2 := scale_rounds_ready ops input row tid t 0 2 inverse (outputScaleStart t (tid/32) inverse s)
    (output_scale_start_ready ops input row tid t inverse s h0 h1 cached weights)
  exact ⟨by simp [scaledLane,advance],r2.rowIndex,r2.tidIndex,r2.inputCached,r2.weightCached⟩

theorem scaled_lane_epochs (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) :
    (scaledLane ops input row tid t inverse s).epochs=s.epochs := by
  simp only [scaledLane,advance,scale_rounds_epochs,outputScaleStart,setReg,setIndex,record]

theorem scaled_lane_memory_outside (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) (l : Location) (hl : OutsideOutput t l) :
    (scaledLane ops input row tid t inverse s).memory l=s.memory l :=
  scale_rounds_memory_outside ops input row tid t 0 2 inverse (outputScaleStart t (tid/32) inverse s) l hl

theorem scaled_lane_trace_length (ops : Ops α) (input : Nat → Nat → α)
    (row tid t : Nat) (inverse : α) (s : State α) :
    (scaledLane ops input row tid t inverse s).trace.length=s.trace.length+49 := by
  simp only [scaledLane,advance,scale_rounds_trace_length,outputScaleStart,setReg,setIndex,record,List.length_cons]

theorem scaled_lane_good (ops : Ops α) (input : Nat → Nat → α)
    (row t : Nat) (inverse : α) (s : State α) (epoch : (s.epochs t).block=2)
    (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(scaledLane ops input row (t%1024) t inverse s).trace,Good event := by
  apply scale_rounds_good
  intro event he
  change event∈⟨t,partialSlot t ((t%1024)/32),false,s.epochs t⟩::s.trace at he
  rcases List.mem_cons.mp he with rfl | he
  · exact Good.inverseRead rfl rfl rfl rfl epoch rfl
  · exact good event he

theorem resumed_output_scaling (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row w lane : Nat) (s : State α) (reads : Reads p input s) (hw : w<16) (hl : lane<64) :
    let t := cohortBase row w+lane
    let tid := w*64+lane
    let reached := resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane reached=
      LarkCollective.runLane ops (layout p) (geometry p) (program true) t 387
        (scaledLane ops input row tid t (blockInverseValue ops input row (tid/32)) reached) := by
  dsimp only
  let t := cohortBase row w+lane
  let tid := w*64+lane
  let reached := resumedSecondBlock p ops input row (resumedFirstBlock p ops input row s)
  have ht := cohort_in_block p row w t hw ((cohort_mem row w 64 t).mpr ⟨lane,hl,rfl⟩)
  have coords := cohort_arithmetic row w lane hw hl
  have hrow : t/1024=row := coords.1
  have htid : t%1024=tid := coords.2.1
  have indices := resumed_twice_indices p ops input row t s reads ht
  have caches := resumed_twice_caches p ops input row w lane s reads hw hl
  apply scaled_lane_eq p ops input row tid t 387 _ reached (by dsimp only [tid]; omega)
  · exact resumed_second_block_pc p ops input row t (resumedFirstBlock p ops input row s) ht
  · simpa only [hrow] using indices.1
  · simpa only [htid] using indices.2.1
  · simpa only [htid] using indices.2.2.2
  · change reached.memory ⟨.shared,t/1024,0,tid/32⟩=_
    rw [hrow]
    exact resumed_twice_shared_values p ops input row (tid/32) s (by dsimp only [tid]; omega)
  · exact caches.1
  · exact caches.2

#print axioms output_scale_start_eq
#print axioms output_scale_start_ready
#print axioms scaled_lane_eq
#print axioms scaled_lane_prefix
#print axioms scaled_lane_fields
#print axioms scaled_lane_epochs
#print axioms scaled_lane_memory_outside
#print axioms scaled_lane_trace_length
#print axioms scaled_lane_good
#print axioms resumed_output_scaling
end LarkNativeSglangRmsNorm
