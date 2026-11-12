import Lark.NativeAwqGemmOutputIndex

/-! Actual final FP32-to-half conversion and guarded global output store. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

theorem location_global_output (p : Shape) (t offset : Nat) (hi : offset<p.m*p.n) :
    location (layout p) (geometry p) t .global 2 (offset : Int) true=some (globalCell 2 offset) := by
  have nonnegative : ¬(offset : Int)<0 := by omega
  simp [location,layout,globalCell,nonnegative,hi,show (Role.output == Role.input)=false by decide]

def outputStored (p : Shape) (ops : Ops α) (t q : Nat) (value : α) (s : State α) : State α :=
  written s t (outCell p t q) (ops.toHalf value) (outPC p (q+1))

theorem output_store_execute (p : Shape) (ops : Ops α) (t q : Nat) (value : α) (s : State α)
    (hq : q<4*banks p) (setup : SetupIndices p t s) (guard : globalOutputRow p t (q%4)<p.m)
    (hr : s.regs t q=some value) (hp : s.pc t=outPC p q+1) :
    execute ops (layout p) (geometry p) t
      (.store .global 2 (outputIndex p (q/4) (q%4)) (.un .toHalf (.reg q))) s=some (outputStored p ops t q value s) :=
  execute_store_of ops p t 2 (outPC p (q+1)) .global (outputIndex p (q/4) (q%4)) (.un .toHalf (.reg q)) s s
    ((outOffset p t q : Nat) : Int) (outCell p t q) (ops.toHalf value)
    (eval_output_address p t q s hq setup guard)
    (location_global_output p t (outOffset p t q) (out_offset_bound p t q hq guard))
    (by simp [evalExpr,applyUnary,hr]) (by rw [hp]; unfold outPC; omega)

theorem output_store_run (p : Shape) (ops : Ops α) (t q extra : Nat) (value : α) (s : State α)
    (hq : q<4*banks p) (setup : SetupIndices p t s) (guard : globalOutputRow p t (q%4)<p.m)
    (hr : s.regs t q=some value) (hp : s.pc t=outPC p q+1) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (outputStored p ops t q value s) :=
  scalar_step p ops t (outPC p q+1) extra _ s _ (output_store_site p q hq) hp
    (output_store_execute p ops t q value s hq setup guard hr hp)

theorem output_stored_value (p : Shape) (ops : Ops α) (t q : Nat) (value : α) (s : State α) :
    (outputStored p ops t q value s).memory (outCell p t q)=some (ops.toHalf value) := by
  simp [outputStored,written,advance]

theorem output_stored_other (p : Shape) (ops : Ops α) (t q : Nat) (value : α) (s : State α)
    (loc : Location) (hl : loc≠outCell p t q) : (outputStored p ops t q value s).memory loc=s.memory loc := by
  simp [outputStored,written,advance,record,hl]

theorem output_stored_trace (p : Shape) (ops : Ops α) (t q : Nat) (value : α) (s : State α) :
    (outputStored p ops t q value s).trace=⟨t,outCell p t q,true,s.epochs t⟩::s.trace := rfl

theorem output_stored_frames (p : Shape) (ops : Ops α) (t q : Nat) (value : α) (s : State α) :
    (outputStored p ops t q value s).indices=s.indices ∧ (outputStored p ops t q value s).regs=s.regs ∧
      (outputStored p ops t q value s).epochs=s.epochs := ⟨rfl,rfl,rfl⟩

theorem output_stored_reads (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (t q : Nat) (value : α)
    (s : State α) (reads : Reads p input s) : Reads p input (outputStored p ops t q value s) := by
  constructor
  · intro i hi
    have different : globalCell 0 i≠outCell p t q := by
      intro same; have impossible := congrArg Location.buffer same; cases impossible
    simpa only [outputStored,written,advance,record,if_neg different] using reads.1 i hi
  · intro i hi
    have different : globalCell 1 i≠outCell p t q := by
      intro same; have impossible := congrArg Location.buffer same; cases impossible
    simpa only [outputStored,written,advance,record,if_neg different] using reads.2 i hi

#print axioms location_global_output
#print axioms output_store_execute
#print axioms output_store_run
#print axioms output_stored_value
#print axioms output_stored_other
#print axioms output_stored_trace
#print axioms output_stored_frames
#print axioms output_stored_reads
end LarkNativeAwqGemm
