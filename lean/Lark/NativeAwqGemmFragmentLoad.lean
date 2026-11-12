import Lark.NativeAwqGemmFragmentValues

/-! Actual shared read/packed-half register assignment for native operands.
Every scalar read contributes its original thread, location and epoch event. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def fragmentLoaded (t r pc : Nat) (loc : Location) (value : α) (s : State α) : State α :=
  setReg (record s t loc false) t r value pc

theorem execute_fragment_load_of (p : Shape) (ops : Ops α) (t buffer r pc : Nat)
    (index : Index) (offset : Int) (loc : Location) (value : α) (s : State α)
    (hi : evalIndex (geometry p) t s index=some offset)
    (hl : location (layout p) (geometry p) t .shared buffer offset false=some loc)
    (hm : s.memory loc=some value) (hp : s.pc t+1=pc) :
    execute ops (layout p) (geometry p) t (.assign r (.load .shared buffer index)) s=
      some (fragmentLoaded t r pc loc value s) := by
  simp only [execute,evalExpr,hi,hl,hm,bind,pure,Option.bind,hp]
  rfl

theorem fragment_loaded_frames (t r pc : Nat) (loc : Location) (value : α) (s : State α) :
    (fragmentLoaded t r pc loc value s).memory=s.memory ∧
      (fragmentLoaded t r pc loc value s).indices=s.indices ∧
        (fragmentLoaded t r pc loc value s).epochs=s.epochs := ⟨rfl,rfl,rfl⟩

theorem fragment_loaded_pc (t u r pc : Nat) (loc : Location) (value : α) (s : State α) :
    (fragmentLoaded t r pc loc value s).pc u=if u=t then pc else s.pc u := rfl

theorem fragment_loaded_regs (t u r q pc : Nat) (loc : Location) (value : α) (s : State α) :
    (fragmentLoaded t r pc loc value s).regs u q=if u=t ∧ q=r then some value else s.regs u q := rfl

theorem fragment_loaded_trace (t r pc : Nat) (loc : Location) (value : α) (s : State α) :
    (fragmentLoaded t r pc loc value s).trace=⟨t,loc,false,s.epochs t⟩::s.trace := rfl

def aLoadPC (p : Shape) (half e : Nat) : Nat := passPC p half+e
def bLoadPC (p : Shape) (half bank e : Nat) : Nat := passPC p half+4+5*bank+e

def aFragmentLoaded (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (tile t half e : Nat) (s : State α) : State α :=
  fragmentLoaded t (leftBase p half+e) (aLoadPC p half e+1)
    (sharedCell t 0 (aFragment (laneId t) half e)) (aOperand p ops input tile t half e) s

def bFragmentLoaded (p : Shape) (input : Nat → Nat → α) (tile t half bank e : Nat) (s : State α) : State α :=
  fragmentLoaded t (rightBase p half bank+e) (bLoadPC p half bank e+1)
    (sharedCell t 1 (bFragment p (laneId t) half bank e)) (bOperand p input tile t half bank e) s

theorem a_fragment_load_execute (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t half e : Nat) (s : State α) (hb : blockId t=b) (hh : half<2) (he : e<4)
    (hi : s.indices t 0=some ((laneId t : Nat) : Int)) (reads : TileReads p ops input tile b s)
    (hp : s.pc t=aLoadPC p half e) :
    execute ops (layout p) (geometry p) t
      (.assign (leftBase p half+e) (.load .shared 0 (aFragmentIndex half e))) s=
        some (aFragmentLoaded p ops input tile t half e s) :=
  execute_fragment_load_of p ops t 0 (leftBase p half+e) (aLoadPC p half e+1) (aFragmentIndex half e)
    ((aFragment (laneId t) half e : Nat) : Int) _ _ s
    (eval_a_fragment p t half e s hh he hi)
    (location_shared_a p t _ false (a_fragment_bound (laneId t) half e (lane_bound t) hh he))
    (a_operand_read p ops input tile b t half e s hb hh he reads) (by omega)

theorem b_fragment_load_execute (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t half bank e : Nat) (s : State α) (hb : blockId t=b) (hh : half<2) (hbank : bank<banks p) (he : e<4)
    (hi : s.indices t 0=some ((laneId t : Nat) : Int)) (reads : TileReads p ops input tile b s)
    (hp : s.pc t=bLoadPC p half bank e) :
    execute ops (layout p) (geometry p) t
      (.assign (rightBase p half bank+e) (.load .shared 1 (bFragmentIndex p half bank e))) s=
        some (bFragmentLoaded p input tile t half bank e s) :=
  execute_fragment_load_of p ops t 1 (rightBase p half bank+e) (bLoadPC p half bank e+1) (bFragmentIndex p half bank e)
    ((bFragment p (laneId t) half bank e : Nat) : Int) _ _ s
    (eval_b_fragment p t half bank e s hh hbank he hi)
    (location_shared_b p t _ false (b_fragment_bound p (laneId t) half bank e (lane_bound t) hh hbank he))
    (b_operand_read p ops input tile b t half bank e s hb hh hbank he reads) (by omega)

theorem a_fragment_load_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t half e extra : Nat) (s : State α) (hb : blockId t=b) (hh : half<2) (he : e<4)
    (hi : s.indices t 0=some ((laneId t : Nat) : Int)) (reads : TileReads p ops input tile b s)
    (hp : s.pc t=aLoadPC p half e) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (aFragmentLoaded p ops input tile t half e s) :=
  scalar_step p ops t (aLoadPC p half e) extra _ s _ (matrix_a_site p half e hh he) hp
    (a_fragment_load_execute p ops input tile b t half e s hb hh he hi reads hp)

theorem b_fragment_load_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b t half bank e extra : Nat) (s : State α) (hb : blockId t=b) (hh : half<2) (hbank : bank<banks p) (he : e<4)
    (hi : s.indices t 0=some ((laneId t : Nat) : Int)) (reads : TileReads p ops input tile b s)
    (hp : s.pc t=bLoadPC p half bank e) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (bFragmentLoaded p input tile t half bank e s) :=
  scalar_step p ops t (bLoadPC p half bank e) extra _ s _ (matrix_b_site p half bank e hh hbank he) hp
    (b_fragment_load_execute p ops input tile b t half bank e s hb hh hbank he hi reads hp)

#print axioms execute_fragment_load_of
#print axioms fragment_loaded_frames
#print axioms fragment_loaded_pc
#print axioms fragment_loaded_regs
#print axioms fragment_loaded_trace
#print axioms a_fragment_load_execute
#print axioms b_fragment_load_execute
#print axioms a_fragment_load_run
#print axioms b_fragment_load_run
end LarkNativeAwqGemm
