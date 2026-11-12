import Lark.NativeAwqGemmIndexEval

/-! Successful execution of all thirteen initial index assignments in the
complete native AWQ program, for every accepted shape and input state. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

theorem program_index_site (p : Shape) (i : Nat) (hi : i<13) :
    (program p)[i]?=(indexInstructions p)[i]? := by
  unfold program
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (l₁ := initialInstructions p) (i := i)
    (by rw [initial_length]; omega)]
  unfold initialInstructions
  simp only [List.append_assoc]
  exact List.getElem?_append_left (l₁ := indexInstructions p) (i := i)
    (by rw [index_instructions_length]; exact hi)

theorem output_index_site (p : Shape) (e : Nat) (he : e<4) :
    (program p)[9+e]?=some (ix (9+e)
      (.add (.add (.mul (v 4) (c 16)) (.mul (.div (v 0) (c 16)) (c 4))) (c e))) := by
  rw [program_index_site p (9+e) (by omega)]
  have cases : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl

theorem output_index_step (p : Shape) (ops : Ops α) (t e extra : Nat) (s : State α)
    (ht : t<(geometry p).grid*64) (he : e<4) (hp : s.pc t=9+e) (h : HeaderIndices p t s) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+1) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra
        (setIndex s t (9+e) ((globalOutputRow p t e : Nat) : Int) (10+e)) := by
  exact scalar_step p ops t (9+e) extra _ s _ (output_index_site p e he) hp
    (execute_index_of ops p t (9+e) (10+e) _ s _ (eval_output_row p t e s ht he h) (by omega))

def indexSetupState (p : Shape) (t : Nat) (s : State α) : State α :=
  let s := setIndex s t 6 ((inputRow p t : Nat) : Int) 7
  let s := setIndex s t 7 ((inputCol t : Nat) : Int) 8
  let s := setIndex s t 8 ((sharedABase t : Nat) : Int) 9
  let s := setIndex s t 9 ((globalOutputRow p t 0 : Nat) : Int) 10
  let s := setIndex s t 10 ((globalOutputRow p t 1 : Nat) : Int) 11
  let s := setIndex s t 11 ((globalOutputRow p t 2 : Nat) : Int) 12
  setIndex s t 12 ((globalOutputRow p t 3 : Nat) : Int) 13

def indicesState (p : Shape) (t : Nat) (s : State α) : State α :=
  indexSetupState p t (headerState p t s)

theorem index_setup_run (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (ht : t<(geometry p).grid*64) (hp : s.pc t=6) (h : HeaderIndices p t s) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+7) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (indexSetupState p t s) := by
  let s1 := setIndex s t 6 ((inputRow p t : Nat) : Int) 7
  let s2 := setIndex s1 t 7 ((inputCol t : Nat) : Int) 8
  let s3 := setIndex s2 t 8 ((sharedABase t : Nat) : Int) 9
  let s4 := setIndex s3 t 9 ((globalOutputRow p t 0 : Nat) : Int) 10
  let s5 := setIndex s4 t 10 ((globalOutputRow p t 1 : Nat) : Int) 11
  let s6 := setIndex s5 t 11 ((globalOutputRow p t 2 : Nat) : Int) 12
  let s7 := setIndex s6 t 12 ((globalOutputRow p t 3 : Nat) : Int) 13
  have h1 := setIndex_header p t 6 7 ((inputRow p t : Nat) : Int) s h (by decide)
  have h2 := setIndex_header p t 7 8 ((inputCol t : Nat) : Int) s1 h1 (by decide)
  have h3 := setIndex_header p t 8 9 ((sharedABase t : Nat) : Int) s2 h2 (by decide)
  have h4 := setIndex_header p t 9 10 ((globalOutputRow p t 0 : Nat) : Int) s3 h3 (by decide)
  have h5 := setIndex_header p t 10 11 ((globalOutputRow p t 1 : Nat) : Int) s4 h4 (by decide)
  have h6 := setIndex_header p t 11 12 ((globalOutputRow p t 2 : Nat) : Int) s5 h5 (by decide)
  have e1 := execute_index_of ops p t 6 7 _ s _ (eval_input_row p t s ht h) (by omega)
  have e2 := execute_index_of ops p t 7 8 _ s1 _ (eval_input_col p t s1 h1)
    (by simp [s1,setIndex,advance])
  have e3 := execute_index_of ops p t 8 9 _ s2 _ (eval_shared_a_base p t s2 h2
    (by simp [s2,setIndex,advance])) (by simp [s2,setIndex,advance])
  rewrite [show extra+7=(extra+6)+1 by omega,
    scalar_step p ops t 6 (extra+6) _ s s1 rfl hp e1]
  rewrite [show extra+6=(extra+5)+1 by omega,
    scalar_step p ops t 7 (extra+5) _ s1 s2 rfl (by simp [s1,setIndex,advance]) e2]
  rewrite [show extra+5=(extra+4)+1 by omega,
    scalar_step p ops t 8 (extra+4) _ s2 s3 rfl (by simp [s2,setIndex,advance]) e3]
  rewrite [show extra+4=(extra+3)+1 by omega,
    output_index_step p ops t 0 (extra+3) s3 ht (by decide) (by simp [s3,setIndex,advance]) h3]
  rewrite [show extra+3=(extra+2)+1 by omega,
    output_index_step p ops t 1 (extra+2) s4 ht (by decide) (by simp [s4,setIndex,advance]) h4]
  rewrite [show extra+2=(extra+1)+1 by omega,
    output_index_step p ops t 2 (extra+1) s5 ht (by decide) (by simp [s5,setIndex,advance]) h5]
  exact output_index_step p ops t 3 extra s6 ht (by decide) (by simp [s6,setIndex,advance]) h6

theorem initial_indices_run (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (ht : t<(geometry p).grid*64) (hp : s.pc t=0) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+13) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (indicesState p t s) := by
  rewrite [show extra+13=(extra+7)+6 by omega,header_run p ops t (extra+7) s ht hp]
  exact index_setup_run p ops t extra _ ht (header_pc p t s) (header_indices p t s)

structure SetupIndices (p : Shape) (t : Nat) (s : State α) : Prop where
  header : HeaderIndices p t s
  aRow : s.indices t 6=some ((inputRow p t : Nat) : Int)
  aCol : s.indices t 7=some ((inputCol t : Nat) : Int)
  aBase : s.indices t 8=some ((sharedABase t : Nat) : Int)
  outputRows : ∀ e, e<4 → s.indices t (9+e)=some ((globalOutputRow p t e : Nat) : Int)

theorem indices_ready (p : Shape) (t : Nat) (s : State α) : SetupIndices p t (indicesState p t s) := by
  have base : HeaderIndices p t (indicesState p t s) := by
    unfold indicesState indexSetupState
    apply setIndex_header p t 12 13 _ _ _ (by decide)
    apply setIndex_header p t 11 12 _ _ _ (by decide)
    apply setIndex_header p t 10 11 _ _ _ (by decide)
    apply setIndex_header p t 9 10 _ _ _ (by decide)
    apply setIndex_header p t 8 9 _ _ _ (by decide)
    apply setIndex_header p t 7 8 _ _ _ (by decide)
    exact setIndex_header p t 6 7 _ _ (header_indices p t s) (by decide)
  exact {
    header := base
    aRow := by simp [indicesState,indexSetupState,setIndex,advance]
    aCol := by simp [indicesState,indexSetupState,setIndex,advance]
    aBase := by simp [indicesState,indexSetupState,setIndex,advance]
    outputRows := by
      intro e he
      have cases : e=0 ∨ e=1 ∨ e=2 ∨ e=3 := by omega
      rcases cases with rfl | rfl | rfl | rfl <;>
        simp [indicesState,indexSetupState,setIndex,advance] }

theorem indices_pc (p : Shape) (t : Nat) (s : State α) : (indicesState p t s).pc t=13 := by
  simp [indicesState,indexSetupState,setIndex,advance]

theorem indices_frames (p : Shape) (t : Nat) (s : State α) :
    (indicesState p t s).memory=s.memory ∧ (indicesState p t s).trace=s.trace ∧
      (indicesState p t s).epochs=s.epochs ∧ (indicesState p t s).regs=s.regs :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem indices_other (p : Shape) (t u : Nat) (s : State α) (hu : u≠t) :
    (indicesState p t s).pc u=s.pc u ∧ (indicesState p t s).indices u=s.indices u := by
  constructor
  · simp [indicesState,indexSetupState,headerState,setIndex,advance,hu]
  · funext q
    simp [indicesState,indexSetupState,headerState,setIndex,advance,hu]

#print axioms program_index_site
#print axioms output_index_site
#print axioms output_index_step
#print axioms index_setup_run
#print axioms initial_indices_run
#print axioms indices_ready
#print axioms indices_pc
#print axioms indices_frames
#print axioms indices_other
end LarkNativeAwqGemm
