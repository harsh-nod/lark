import Lark.NativeAwqGemmState

/-! Execution of the source's native lane/logical-warp/block decode.
The conclusion uses runLane for the full source-bound program and every Shape.
It is an initial segment of the complete execution proof, not a certificate. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def headerState (p : Shape) (t : Nat) (s : State α) : State α :=
  let s := setIndex s t 0 ((t%64 : Nat) : Int) 1
  let s := setIndex s t 1 ((t%64%32 : Nat) : Int) 2
  let s := setIndex s t 2 ((t%64/32 : Nat) : Int) 3
  let s := setIndex s t 3 ((t/64 : Nat) : Int) 4
  let s := setIndex s t 4 ((t/64/columnTiles p : Nat) : Int) 5
  setIndex s t 5 ((t/64%columnTiles p : Nat) : Int) 6

theorem header_run (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (ht : t<(geometry p).grid*64) (hp : s.pc t=0) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+6) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (headerState p t s) := by
  let lane := t%64
  let block := t/64
  let columns := columnTiles p
  let s1 := setIndex s t 0 (lane : Int) 1
  let s2 := setIndex s1 t 1 ((lane%32 : Nat) : Int) 2
  let s3 := setIndex s2 t 2 ((lane/32 : Nat) : Int) 3
  let s4 := setIndex s3 t 3 (block : Int) 4
  let s5 := setIndex s4 t 4 ((block/columns : Nat) : Int) 5
  let s6 := setIndex s5 t 5 ((block%columns : Nat) : Int) 6
  have hl : lane<64 := Nat.mod_lt _ (by decide)
  have hb : block<2147483648 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self t 64) (thread_int32 p t ht)
  have hc : columns<2147483648 := by
    have h := column_threads_bound p
    have hn := (scalar_parameter_bounds p).2.2
    change columns*64≤p.n at h
    omega
  have hcp : 0<columns := column_tiles_positive p
  have e1 := execute_index_of ops p t 0 1 .tid s (lane : Int)
    (by change int32 (lane : Int)=_; exact int32_nat lane (by omega)) (by omega)
  have e2 := execute_index_of ops p t 1 2 (.mod (v 0) (c 32)) s1 ((lane%32 : Nat) : Int)
    (eval_nat_mod (geometry p) t lane 32 s1 (v 0)
      (by simp [v,evalIndex,s1,setIndex,advance]) (by decide) (by decide))
    (by simp [s1,setIndex,advance])
  have e3 := execute_index_of ops p t 2 3 (.div (v 0) (c 32)) s2 ((lane/32 : Nat) : Int)
    (eval_nat_div (geometry p) t lane 32 s2 (v 0)
      (by simp [v,evalIndex,s2,s1,setIndex,advance]) (by decide) (by decide))
    (by simp [s2,setIndex,advance])
  have e4 := execute_index_of ops p t 3 4 .bid s3 (block : Int)
    (by change int32 (block : Int)=_; exact int32_nat block hb)
    (by simp [s3,setIndex,advance])
  have e5 := execute_index_of ops p t 4 5 (.div (v 3) (c (columnTiles p))) s4 ((block/columns : Nat) : Int)
    (eval_nat_div (geometry p) t block columns s4 (v 3)
      (by simp [v,evalIndex,s4,setIndex,advance]) hcp hc)
    (by simp [s4,setIndex,advance])
  have e6 := execute_index_of ops p t 5 6 (.mod (v 3) (c (columnTiles p))) s5 ((block%columns : Nat) : Int)
    (eval_nat_mod (geometry p) t block columns s5 (v 3)
      (by simp [v,evalIndex,s5,s4,setIndex,advance]) hcp hc)
    (by simp [s5,setIndex,advance])
  rewrite [show extra+6=(extra+5)+1 by omega,
    scalar_step p ops t 0 (extra+5) _ s s1 rfl hp e1]
  rewrite [show extra+5=(extra+4)+1 by omega,
    scalar_step p ops t 1 (extra+4) _ s1 s2 rfl (by simp [s1,setIndex,advance]) e2]
  rewrite [show extra+4=(extra+3)+1 by omega,
    scalar_step p ops t 2 (extra+3) _ s2 s3 rfl (by simp [s2,setIndex,advance]) e3]
  rewrite [show extra+3=(extra+2)+1 by omega,
    scalar_step p ops t 3 (extra+2) _ s3 s4 rfl (by simp [s3,setIndex,advance]) e4]
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p ops t 4 (extra+1) _ s4 s5 rfl (by simp [s4,setIndex,advance]) e5]
  exact scalar_step p ops t 5 extra _ s5 s6 rfl (by simp [s5,setIndex,advance]) e6

theorem header_pc (p : Shape) (t : Nat) (s : State α) : (headerState p t s).pc t=6 := by
  simp [headerState,setIndex,advance]

theorem header_frames (p : Shape) (t : Nat) (s : State α) :
    (headerState p t s).memory=s.memory ∧ (headerState p t s).trace=s.trace ∧
      (headerState p t s).epochs=s.epochs ∧ (headerState p t s).regs=s.regs :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem header_other (p : Shape) (t u : Nat) (s : State α) (hu : u≠t) :
    (headerState p t s).pc u=s.pc u ∧ (headerState p t s).indices u=s.indices u := by
  constructor
  · simp [headerState,setIndex,advance,hu]
  · funext q
    simp [headerState,setIndex,advance,hu]

#print axioms header_run
#print axioms header_pc
#print axioms header_frames
#print axioms header_other
end LarkNativeAwqGemm
