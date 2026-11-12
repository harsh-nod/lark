import Lark.NativeAwqGemmIndices

/-! Induction over the actual source's sixteen/thirty-two accumulator writes.
The full instruction stream and its signed scalar model are unchanged. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

theorem zero_register_site (p : Shape) (r : Nat) (hr : r<4*banks p) :
    (program p)[13+r]?=some (put r (.lit 0 1)) := by
  unfold program
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (l₁ := initialInstructions p) (i := 13+r)
    (by rw [initial_length]; omega)]
  unfold initialInstructions
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (l₁ := indexInstructions p) (i := 13+r)
    (by rw [index_instructions_length]; omega)]
  rw [index_instructions_length,show 13+r-13=r by omega]
  rw [List.getElem?_append_left
    (l₁ := (List.range (4*banks p)).map (fun r => put r (.lit 0 1))) (i := r)
    (by simpa only [List.length_map,List.length_range] using hr)]
  rw [List.getElem?_map,List.getElem?_range hr]
  rfl

theorem initial_tail_site (p : Shape) (i : Nat) (hi : i<3) :
    (program p)[13+4*banks p+i]?=
      [ix 13 (c 0),branch (.lt (v 13) (c (p.k/32))) (outputPC p),blockBarrier][i]? := by
  unfold program
  simp only [List.append_assoc]
  rw [List.getElem?_append_left (l₁ := initialInstructions p) (i := 13+4*banks p+i)
    (by rw [initial_length]; omega)]
  unfold initialInstructions
  simp only [List.append_assoc]
  rw [List.getElem?_append_right (l₁ := indexInstructions p) (i := 13+4*banks p+i)
    (by rw [index_instructions_length]; omega)]
  rw [index_instructions_length,show 13+4*banks p+i-13=4*banks p+i by omega]
  rw [List.getElem?_append_right
    (l₁ := (List.range (4*banks p)).map (fun r => put r (.lit 0 1))) (i := 4*banks p+i)
    (by simp only [List.length_map,List.length_range]; omega)]
  simp only [List.length_map,List.length_range]
  rw [show 4*banks p+i-4*banks p=i by omega]

theorem k_counter_site (p : Shape) : (program p)[13+4*banks p]?=some (ix 13 (c 0)) :=
  initial_tail_site p 0 (by decide)

theorem initial_while_site (p : Shape) :
    (program p)[whilePC p]?=some (branch (.lt (v 13) (c (p.k/32))) (outputPC p)) := by
  rw [show whilePC p=13+4*banks p+1 by unfold whilePC; omega,initial_tail_site p 1 (by decide)]
  rfl

theorem first_barrier_site (p : Shape) : (program p)[firstBarrier p]?=some blockBarrier := by
  rw [show firstBarrier p=13+4*banks p+2 by unfold firstBarrier; omega,initial_tail_site p 2 (by decide)]
  rfl

def zeroed (ops : Ops α) (t : Nat) : Nat → State α → State α
  | 0,s => s
  | n+1,s => setReg (zeroed ops t n s) t n (ops.literal 0 1) (14+n)

theorem zeroed_pc (ops : Ops α) (t n : Nat) (s : State α) (hp : s.pc t=13) :
    (zeroed ops t n s).pc t=13+n := by
  cases n with
  | zero => exact hp
  | succ n => simp only [zeroed,setReg,advance,ite_true]; omega

theorem zeroed_run (p : Shape) (ops : Ops α) (t n extra : Nat) (s : State α)
    (hn : n≤4*banks p) (hp : s.pc t=13) :
    LarkMFMA.runLane ops (layout p) (geometry p) (program p) t (extra+n) s=
      LarkMFMA.runLane ops (layout p) (geometry p) (program p) t extra (zeroed ops t n s) := by
  induction n generalizing extra with
  | zero => rfl
  | succ n ih =>
    rewrite [show extra+(n+1)=(extra+1)+n by omega,ih (extra+1) (by omega)]
    have pc := zeroed_pc ops t n s hp
    have step := execute_pure_of ops p t n (14+n) (.lit 0 1) (zeroed ops t n s) (ops.literal 0 1)
      (by simp [evalExpr]) (by omega)
    exact scalar_step p ops t (13+n) extra _ _ _ (zero_register_site p n (by omega)) pc step

theorem zeroed_values (ops : Ops α) (t n r : Nat) (s : State α) (hr : r<n) :
    (zeroed ops t n s).regs t r=some (ops.literal 0 1) := by
  induction n generalizing r with
  | zero => omega
  | succ n ih =>
    by_cases same : r=n
    · subst r
      simp [zeroed,setReg,advance]
    · have old := ih r (by omega)
      simpa [zeroed,setReg,advance,same] using old

theorem zeroed_frames (ops : Ops α) (t n : Nat) (s : State α) :
    (zeroed ops t n s).memory=s.memory ∧ (zeroed ops t n s).trace=s.trace ∧
      (zeroed ops t n s).epochs=s.epochs ∧ (zeroed ops t n s).indices=s.indices := by
  induction n with
  | zero => exact ⟨rfl,rfl,rfl,rfl⟩
  | succ n ih => simpa only [zeroed,setReg,advance] using ih

theorem zeroed_other (ops : Ops α) (t n u : Nat) (s : State α) (hu : u≠t) :
    (zeroed ops t n s).pc u=s.pc u ∧ (zeroed ops t n s).regs u=s.regs u := by
  induction n with
  | zero => exact ⟨rfl,rfl⟩
  | succ n ih =>
    constructor
    · simpa [zeroed,setReg,advance,hu] using ih.1
    · funext r
      simpa [zeroed,setReg,advance,hu] using congrFun ih.2 r

theorem setup_of_thread_indices (p : Shape) (t : Nat) (s next : State α)
    (h : SetupIndices p t s) (hi : next.indices t=s.indices t) : SetupIndices p t next := by
  exact {
    header := {
      lane := by rw [hi]; exact h.header.lane
      logicalLane := by rw [hi]; exact h.header.logicalLane
      logicalWarp := by rw [hi]; exact h.header.logicalWarp
      block := by rw [hi]; exact h.header.block
      row := by rw [hi]; exact h.header.row
      column := by rw [hi]; exact h.header.column }
    aRow := by rw [hi]; exact h.aRow
    aCol := by rw [hi]; exact h.aCol
    aBase := by rw [hi]; exact h.aBase
    outputRows := by intro e he; rw [hi]; exact h.outputRows e he }

theorem setup_of_indices (p : Shape) (t : Nat) (s next : State α)
    (h : SetupIndices p t s) (hi : next.indices=s.indices) : SetupIndices p t next :=
  setup_of_thread_indices p t s next h (congrFun hi t)

theorem setIndex_setup (p : Shape) (t r pc : Nat) (value : Int) (s : State α)
    (h : SetupIndices p t s) (hr : 13≤r) : SetupIndices p t (setIndex s t r value pc) := by
  have h6 : (6 : Nat)≠r := by omega
  have h7 : (7 : Nat)≠r := by omega
  have h8 : (8 : Nat)≠r := by omega
  exact {
    header := setIndex_header p t r pc value s h.header (by omega)
    aRow := by simpa [setIndex,advance,h6] using h.aRow
    aCol := by simpa [setIndex,advance,h7] using h.aCol
    aBase := by simpa [setIndex,advance,h8] using h.aBase
    outputRows := by
      intro e he
      have different : 9+e≠r := by omega
      simpa [setIndex,advance,different] using h.outputRows e he }

#print axioms zero_register_site
#print axioms initial_tail_site
#print axioms k_counter_site
#print axioms initial_while_site
#print axioms first_barrier_site
#print axioms zeroed_pc
#print axioms zeroed_run
#print axioms zeroed_values
#print axioms zeroed_frames
#print axioms zeroed_other
#print axioms setup_of_indices
#print axioms setup_of_thread_indices
#print axioms setIndex_setup
end LarkNativeAwqGemm
