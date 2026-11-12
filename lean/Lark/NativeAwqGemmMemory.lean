import Lark.NativeAwqGemmInitialBlock

/-! Native AWQ memory operations retain every actual load/store trace event.
These helpers concern shared staging; no whole-kernel certificate is asserted. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def globalCell (buffer offset : Nat) : Location := ⟨.global,0,buffer,offset⟩
def sharedCell (t buffer offset : Nat) : Location := ⟨.shared,t/64,buffer,offset⟩

def Reads (p : Shape) (input : Nat → Nat → α) (s : State α) : Prop :=
  (∀ i, i<p.m*p.k → s.memory (globalCell 0 i)=some (input 0 i)) ∧
  (∀ i, i<p.k*p.n → s.memory (globalCell 1 i)=some (input 1 i))

theorem initial_reads (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α) :
    Reads p input (initial (layout p) input outside) := by
  constructor
  · intro i hi
    exact initial_places (layout p) input outside 0 i ⟨.input,p.m*p.k⟩ rfl rfl hi
  · intro i hi
    exact initial_places (layout p) input outside 1 i ⟨.input,p.k*p.n⟩ rfl rfl hi

theorem location_global_a (p : Shape) (t offset : Nat) (hi : offset<p.m*p.k) :
    location (layout p) (geometry p) t .global 0 (offset : Int) false=some (globalCell 0 offset) := by
  have h0 : ¬(offset : Int)<0 := by omega
  simp [location,layout,globalCell,h0,hi]

theorem location_shared_a (p : Shape) (t offset : Nat) (write : Bool) (hi : offset<640) :
    location (layout p) (geometry p) t .shared 0 (offset : Int) write=some (sharedCell t 0 offset) := by
  have h0 : ¬(offset : Int)<0 := by omega
  simp [location,layout,geometry,sharedCell,h0,hi]

theorem load_global_a (ops : Ops α) (p : Shape) (t offset : Nat) (s : State α)
    (input : Nat → Nat → α) (index : Index) (hi : offset<p.m*p.k) (reads : Reads p input s)
    (he : evalIndex (geometry p) t s index=some (offset : Int)) :
    evalExpr ops (layout p) (geometry p) t (.load .global 0 index) s=
      some (input 0 offset,record s t (globalCell 0 offset) false) := by
  simp only [evalExpr,he,location_global_a p t offset hi,reads.1 offset hi,bind,pure,Option.bind]

def written (s : State α) (t : Nat) (loc : Location) (value : α) (pc : Nat) : State α :=
  advance {record s t loc true with memory := fun l => if l=loc then some value else s.memory l} t pc

theorem execute_store_of (ops : Ops α) (p : Shape) (t buffer pc : Nat) (space : Space)
    (index : Index) (expression : Expr) (s evaluated : State α) (offset : Int) (loc : Location) (value : α)
    (hi : evalIndex (geometry p) t s index=some offset)
    (hl : location (layout p) (geometry p) t space buffer offset true=some loc)
    (he : evalExpr ops (layout p) (geometry p) t expression s=some (value,evaluated))
    (hp : s.pc t+1=pc) :
    execute ops (layout p) (geometry p) t (.store space buffer index expression) s=
      some (written evaluated t loc value pc) := by
  simp only [execute,hi,hl,he,hp,bind,pure,Option.bind]
  rfl

theorem written_trace (s : State α) (t : Nat) (loc : Location) (value : α) (pc : Nat) :
    (written s t loc value pc).trace=⟨t,loc,true,s.epochs t⟩::s.trace := rfl

theorem written_frames (s : State α) (t : Nat) (loc : Location) (value : α) (pc : Nat) :
    (written s t loc value pc).indices=s.indices ∧ (written s t loc value pc).regs=s.regs ∧
      (written s t loc value pc).epochs=s.epochs := ⟨rfl,rfl,rfl⟩

theorem record_reads (p : Shape) (input : Nat → Nat → α) (s : State α)
    (t : Nat) (loc : Location) (write : Bool) (h : Reads p input s) : Reads p input (record s t loc write) := h

theorem written_shared_reads (p : Shape) (input : Nat → Nat → α) (s : State α)
    (t pc : Nat) (loc : Location) (value : α) (hl : loc.space=.shared) (h : Reads p input s) :
    Reads p input (written s t loc value pc) := by
  constructor
  · intro i hi
    have different : globalCell 0 i≠loc := by
      intro same
      have impossible := congrArg Location.space same
      simp [globalCell,hl] at impossible
    simpa only [written,advance,record,if_neg different] using h.1 i hi
  · intro i hi
    have different : globalCell 1 i≠loc := by
      intro same
      have impossible := congrArg Location.space same
      simp [globalCell,hl] at impossible
    simpa only [written,advance,record,if_neg different] using h.2 i hi

theorem eval_int_lt_false (g : Geometry) (t : Nat) (s : State α) (a b : Index) (x y : Int)
    (ha : evalIndex g t s a=some x) (hb : evalIndex g t s b=some y) (hlt : ¬x<y) :
    evalPredicate g t s (.lt a b)=some false := by
  change (do
    let left ← evalIndex g t s a
    let right ← evalIndex g t s b
    pure (decide (left<right))) = _
  rw [ha,hb]
  simp [hlt]

theorem execute_branch_false (ops : Ops α) (p : Shape) (t target : Nat)
    (condition : Predicate) (s : State α) (he : evalPredicate (geometry p) t s condition=some false) :
    execute ops (layout p) (geometry p) t (.branch condition target) s=some (advance s t target) := by
  simp [execute,he]

theorem execute_jump (ops : Ops α) (p : Shape) (t target : Nat) (s : State α) :
    execute ops (layout p) (geometry p) t (.jump target) s=some (advance s t target) := rfl

def afterFirstBarrier (p : Shape) (ops : Ops α) (b : Nat) (s : State α) : State α :=
  resume (blockThreads (geometry p) b) .block (blockPrefix p ops b s)

theorem after_first_setup (p : Shape) (ops : Ops α) (b t : Nat) (s : State α)
    (ht : t∈blockThreads (geometry p) b) : SetupIndices p t (afterFirstBarrier p ops b s) :=
  setup_of_indices p t (blockPrefix p ops b s) _ (block_prefix_ready p ops b t s ht).setup rfl

theorem after_first_pc (p : Shape) (ops : Ops α) (b t : Nat) (s : State α)
    (ht : t∈blockThreads (geometry p) b) : (afterFirstBarrier p ops b s).pc t=firstBarrier p+1 := by
  have ready := block_prefix_ready p ops b t s ht
  simp only [afterFirstBarrier,resume,List.contains_iff_mem.mpr ht,ite_true,ready.pc]

theorem after_first_k (p : Shape) (ops : Ops α) (b t : Nat) (s : State α)
    (ht : t∈blockThreads (geometry p) b) : (afterFirstBarrier p ops b s).indices t 13=some 0 :=
  (block_prefix_ready p ops b t s ht).k

theorem after_first_reads (p : Shape) (ops : Ops α) (b : Nat) (s : State α)
    (input : Nat → Nat → α) (reads : Reads p input s) : Reads p input (afterFirstBarrier p ops b s) := by
  have memory := (block_prefix_frames p ops b s).1
  change Reads p input (blockPrefix p ops b s)
  unfold Reads
  rw [memory]
  exact reads

#print axioms initial_reads
#print axioms location_global_a
#print axioms location_shared_a
#print axioms load_global_a
#print axioms execute_store_of
#print axioms written_trace
#print axioms written_frames
#print axioms record_reads
#print axioms written_shared_reads
#print axioms eval_int_lt_false
#print axioms execute_branch_false
#print axioms execute_jump
#print axioms after_first_setup
#print axioms after_first_pc
#print axioms after_first_k
#print axioms after_first_reads
end LarkNativeAwqGemm
