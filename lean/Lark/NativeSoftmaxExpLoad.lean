import Lark.NativeSoftmaxExpClamp

/-! One actual component of the exponentiation pass's private-buffer load.
The source's unclamped column, clamp, input conversion, private store and loop
controls all execute. The private store and input read are separate accesses. -/
namespace LarkNativeSoftmax
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def localCell (buffer t offset : Nat) : Location := ⟨.local,t,buffer,offset⟩

def expInputValue (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) : α :=
  ops.fromHalf (input 1 (address row (clamped (column tid iteration component))))

def expLoadCost (tid iteration component : Nat) : Nat :=
  6+clampCost (column tid iteration component)

def expLoadHead (row tid iteration component t : Nat) (s : State α) : State α :=
  let col := column tid iteration component
  let s := advance s t 49
  let s := setIndex s t 11 (col : Int) 50
  let s := expClampedState t col s
  setIndex s t 12 ((address row (clamped col) : Nat) : Int) 53

def expLoadStored (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) : State α :=
  written t 54 (localCell 0 t component) (expInputValue ops input row tid iteration component)
    (record s t (globalCell 1 (address row (clamped (column tid iteration component)))) false)

def expLoadAdvance (t component : Nat) (s : State α) : State α :=
  advance (setIndex s t 10 ((component+1 : Nat) : Int) 55) t 48

def expLoadTail (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) : State α :=
  expLoadAdvance t component (expLoadStored ops input row tid iteration component t s)

def expLoadAfter (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) : State α :=
  expLoadTail ops input row tid iteration component t (expLoadHead row tid iteration component t s)

theorem eval_exp_load_column (p : Shape) (t tid iteration component : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<7) (hc : component<8)
    (h9 : s.indices t 9=some ((base tid iteration : Nat) : Int))
    (h10 : s.indices t 10=some (component : Int)) :
    evalIndex (geometry p) t s (.add (.ivar 9) (.mul (.ivar 10) (.const 1024))) =
      some ((column tid iteration component : Nat) : Int) := by
  have hm := eval_nat_mul (geometry p) t component 1024 s (.ivar 10) h10 (by decide) (by omega)
  have hb : base tid iteration+component*1024<2147483648 := by unfold base; omega
  simpa only [column_expansion] using
    eval_nat_sum (geometry p) t (base tid iteration) (component*1024) s
      (.ivar 9) (.mul (.ivar 10) (.const 1024)) h9 hm hb

theorem eval_exp_load_address (p : Shape) (t row col : Nat) (s : State α)
    (hr : row<p.rows) (hc : col<50257)
    (h0 : s.indices t 0=some (row : Int)) (h11 : s.indices t 11=some (col : Int)) :
    evalIndex (geometry p) t s (.add (.mul (.ivar 0) (.const 50257)) (.ivar 11)) =
      some ((address row col : Nat) : Int) := by
  have hb := p.bound
  have hm := eval_nat_mul (geometry p) t row 50257 s (.ivar 0) h0 (by decide) (by omega)
  exact eval_nat_sum (geometry p) t (row*50257) col s _ _ hm h11 (by omega)

theorem exp_local_location (p : Shape) (t component : Nat) (hc : component<8) (write : Bool) :
    location (layout p) (geometry p) t .local 0 (component : Int) write=some (localCell 0 t component) := by
  simp [location,layout,localCell,show ¬ (component : Int)<0 by omega,hc]

theorem exp_load_head_fields (row tid iteration component t : Nat) (s : State α) :
    (expLoadHead row tid iteration component t s).pc t=53 ∧
    (expLoadHead row tid iteration component t s).indices t 12=
      some ((address row (clamped (column tid iteration component)) : Nat) : Int) ∧
    (expLoadHead row tid iteration component t s).indices t 10=s.indices t 10 ∧
    (expLoadHead row tid iteration component t s).memory=s.memory ∧
    (expLoadHead row tid iteration component t s).trace=s.trace ∧
    (expLoadHead row tid iteration component t s).epochs=s.epochs ∧
    (expLoadHead row tid iteration component t s).regs=s.regs := by
  by_cases hc : 50257≤column tid iteration component <;>
    simp [expLoadHead,expClampedState,hc,setIndex,advance]

theorem exp_load_head_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (row tid iteration component t extra : Nat) (s : State α)
    (hr : row<p.rows) (ht : tid<1024) (hi : iteration<7) (hc : component<8)
    (h0 : s.indices t 0=some (row : Int))
    (h9 : s.indices t 9=some ((base tid iteration : Nat) : Int))
    (h10 : s.indices t 10=some (component : Int)) (hp : s.pc t=48) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t
        (extra+3+clampCost (column tid iteration component)) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expLoadHead row tid iteration component t s) := by
  let col := column tid iteration component
  let s1 := advance s t 49
  let s2 := setIndex s1 t 11 (col : Int) 50
  let s3 := expClampedState t col s2
  have pred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 10) (.const 8)
    (component : Int) 8 h10 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 10) (.const 8)) 56) s=some s1 := by
    simp [execute,pred,hp,s1]
  have he2 := eval_exp_load_column p t tid iteration component s1 ht hi hc h9 h10
  have e2 := execute_index_of ops (layout p) (geometry p) t 11 50
    (.add (.ivar 9) (.mul (.ivar 10) (.const 1024))) s1 _ he2 (by simp [s1,advance])
  change execute _ _ _ _ _ s1=some s2 at e2
  have f3 := exp_clamped_fields t col s2 (by simp [s2,setIndex,advance])
  have h03 : s3.indices t 0=some (row : Int) := by
    change (expClampedState t col s2).indices t 0=_
    rewrite [exp_clamped_index_other t col 0 s2 (by decide)]
    simpa [s2,s1,setIndex,advance] using h0
  have he4 := eval_exp_load_address p t row (clamped col) s3 hr (clamped_bound col) h03 f3.2
  have e4 := execute_index_of ops (layout p) (geometry p) t 12 53
    (.add (.mul (.ivar 0) (.const 50257)) (.ivar 11)) s3 _ he4
    (by rewrite [show s3.pc t=52 from f3.1]; rfl)
  change execute _ _ _ _ _ s3=some (expLoadHead row tid iteration component t s) at e4
  rewrite [show extra+3+clampCost (column tid iteration component)=((extra+1)+clampCost col)+2 by
    dsimp only [col]; omega]
  rewrite [show ((extra+1)+clampCost col)+2=(((extra+1)+clampCost col)+1)+1 by omega,
    scalar_step p guarded ops t 48 _ _ s s1 (by cases guarded <;> rfl) hp e1]
  rewrite [scalar_step p guarded ops t 49 _ _ s1 s2 (by cases guarded <;> rfl) (by simp [s1,advance]) e2]
  rewrite [exp_clamp_eq p guarded ops t col (extra+1) s2 (by simp [s2,setIndex,advance])
    (by simp [s2,setIndex,advance])]
  rewrite [scalar_step p guarded ops t 52 _ _ s3 _ (by cases guarded <;> rfl) f3.1 e4]
  rfl

theorem execute_store_effect (ops : Ops α) (l : Layout) (g : Geometry) (t pc : Nat)
    (space : Space) (buffer : Nat) (ix : Index) (e : Expr) (s evaluated : State α)
    (index : Int) (cell : Location) (value : α)
    (hi : evalIndex g t s ix=some index)
    (hl : location l g t space buffer index true=some cell)
    (he : evalExpr ops l g t e s=some (value,evaluated))
    (hp : s.pc t+1=pc) :
    execute ops l g t (.store space buffer ix e) s=some (written t pc cell value evaluated) := by
  simp only [execute,hi,hl,he,hp,bind,pure,Option.bind]
  rfl

theorem converted_input_eval_of (ops : Ops α) (l : Layout) (g : Geometry)
    (t offset indexReg : Nat) (value : α) (s : State α)
    (hl : location l g t .global 1 (offset : Int) false=some (globalCell 1 offset))
    (hi : s.indices t indexReg=some (offset : Int))
    (hm : s.memory (globalCell 1 offset)=some value) :
    evalExpr ops l g t (.un .fromHalf (.load .global 1 (.ivar indexReg))) s =
      some (ops.fromHalf value,record s t (globalCell 1 offset) false) := by
  simp only [evalExpr,evalIndex,hi,hl,hm,applyUnary,bind,pure,Option.bind]

theorem exp_input_eval (p : Shape) (ops : Ops α) (t offset indexReg : Nat) (value : α) (s : State α)
    (hb : offset<p.rows*50257) (hi : s.indices t indexReg=some (offset : Int))
    (hm : s.memory (globalCell 1 offset)=some value) :
    evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .global 1 (.ivar indexReg))) s =
      some (ops.fromHalf value,record s t (globalCell 1 offset) false) := by
  exact converted_input_eval_of ops (layout p) (geometry p) t offset indexReg value s
    (input_location p t offset hb) hi hm

theorem exp_load_store_execute (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) (hc : component<8)
    (hb : address row (clamped (column tid iteration component))<p.rows*50257)
    (hp : s.pc t=53) (h10 : s.indices t 10=some (component : Int))
    (h12 : s.indices t 12=some ((address row (clamped (column tid iteration component)) : Nat) : Int))
    (hm : s.memory (globalCell 1 (address row (clamped (column tid iteration component))))=
      some (input 1 (address row (clamped (column tid iteration component))))) :
    execute ops (layout p) (geometry p) t
      (.store .local 0 (.ivar 10) (.un .fromHalf (.load .global 1 (.ivar 12)))) s=
      some (expLoadStored ops input row tid iteration component t s) := by
  have load : evalExpr ops (layout p) (geometry p) t (.un .fromHalf (.load .global 1 (.ivar 12))) s =
      some (expInputValue ops input row tid iteration component,
        record s t (globalCell 1 (address row (clamped (column tid iteration component)))) false) := by
    exact exp_input_eval p ops t _ 12 _ s hb h12 hm
  exact execute_store_effect ops (layout p) (geometry p) t 54 .local 0 (.ivar 10)
    (.un .fromHalf (.load .global 1 (.ivar 12))) s _ (component : Int) (localCell 0 t component) _
    h10 (exp_local_location p t component hc true) load (by omega)

theorem exp_load_store_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t extra : Nat) (s : State α) (hc : component<8)
    (hb : address row (clamped (column tid iteration component))<p.rows*50257)
    (hp : s.pc t=53) (h10 : s.indices t 10=some (component : Int))
    (h12 : s.indices t 12=some ((address row (clamped (column tid iteration component)) : Nat) : Int))
    (hm : s.memory (globalCell 1 (address row (clamped (column tid iteration component))))=
      some (input 1 (address row (clamped (column tid iteration component))))) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+1) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expLoadStored ops input row tid iteration component t s) :=
  scalar_step p guarded ops t 53 extra _ s _ (by cases guarded <;> rfl) hp
    (exp_load_store_execute p ops input row tid iteration component t s hc hb hp h10 h12 hm)

theorem exp_load_stored_controls (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) :
    (expLoadStored ops input row tid iteration component t s).pc t=54 ∧
    (expLoadStored ops input row tid iteration component t s).indices=s.indices := by
  simp [expLoadStored,written,record,advance]

theorem exp_load_advance_eq (p : Shape) (guarded : Bool) (ops : Ops α)
    (t component extra : Nat) (s : State α) (hc : component<8)
    (hp : s.pc t=54) (h10 : s.indices t 10=some (component : Int)) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+2) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expLoadAdvance t component s) := by
  let next := setIndex s t 10 ((component+1 : Nat) : Int) 55
  have ix := eval_nat_sum (geometry p) t component 1 s (.ivar 10) (.const 1) h10 rfl (by omega)
  have e1 := execute_index_of ops (layout p) (geometry p) t 10 55
    (.add (.ivar 10) (.const 1)) s _ ix (by omega)
  change execute _ _ _ _ _ s=some next at e1
  have e2 : execute ops (layout p) (geometry p) t (.jump 48) next=some (expLoadAdvance t component s) := rfl
  rewrite [show extra+2=(extra+1)+1 by omega,
    scalar_step p guarded ops t 54 _ _ s next (by cases guarded <;> rfl) hp e1]
  exact scalar_step p guarded ops t 55 extra _ next _ (by cases guarded <;> rfl)
    (by simp [next,setIndex,advance]) e2

theorem exp_load_tail_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t extra : Nat) (s : State α) (hc : component<8)
    (hb : address row (clamped (column tid iteration component))<p.rows*50257)
    (hp : s.pc t=53) (h10 : s.indices t 10=some (component : Int))
    (h12 : s.indices t 12=some ((address row (clamped (column tid iteration component)) : Nat) : Int))
    (hm : s.memory (globalCell 1 (address row (clamped (column tid iteration component))))=
      some (input 1 (address row (clamped (column tid iteration component))))) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t (extra+3) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expLoadTail ops input row tid iteration component t s) := by
  have controls := exp_load_stored_controls ops input row tid iteration component t s
  rewrite [show extra+3=(extra+2)+1 by omega,
    exp_load_store_eq p guarded ops input row tid iteration component t (extra+2) s hc hb hp h10 h12 hm]
  exact exp_load_advance_eq p guarded ops t component extra _ hc controls.1
    ((congrArg (fun indices => indices t 10) controls.2).trans h10)

theorem exp_load_eq (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t extra : Nat) (s : State α)
    (hr : row<p.rows) (ht : tid<1024) (hi : iteration<7) (hc : component<8)
    (h0 : s.indices t 0=some (row : Int))
    (h9 : s.indices t 9=some ((base tid iteration : Nat) : Int))
    (h10 : s.indices t 10=some (component : Int)) (hp : s.pc t=48) (reads : Reads p input s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t
        (extra+expLoadCost tid iteration component) s =
      LarkCollective.runLane ops (layout p) (geometry p) (program guarded) t extra
        (expLoadAfter ops input row tid iteration component t s) := by
  have fields := exp_load_head_fields row tid iteration component t s
  have hb := address_bound p row (clamped (column tid iteration component)) hr (clamped_bound _)
  have hm : (expLoadHead row tid iteration component t s).memory
      (globalCell 1 (address row (clamped (column tid iteration component))))=
        some (input 1 (address row (clamped (column tid iteration component)))) := by
    rewrite [fields.2.2.2.1]
    exact reads _ hb
  rewrite [show extra+expLoadCost tid iteration component=
    (extra+3)+3+clampCost (column tid iteration component) by unfold expLoadCost; omega]
  rewrite [exp_load_head_eq p guarded ops row tid iteration component t (extra+3) s hr ht hi hc h0 h9 h10 hp]
  exact exp_load_tail_eq p guarded ops input row tid iteration component t extra _ hc hb fields.1
    (fields.2.2.1.trans h10) fields.2.1 hm

theorem exp_load_fields (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) :
    (expLoadAfter ops input row tid iteration component t s).pc t=48 ∧
    (expLoadAfter ops input row tid iteration component t s).indices t 10=some ((component+1 : Nat) : Int) ∧
    (expLoadAfter ops input row tid iteration component t s).epochs=s.epochs ∧
    (expLoadAfter ops input row tid iteration component t s).regs=s.regs ∧
    (expLoadAfter ops input row tid iteration component t s).trace=
      ⟨t,localCell 0 t component,true,s.epochs t⟩::
      ⟨t,globalCell 1 (address row (clamped (column tid iteration component))),false,s.epochs t⟩::s.trace := by
  by_cases hc : 50257≤column tid iteration component <;>
    simp [expLoadAfter,expLoadHead,expLoadTail,expLoadStored,expLoadAdvance,expClampedState,hc,setIndex,written,record,advance]

theorem exp_load_value (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) :
    (expLoadAfter ops input row tid iteration component t s).memory (localCell 0 t component)=
      some (expInputValue ops input row tid iteration component) := by
  simp only [expLoadAfter,expLoadHead,expLoadTail,expLoadStored,expLoadAdvance,advance,setIndex,written_memory,ite_true]

theorem exp_load_memory_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) (l : Location) (hl : l ≠ localCell 0 t component) :
    (expLoadAfter ops input row tid iteration component t s).memory l=s.memory l := by
  simp only [expLoadAfter,expLoadHead,expLoadTail,expLoadStored,expLoadAdvance,advance,setIndex,written_memory,if_neg hl,record]
  exact congrArg (fun memory => memory l) (exp_clamped_preserves t _ _).1

theorem exp_load_index_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t r : Nat) (s : State α) (h10 : r ≠ 10) (h11 : r ≠ 11) (h12 : r ≠ 12) :
    (expLoadAfter ops input row tid iteration component t s).indices t r=s.indices t r := by
  by_cases hc : 50257≤column tid iteration component <;>
    simp [expLoadAfter,expLoadHead,expLoadTail,expLoadStored,expLoadAdvance,expClampedState,hc,setIndex,written,record,advance,h10,h11,h12]

theorem exp_load_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α) (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (expLoadAfter ops input row tid iteration component t s).trace, Good a := by
  intro a ha
  rewrite [(exp_load_fields ops input row tid iteration component t s).2.2.2.2] at ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact Good.privateAccess rfl rfl
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact Good.input rfl rfl rfl rfl
    · exact good a ha

structure ExpLoadReady (p : Shape) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (offset acc : α) (s : State α) : Prop where
  pc : s.pc t=48
  rowIndex : s.indices t 0=some (row : Int)
  tidIndex : s.indices t 1=some (tid : Int)
  baseIndex : s.indices t 9=some ((base tid iteration : Nat) : Int)
  componentIndex : s.indices t 10=some (component : Int)
  maximum : s.regs t 5=some offset
  accumulator : s.regs t 6=some acc
  reads : Reads p input s
  good : ∀ a ∈ s.trace, Good a

def ExpBuffered (ops : Ops α) (input : Nat → Nat → α) (row tid iteration t upto : Nat) (s : State α) : Prop :=
  ∀ component, component<upto → s.memory (localCell 0 t component)=some (expInputValue ops input row tid iteration component)

theorem exp_load_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (offset acc : α) (s : State α)
    (ready : ExpLoadReady p input row tid iteration component t offset acc s) :
    ExpLoadReady p input row tid iteration (component+1) t offset acc
      (expLoadAfter ops input row tid iteration component t s) := by
  obtain ⟨hp,h10,_,hreg,_⟩ := exp_load_fields ops input row tid iteration component t s
  exact {
    pc := hp
    rowIndex := (exp_load_index_other ops input row tid iteration component t 0 s
      (by decide) (by decide) (by decide)).trans ready.rowIndex
    tidIndex := (exp_load_index_other ops input row tid iteration component t 1 s
      (by decide) (by decide) (by decide)).trans ready.tidIndex
    baseIndex := (exp_load_index_other ops input row tid iteration component t 9 s
      (by decide) (by decide) (by decide)).trans ready.baseIndex
    componentIndex := h10
    maximum := (congrArg (fun regs => regs t 5) hreg).trans ready.maximum
    accumulator := (congrArg (fun regs => regs t 6) hreg).trans ready.accumulator
    reads := by
      intro i hb
      rewrite [exp_load_memory_other ops input row tid iteration component t s _ (by
        intro h; have hs := congrArg Location.space h; simp [globalCell,localCell] at hs)]
      exact ready.reads i hb
    good := exp_load_good ops input row tid iteration component t s ready.good }

theorem exp_load_buffered (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (s : State α)
    (buffered : ExpBuffered ops input row tid iteration t component s) :
    ExpBuffered ops input row tid iteration t (component+1)
      (expLoadAfter ops input row tid iteration component t s) := by
  intro slot hs
  by_cases he : slot=component
  · subst slot; exact exp_load_value ops input row tid iteration component t s
  · rewrite [exp_load_memory_other ops input row tid iteration component t s _ (by
      intro h; have ho := congrArg Location.offset h; exact he ho)]
    exact buffered slot (by omega)

#print axioms eval_exp_load_column
#print axioms eval_exp_load_address
#print axioms exp_local_location
#print axioms exp_load_head_fields
#print axioms exp_load_head_eq
#print axioms execute_store_effect
#print axioms converted_input_eval_of
#print axioms exp_input_eval
#print axioms exp_load_store_execute
#print axioms exp_load_store_eq
#print axioms exp_load_stored_controls
#print axioms exp_load_advance_eq
#print axioms exp_load_tail_eq
#print axioms exp_load_eq
#print axioms exp_load_fields
#print axioms exp_load_value
#print axioms exp_load_memory_other
#print axioms exp_load_index_other
#print axioms exp_load_good
#print axioms exp_load_ready
#print axioms exp_load_buffered
end LarkNativeSoftmax
