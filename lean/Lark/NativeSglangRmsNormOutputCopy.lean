import Lark.NativeSglangRmsNormScaleLoop

/-! One actual global-output copy cycle. The already converted private half
is copied raw, with one private read and one global write retained in the trace.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex execute_index_of)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem cached_output_at (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α)
    (hi : iteration<2) (hc : component<8) (cached : OutputPrefix ops input row tid 16 t inverse s) :
    s.memory (privateCell t 2 (iteration*8+component))=some (outputScaled ops input row tid iteration component inverse) := by
  have hd : (iteration*8+component)/8=iteration := by omega
  have hm : (iteration*8+component)%8=component := by omega
  simpa only [hd,hm] using cached (iteration*8+component) (by omega)

theorem eval_copy_column (p : Shape) (t tid iteration component : Nat) (s : State α)
    (ht : tid<1024) (hi : iteration<2) (hc : component<8)
    (h1 : s.indices t 1=some (tid : Int)) (h19 : s.indices t 19=some (iteration : Int))
    (h20 : s.indices t 20=some (component : Int)) :
    evalIndex (geometry p) t s (columnIndex 19 20)=some ((column tid iteration component : Nat) : Int) := by
  have hm := eval_nat_mul (geometry p) t iteration 1024 s (.ivar 19) h19 (by decide) (by omega)
  have ha := eval_nat_sum (geometry p) t (iteration*1024) tid s _ (.ivar 1) hm h1 (by omega)
  have hv := eval_nat_mul (geometry p) t (iteration*1024+tid) 8 s _ ha (by decide) (by omega)
  exact eval_nat_sum (geometry p) t ((iteration*1024+tid)*8) component s _ _ hv h20 (by omega)

theorem eval_copy_address (p : Shape) (t row col : Nat) (s : State α)
    (hr : row<p.rows) (hc : col<16384) (h0 : s.indices t 0=some (row : Int))
    (h21 : s.indices t 21=some (col : Int)) :
    evalIndex (geometry p) t s (.add (.mul (.ivar 0) (.const 16384)) (.ivar 21))=
      some ((address row col : Nat) : Int) := by
  have hb := p.bound
  have hm := eval_nat_mul (geometry p) t row 16384 s (.ivar 0) h0 (by decide) (by omega)
  exact eval_nat_sum (geometry p) t (row*16384) col s _ _ hm h21 (by omega)

theorem eval_copy_slot (p : Shape) (t iteration component : Nat) (s : State α)
    (hi : iteration<2) (hc : component<8) (h19 : s.indices t 19=some (iteration : Int))
    (h20 : s.indices t 20=some (component : Int)) :
    evalIndex (geometry p) t s (.add (.mul (.ivar 19) (.const 8)) (.ivar 20))=
      some ((iteration*8+component : Nat) : Int) := by
  have hm := eval_nat_mul (geometry p) t iteration 8 s (.ivar 19) h19 (by decide) (by omega)
  exact eval_nat_sum (geometry p) t (iteration*8) component s _ _ hm h20 (by omega)

def outputCopyAfter (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) : State α :=
  let col := column tid iteration component
  let offset := address row col
  let slot := iteration*8+component
  let s := advance s t 101
  let s := setIndex s t 21 (col : Int) 102
  let s := setIndex s t 22 (offset : Int) 103
  let s := setIndex s t 23 (slot : Int) 104
  let s := cacheWritten t 105 (globalCell 0 offset) (outputScaled ops input row tid iteration component inverse)
    (record s t (privateCell t 2 slot) false)
  let s := setIndex s t 20 ((component+1 : Nat) : Int) 106
  advance s t 100

theorem copy_output_half (p : Shape) (ops : Ops α) (t offset slot : Nat) (s : State α) (value : α)
    (ho : offset<p.rows*16384) (hs : slot<16) (h22 : s.indices t 22=some (offset : Int))
    (h23 : s.indices t 23=some (slot : Int)) (hm : s.memory (privateCell t 2 slot)=some value)
    (hp : s.pc t=104) :
    execute ops (layout p) (geometry p) t (.store .global 0 (.ivar 22) (.load .local 2 (.ivar 23))) s=
      some (cacheWritten t 105 (globalCell 0 offset) value (record s t (privateCell t 2 slot) false)) := by
  change s.memory ⟨.local,t,2,slot⟩=some value at hm
  simp only [execute,evalExpr,evalIndex,h22,h23,output_location p t offset true ho,
    private_location p t 2 slot false (by decide) hs,privateCell,hm,bind,pure,Option.bind]
  simp only [cacheWritten,privateCell,globalCell,record,advance,hp]

theorem output_copy_cycle (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t extra : Nat) (inverse : α) (s : State α)
    (hr : row<p.rows) (ht : tid<1024) (hi : iteration<2) (hc : component<8)
    (h0 : s.indices t 0=some (row : Int)) (h1 : s.indices t 1=some (tid : Int))
    (h19 : s.indices t 19=some (iteration : Int)) (h20 : s.indices t 20=some (component : Int))
    (hp : s.pc t=100) (cached : OutputPrefix ops input row tid 16 t inverse s) :
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t (extra+7) s=
    LarkCollective.runLane ops (layout p) (geometry p) (program true) t extra
      (outputCopyAfter ops input row tid iteration component t inverse s) := by
  let col := column tid iteration component
  let offset := address row col
  let slot := iteration*8+component
  let s1 := advance s t 101
  let s2 := setIndex s1 t 21 (col : Int) 102
  let s3 := setIndex s2 t 22 (offset : Int) 103
  let s4 := setIndex s3 t 23 (slot : Int) 104
  let s5 := cacheWritten t 105 (globalCell 0 offset) (outputScaled ops input row tid iteration component inverse)
    (record s4 t (privateCell t 2 slot) false)
  let s6 := setIndex s5 t 20 ((component+1 : Nat) : Int) 106
  have pred := LarkReduction.predicate_lt_of (geometry p) t s (.ivar 20) (.const 8)
    (component : Int) 8 h20 rfl (by omega)
  have e1 : execute ops (layout p) (geometry p) t (.branch (.lt (.ivar 20) (.const 8)) 107) s=some s1 := by
    simp [execute,pred,hp,s1]
  have he2 := eval_copy_column p t tid iteration component s1 ht hi hc h1 h19 h20
  have e2 := execute_index_of ops (layout p) (geometry p) t 21 102 (columnIndex 19 20) s1 _ he2 (by simp [s1,advance])
  have he3 := eval_copy_address p t row col s2 hr (column_bound tid iteration component ht hi hc)
    (by simpa [s2,s1,setIndex,advance] using h0) (by simp [s2,setIndex,advance])
  have e3 := execute_index_of ops (layout p) (geometry p) t 22 103
    (.add (.mul (.ivar 0) (.const 16384)) (.ivar 21)) s2 _ he3 (by simp [s2,setIndex,advance])
  have he4 := eval_copy_slot p t iteration component s3 hi hc
    (by simpa [s3,s2,s1,setIndex,advance] using h19) (by simpa [s3,s2,s1,setIndex,advance] using h20)
  have e4 := execute_index_of ops (layout p) (geometry p) t 23 104
    (.add (.mul (.ivar 19) (.const 8)) (.ivar 20)) s3 _ he4 (by simp [s3,setIndex,advance])
  have hm := cached_output_at ops input row tid iteration component t inverse s hi hc cached
  have e5 := copy_output_half p ops t offset slot s4 _ (address_bound p row tid iteration component hr ht hi hc)
    (by omega) (by simp [s4,s3,setIndex,advance]) (by simp [s4,setIndex,advance]) hm (by simp [s4,setIndex,advance])
  have idx : s5.indices t 20=some (component : Int) := by
    simp [s5,s4,s3,s2,s1,setIndex,cacheWritten,record,advance,h20]
  have plus := eval_nat_sum (geometry p) t component 1 s5 (.ivar 20) (.const 1) idx rfl (by omega)
  have e6 := execute_index_of ops (layout p) (geometry p) t 20 106 (.add (.ivar 20) (.const 1)) s5 _ plus
    (by simp [s5,cacheWritten,advance])
  have e7 : execute ops (layout p) (geometry p) t (.jump 100) s6=
      some (outputCopyAfter ops input row tid iteration component t inverse s) := rfl
  rw [scalar_step p true ops t 100 (extra+6) _ s s1 (by decide) hp e1]
  rw [scalar_step p true ops t 101 (extra+5) _ s1 s2 (by decide) (by simp [s1,advance]) e2]
  rw [scalar_step p true ops t 102 (extra+4) _ s2 s3 (by decide) (by simp [s2,setIndex,advance]) e3]
  rw [scalar_step p true ops t 103 (extra+3) _ s3 s4 (by decide) (by simp [s3,setIndex,advance]) e4]
  rw [scalar_step p true ops t 104 (extra+2) _ s4 s5 (by decide) (by simp [s4,setIndex,advance]) e5]
  rw [scalar_step p true ops t 105 (extra+1) _ s5 s6 (by decide) (by simp [s5,cacheWritten,advance]) e6]
  rw [scalar_step p true ops t 106 extra _ s6 _ (by decide) (by simp [s6,setIndex,advance]) e7]

theorem output_copy_fields (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) :
    (outputCopyAfter ops input row tid iteration component t inverse s).pc t=100 ∧
    (outputCopyAfter ops input row tid iteration component t inverse s).indices t 0=s.indices t 0 ∧
    (outputCopyAfter ops input row tid iteration component t inverse s).indices t 1=s.indices t 1 ∧
    (outputCopyAfter ops input row tid iteration component t inverse s).indices t 19=s.indices t 19 ∧
    (outputCopyAfter ops input row tid iteration component t inverse s).indices t 20=some ((component+1 : Nat) : Int) ∧
    (outputCopyAfter ops input row tid iteration component t inverse s).regs=s.regs ∧
    (outputCopyAfter ops input row tid iteration component t inverse s).epochs=s.epochs := by
  simp [outputCopyAfter,setIndex,cacheWritten,record,advance]

theorem output_copy_memory (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) (l : Location) :
    (outputCopyAfter ops input row tid iteration component t inverse s).memory l=
      if l=globalCell 0 (address row (column tid iteration component))
      then some (outputScaled ops input row tid iteration component inverse) else s.memory l := rfl

theorem output_copy_written (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) :
    (outputCopyAfter ops input row tid iteration component t inverse s).memory (globalCell 0 (address row (column tid iteration component)))=
      some (outputScaled ops input row tid iteration component inverse) := by simp only [output_copy_memory,↓reduceIte]

theorem output_copy_other (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t u : Nat) (inverse : α) (s : State α) (hu : u≠t) :
    (outputCopyAfter ops input row tid iteration component t inverse s).pc u=s.pc u ∧
    (outputCopyAfter ops input row tid iteration component t inverse s).indices u=s.indices u := by
  simp [outputCopyAfter,setIndex,cacheWritten,record,advance,hu]

theorem output_copy_trace (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α) :
    (outputCopyAfter ops input row tid iteration component t inverse s).trace=
      ⟨t,globalCell 0 (address row (column tid iteration component)),true,s.epochs t⟩::
      ⟨t,privateCell t 2 (iteration*8+component),false,s.epochs t⟩::s.trace := rfl

theorem output_copy_good (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component t : Nat) (inverse : α) (s : State α)
    (ht : tid<1024) (hi : iteration<2) (hc : component<8) (he : t=row*1024+tid)
    (good : ∀ event∈s.trace,Good event) :
    ∀ event∈(outputCopyAfter ops input row tid iteration component t inverse s).trace,Good event := by
  intro event hm
  rw [output_copy_trace] at hm
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Good.output rfl rfl rfl (he.trans (address_writer row tid iteration component ht hi hc).symm)
  rcases List.mem_cons.mp hm with rfl | hm
  · exact Good.localAccess rfl rfl
  · exact good event hm

#print axioms cached_output_at
#print axioms eval_copy_column
#print axioms eval_copy_address
#print axioms eval_copy_slot
#print axioms copy_output_half
#print axioms output_copy_cycle
#print axioms output_copy_fields
#print axioms output_copy_memory
#print axioms output_copy_written
#print axioms output_copy_other
#print axioms output_copy_trace
#print axioms output_copy_good
end LarkNativeSglangRmsNorm
