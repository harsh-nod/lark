import Lark.NativeAwqGemmOutputGrid

/-! Access classes sufficient for native AWQ race freedom. Later execution
lemmas discharge this classification for the actual initialized trace. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

inductive Good (p : Shape) (a : Access) : Prop where
  | input (space : a.location.space=.global) (buffer : a.location.buffer=0 ∨ a.location.buffer=1)
      (read : a.write=false)
  | output (space : a.location.space=.global) (buffer : a.location.buffer=2)
      (writer : a.thread=writer p a.location.offset) (write : a.write=true)
  | stagedA (space : a.location.space=.shared) (owner : a.location.owner=a.thread/64)
      (buffer : a.location.buffer=0) (writer : aWriter a.location=a.thread)
      (phase : a.epoch.block%2=1) (write : a.write=true)
  | stagedB (space : a.location.space=.shared) (owner : a.location.owner=a.thread/64)
      (buffer : a.location.buffer=1) (writer : (bKey p a.location).1=a.thread)
      (phase : a.epoch.block%2=1) (write : a.write=true)
  | operand (space : a.location.space=.shared) (owner : a.location.owner=a.thread/64)
      (phase : a.epoch.block%2=0) (read : a.write=false)

def GoodTrace (p : Shape) (s : State α) : Prop := ∀ a∈s.trace, Good p a

theorem trace_ordered_blocks (p : Shape) (a b : Access)
    (same : a.thread/64=b.thread/64) (epochs : a.epoch.block≠b.epoch.block) :
    ordered (geometry p) a b=true := by simp [ordered,geometry,same,epochs]

theorem good_collision (p : Shape) (a b : Access) (ha : Good p a) (hb : Good p b)
    (same : a.location=b.location) :
    a.thread=b.thread ∨ (a.write=false ∧ b.write=false) ∨ ordered (geometry p) a b=true := by
  have hs := congrArg Location.space same
  have ho := congrArg Location.owner same
  have hf := congrArg Location.buffer same
  have aw := congrArg aWriter same
  have bw := congrArg (fun loc => (bKey p loc).1) same
  have ow := congrArg (fun loc => writer p loc.offset) same
  cases ha <;> cases hb <;> simp_all
  all_goals first
    | omega
    | (right; apply trace_ordered_blocks p a b <;> omega)
    | (apply trace_ordered_blocks p a b <;> omega)

theorem trace_same_location (a b : Location) : sameLocation a b=true ↔ a=b := by
  cases a
  cases b
  simp [sameLocation,Bool.and_eq_true,Location.mk.injEq,and_assoc]

theorem good_conflict_false (p : Shape) (a b : Access) (ha : Good p a) (hb : Good p b) :
    conflict (geometry p) a b=false := by
  by_cases same : a.location=b.location
  · rcases good_collision p a b ha hb same with thread | reads | ordered
    · simp [conflict,thread]
    · simp [conflict,reads.1,reads.2]
    · simp [conflict,ordered]
  · have locations : sameLocation a.location b.location=false := by
      cases h : sameLocation a.location b.location
      · rfl
      · exact False.elim (same ((trace_same_location _ _).mp h))
    simp [conflict,locations]

theorem good_trace_race_free (p : Shape) (s : State α) (good : GoodTrace p s) :
    raceFree (geometry p) s.trace=true := by
  apply List.all_eq_true.mpr
  intro a ha
  apply List.all_eq_true.mpr
  intro b hb
  simp [good_conflict_false p a b (good a ha) (good b hb)]

theorem good_trace_of_trace (p : Shape) (s next : State α) (good : GoodTrace p s) (same : next.trace=s.trace) :
    GoodTrace p next := by
  intro a ha
  rw [same] at ha
  exact good a ha

theorem good_record (p : Shape) (s : State α) (t : Nat) (loc : Location) (write : Bool)
    (good : GoodTrace p s) (event : Good p ⟨t,loc,write,s.epochs t⟩) : GoodTrace p (record s t loc write) := by
  intro a ha
  rcases List.mem_cons.mp ha with same | member
  · subst a; exact event
  · exact good a member

theorem good_input_event (p : Shape) (t buffer offset : Nat) (epoch : Epoch) (hb : buffer=0 ∨ buffer=1) :
    Good p ⟨t,globalCell buffer offset,false,epoch⟩ := .input rfl hb rfl

theorem good_output_event (p : Shape) (t q : Nat) (epoch : Epoch) (hq : q<4*banks p) :
    Good p ⟨t,outCell p t q,true,epoch⟩ := .output rfl rfl (out_offset_writer p t q hq).symm rfl

theorem good_a_event (p : Shape) (t e : Nat) (epoch : Epoch) (he : e<8) (odd : epoch.block%2=1) :
    Good p ⟨t,aCell t e,true,epoch⟩ := .stagedA rfl rfl rfl (a_cell_writer t e he) odd rfl

theorem good_b_event (p : Shape) (t chunk e : Nat) (epoch : Epoch) (he : e<8) (odd : epoch.block%2=1) :
    Good p ⟨t,bCell p t chunk e,true,epoch⟩ :=
  .stagedB rfl rfl rfl (congrArg Prod.fst (b_cell_key p t chunk e he)) odd rfl

theorem good_operand_event (p : Shape) (t buffer offset : Nat) (epoch : Epoch) (even : epoch.block%2=0) :
    Good p ⟨t,sharedCell t buffer offset,false,epoch⟩ := .operand rfl rfl even rfl

theorem initial_good_trace (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α) :
    GoodTrace p (initial (layout p) input outside) := by
  intro a ha
  simp only [initial,List.not_mem_nil] at ha

#print axioms trace_ordered_blocks
#print axioms good_collision
#print axioms trace_same_location
#print axioms good_conflict_false
#print axioms good_trace_race_free
#print axioms good_trace_of_trace
#print axioms good_record
#print axioms good_input_event
#print axioms good_output_event
#print axioms good_a_event
#print axioms good_b_event
#print axioms good_operand_event
#print axioms initial_good_trace
end LarkNativeAwqGemm
