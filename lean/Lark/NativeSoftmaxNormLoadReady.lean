import Lark.NativeSoftmaxNormLoadFrame

/-! Normalization-buffer invariants for actual component execution. Only valid
columns have a value obligation: the original source's unused clamp reads may
observe a cell already normalized by another lane. Race-freedom is proved here
only for the repaired read path. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

structure NormLoadReady (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) : Prop where
  valid : row<p.rows
  bound : tid<1024
  pc : s.pc (row*1024+tid)=97
  native : MaxNativeIndices (row*1024+tid) s
  base : s.indices (row*1024+tid) 17=some ((base tid iteration : Nat) : Int)
  componentIndex : s.indices (row*1024+tid) 18=some (component : Int)
  denominator : s.regs (row*1024+tid) 12=some (rowExpSum ops input row)
  epoch : (s.epochs (row*1024+tid)).block=4
  future : NormFuture ops input row tid iteration s
  present : NormPresent row s

def NormBuffered (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration upto : Nat) (s : State α) : Prop :=
  ∀ component, component<upto → column tid iteration component<50257 →
    s.memory (localCell 1 (row*1024+tid) component)=
      some (ops.fromHalf (expOutputValue ops input row (column tid iteration component)))

theorem norm_buffered_empty (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration : Nat) (s : State α) : NormBuffered ops input row tid iteration 0 s := by
  intro component hc
  omega

theorem norm_load_component_ready (p : Shape) (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α)
    (ready : NormLoadReady p ops input row tid iteration component s) :
    NormLoadReady p ops input row tid iteration (component+1)
      (normLoadState guarded ops row tid iteration component (row*1024+tid) s) := by
  have fields := norm_load_component_fields guarded ops row tid iteration component (row*1024+tid) s
  exact {
    valid := ready.valid
    bound := ready.bound
    pc := fields.1
    native := norm_load_component_native guarded ops row tid iteration component (row*1024+tid) s ready.native
    base := (norm_load_component_index_other guarded ops row tid iteration component (row*1024+tid) 17 s
      (by decide) (by decide) (by decide)).trans ready.base
    componentIndex := fields.2
    denominator := (congrArg (fun regs => regs (row*1024+tid) 12)
      (norm_load_component_regs guarded ops row tid iteration component (row*1024+tid) s)).trans ready.denominator
    epoch := (congrArg (fun epochs => (epochs (row*1024+tid)).block)
      (norm_load_component_epochs guarded ops row tid iteration component (row*1024+tid) s)).trans ready.epoch
    future := norm_load_component_future guarded ops input row tid iteration component (row*1024+tid) iteration s ready.future
    present := norm_load_component_present guarded ops row tid iteration component (row*1024+tid) s ready.present }

theorem norm_load_component_buffered (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (hi : iteration<7) (hc : component<8)
    (future : NormFuture ops input row tid iteration s)
    (buffered : NormBuffered ops input row tid iteration component s) :
    NormBuffered ops input row tid iteration (component+1)
      (normLoadState guarded ops row tid iteration component (row*1024+tid) s) := by
  intro slot hs hcol
  by_cases he : slot=component
  · subst slot
    exact norm_load_component_input_value guarded ops input row tid iteration component (row*1024+tid) s hi hc hcol future
  · rewrite [norm_load_component_memory_other guarded ops row tid iteration component (row*1024+tid) s _ (by
      intro h
      exact he (congrArg Location.offset h))]
    exact buffered slot (by omega) hcol

theorem norm_load_component_fixed_good (ops : Ops α)
    (row tid iteration component : Nat) (s : State α) (ht : tid<1024)
    (good : ∀ a ∈ s.trace, Good a) :
    ∀ a ∈ (normLoadState true ops row tid iteration component (row*1024+tid) s).trace, Good a := by
  apply norm_load_component_good true ops row tid iteration component (row*1024+tid) s ?_ good
  intro hl
  have hc : column tid iteration component<50257 := by simpa using hl
  rewrite [norm_selected_column_valid true _ hc]
  exact Good.output rfl rfl rfl (address_writer row tid iteration component ht hc).symm

#print axioms norm_buffered_empty
#print axioms norm_load_component_ready
#print axioms norm_load_component_buffered
#print axioms norm_load_component_fixed_good
end LarkNativeSoftmax
