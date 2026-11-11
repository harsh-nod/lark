import Lark.NativeSoftmaxSum

/-! Actual exponential output memory survives all later lanes, waves, partial
stores and the serial sum. Both input and output conversion operations remain
explicit. This supplies values to the later normalization proof. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def expOutputValue (ops : Ops α) (input : Nat → Nat → α) (row col : Nat) : α :=
  ops.toHalf (ops.exp (ops.sub (ops.fromHalf (input 1 (address row (clamped col)))) (rowMaximum ops input row)))

def ExpOutputRow (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s : State α) : Prop :=
  ∀ col, col<50257 → s.memory (globalCell 0 (address row col))=some (expOutputValue ops input row col)

theorem exp_scalar_fold_output_other (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (offset : Nat) (s : State α) (hb : ∀ t ∈ ts, t/1024=row)
    (ho : writer offset ∉ ts) :
    (expScalarFold ops input row ts s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    have hrow : row*1024+t%1024=t := by have h := hb t (by simp); omega
    have hn : writer offset ≠ t := by intro h; exact ho (List.mem_cons.mpr (Or.inl h))
    exact (ih (expLaneStep ops input row t s) (by intro u hu; exact hb u (by simp [hu]))
      (by intro h; exact ho (by simp [h]))).trans
      (exp_prefix_output_other_thread ops input row (t%1024) offset s (Nat.mod_lt _ (by decide))
        (by simpa only [hrow] using hn))

theorem exp_scalar_fold_output_member (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (hb : ∀ t ∈ ts, t/1024=row)
    (t iteration component : Nat) (ht : t ∈ ts) (hi : iteration<7) (hc : component<8)
    (hcol : column (t%1024) iteration component<50257) :
    (expScalarFold ops input row ts s).memory (globalCell 0 (address row (column (t%1024) iteration component)))=
      some (ops.toHalf (expComponentValue ops input (rowMaximum ops input row) row (t%1024) iteration component)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    have hbs : ∀ v ∈ ts, v/1024=row := by intro v hv; exact hb v (by simp [hv])
    rcases List.mem_cons.mp ht with he | hm
    · subst t
      have hrow : row*1024+u%1024=u := by have h := hb u (by simp); omega
      have ho : writer (address row (column (u%1024) iteration component))=u :=
        (address_writer row (u%1024) iteration component (Nat.mod_lt _ (by decide)) hcol).trans hrow
      exact (exp_scalar_fold_output_other ops input row ts _ (expLaneStep ops input row u s) hbs
        (by simpa only [ho] using hnot)).trans
        (exp_prefix_outputs ops input row (u%1024) s (Nat.mod_lt _ (by decide)) iteration hi component hc hcol)
    · exact ih (expLaneStep ops input row u s) htail hbs hm

theorem exp_wave_output_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp offset : Nat) (s : State α) (hw : warp<16) (ho : writer offset ∉ cohortThreads row warp 64) :
    (expWave p ops input row warp s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) :=
  (sum_last_wave_memory_frame p ops row warp (sumWaveValues ops input row warp 4)
    (sumStages p ops input row warp 0 4 (expScalarWave ops input row warp s)) _ (Or.inl rfl)).trans
    ((congrFun (sum_stages_preserves p ops input row warp 0 4 (expScalarWave ops input row warp s)).1 _).trans
      (exp_scalar_fold_output_other ops input row (cohortThreads row warp 64) offset s (exp_cohort_row row warp hw) ho))

theorem exp_wave_output_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp t iteration component : Nat) (s : State α) (hw : warp<16)
    (ht : t ∈ cohortThreads row warp 64) (hi : iteration<7) (hc : component<8)
    (hcol : column (t%1024) iteration component<50257) :
    (expWave p ops input row warp s).memory (globalCell 0 (address row (column (t%1024) iteration component)))=
      some (ops.toHalf (expComponentValue ops input (rowMaximum ops input row) row (t%1024) iteration component)) :=
  (sum_last_wave_memory_frame p ops row warp (sumWaveValues ops input row warp 4)
    (sumStages p ops input row warp 0 4 (expScalarWave ops input row warp s)) _ (Or.inl rfl)).trans
    ((congrFun (sum_stages_preserves p ops input row warp 0 4 (expScalarWave ops input row warp s)).1 _).trans
      (exp_scalar_fold_output_member ops input row (cohortThreads row warp 64) s (cohort_nodup row warp 64)
        (exp_cohort_row row warp hw) t iteration component ht hi hc hcol))

theorem exp_wave_fold_output_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (offset : Nat) (s : State α) (hb : ∀ w ∈ ws, w<16)
    (ho : ∀ w ∈ ws, writer offset ∉ cohortThreads row w 64) :
    (expWaveFold p ops input row ws s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  induction ws generalizing s with
  | nil => rfl
  | cons w ws ih =>
    exact (ih (expWave p ops input row w s) (by intro u hu; exact hb u (by simp [hu]))
      (by intro u hu; exact ho u (by simp [hu]))).trans
      (exp_wave_output_other p ops input row w offset s (hb w (by simp)) (ho w (by simp)))

theorem exp_wave_fold_output_member (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ws : List Nat) (s : State α) (hn : ws.Nodup) (hb : ∀ w ∈ ws, w<16)
    (warp t iteration component : Nat) (hw : warp ∈ ws) (ht : t ∈ cohortThreads row warp 64)
    (hi : iteration<7) (hc : component<8) (hcol : column (t%1024) iteration component<50257) :
    (expWaveFold p ops input row ws s).memory (globalCell 0 (address row (column (t%1024) iteration component)))=
      some (ops.toHalf (expComponentValue ops input (rowMaximum ops input row) row (t%1024) iteration component)) := by
  induction ws generalizing s with
  | nil => simp at hw
  | cons w ws ih =>
    obtain ⟨hnot,htail⟩ := List.nodup_cons.mp hn
    have hbs : ∀ v ∈ ws, v<16 := by intro v hv; exact hb v (by simp [hv])
    rcases List.mem_cons.mp hw with he | hm
    · subst warp
      have hrow : row*1024+t%1024=t := by have h := exp_cohort_row row w (hb w (by simp)) t ht; omega
      have ho : writer (address row (column (t%1024) iteration component))=t :=
        (address_writer row (t%1024) iteration component (Nat.mod_lt _ (by decide)) hcol).trans hrow
      exact (exp_wave_fold_output_other p ops input row ws _ (expWave p ops input row w s) hbs (by
        intro v hv
        rewrite [ho]
        exact cohorts_disjoint row w v t (by intro h; subst v; exact hnot hv) ht)).trans
        (exp_wave_output_value p ops input row w t iteration component s (hb w (by simp)) ht hi hc hcol)
    · exact ih (expWave p ops input row w s) htail hbs hm

theorem exp_block_output_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component : Nat) (s : State α) (ht : tid<1024) (hi : iteration<7) (hc : component<8)
    (hcol : column tid iteration component<50257) :
    (expBlock p ops input row s).memory (globalCell 0 (address row (column tid iteration component)))=
      some (ops.toHalf (expComponentValue ops input (rowMaximum ops input row) row tid iteration component)) := by
  have htmod : (row*1024+tid)%1024=tid := by omega
  have h := exp_wave_fold_output_member p ops input row (List.range 16) s List.nodup_range
    (fun _w hw => List.mem_range.mp hw) (tid/64) (row*1024+tid) iteration component
    (List.mem_range.mpr (by omega)) ((cohort_mem row (tid/64) 64 _).mpr
      ⟨tid%64,Nat.mod_lt _ (by decide),by unfold cohortBase; omega⟩)
    hi hc (by simpa only [htmod] using hcol)
  simpa only [htmod] using h

theorem exp_output_at_column (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration component col : Nat) (s : State α) (he : column tid iteration component=col)
    (hm : s.memory (globalCell 0 (address row (column tid iteration component)))=
      some (ops.toHalf (expComponentValue ops input (rowMaximum ops input row) row tid iteration component))) :
    s.memory (globalCell 0 (address row col))=some (expOutputValue ops input row col) := by
  simpa only [expOutputValue,expComponentValue,expInputValue,he] using hm

theorem exp_block_outputs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : ExpOutputRow ops input row (expBlock p ops input row s) := by
  intro col hc
  apply exp_output_at_column ops input row (col%1024) (col/1024/8) (col/1024%8) col (expBlock p ops input row s)
  · unfold column
    omega
  · apply exp_block_output_value p ops input row (col%1024) (col/1024/8) (col/1024%8) s
      (Nat.mod_lt _ (by decide)) (by omega) (Nat.mod_lt _ (by decide))
    unfold column
    omega

theorem exp_output_resume (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (cut : Cut) (s : State α) (outputs : ExpOutputRow ops input row s) :
    ExpOutputRow ops input row (resume ts cut s) := outputs

theorem after_exp_outputs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : ExpOutputRow ops input row (afterExp p ops input row s) :=
  exp_output_resume ops input row (blockThreads (geometry p) row) .block (expBlock p ops input row s)
    (exp_block_outputs p ops input row s)

theorem exp_row_outputs_frame (ops : Ops α) (input : Nat → Nat → α) (row : Nat) (s next : State α)
    (hm : ∀ col, col<50257 → next.memory (globalCell 0 (address row col))=s.memory (globalCell 0 (address row col)))
    (outputs : ExpOutputRow ops input row s) : ExpOutputRow ops input row next := by
  intro col hc
  exact (hm col hc).trans (outputs col hc)

theorem sum_state_outputs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (s : State α) : ExpOutputRow ops input row (sumState p ops input row s) :=
  exp_row_outputs_frame ops input row (afterExp p ops input row (maximumState p ops input row s))
    (sumState p ops input row s) (fun col _ => after_sum_output_frame p ops input row (address row col) _)
    (after_exp_outputs p ops input row (maximumState p ops input row s))

#print axioms exp_scalar_fold_output_other
#print axioms exp_scalar_fold_output_member
#print axioms exp_wave_output_other
#print axioms exp_wave_output_value
#print axioms exp_wave_fold_output_other
#print axioms exp_wave_fold_output_member
#print axioms exp_block_output_value
#print axioms exp_output_at_column
#print axioms exp_block_outputs
#print axioms exp_output_resume
#print axioms after_exp_outputs
#print axioms exp_row_outputs_frame
#print axioms sum_state_outputs
end LarkNativeSoftmax
