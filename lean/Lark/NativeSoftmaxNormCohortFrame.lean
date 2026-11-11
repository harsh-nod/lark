import Lark.NativeSoftmaxNormCohort

/-! Output, memory and exact access frames of the actual normalization lane
fold. Once an owned output is stored, later lanes leave it unchanged. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem norm_scalar_fold_output_other (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (offset : Nat) (s : State α) (hb : ∀ t ∈ ts, t/1024=row) (ho : writer offset ∉ ts) :
    (normScalarFold guarded ops input row ts s).memory (globalCell 0 offset)=s.memory (globalCell 0 offset) := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    have ht := hb t (by simp)
    have he : row*1024+t%1024=t := by omega
    exact (ih _ (by intro u hu; exact hb u (by simp [hu])) (by intro h; exact ho (by simp [h]))).trans
      (norm_lane_output_other_thread guarded ops input row (t%1024) offset s (Nat.mod_lt _ (by decide)) (by
        rewrite [he]; intro h; exact ho (List.mem_cons.mpr (Or.inl h))))

theorem norm_scalar_fold_output_member (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (hn : ts.Nodup) (hb : ∀ t ∈ ts, t/1024=row)
    (t iteration component : Nat) (ht : t ∈ ts) (hi : iteration<7) (hc : component<8)
    (hcol : column (t%1024) iteration component<50257) :
    (normScalarFold guarded ops input row ts s).memory (globalCell 0 (address row (column (t%1024) iteration component)))=
      some (normOutputValue ops input row (column (t%1024) iteration component)) := by
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
      exact (norm_scalar_fold_output_other guarded ops input row ts _ (normLaneStep guarded ops input row u s) hbs
        (by simpa only [ho] using hnot)).trans (norm_lane_outputs guarded ops input row (u%1024) s iteration hi component hc hcol)
    · exact ih _ htail hbs hm

theorem norm_scalar_fold_memory_frame (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) (l : Location) (hb : ∀ t ∈ ts, t/1024=row)
    (hprivate : ∀ t ∈ ts, l.space ≠ .local ∨ l.owner ≠ t ∨ l.buffer ≠ 1)
    (houtput : ∀ t ∈ ts, ∀ it, it<7 → ∀ c, c<8 → column (t%1024) it c<50257 →
      l ≠ globalCell 0 (address row (column (t%1024) it c))) :
    (normScalarFold guarded ops input row ts s).memory l=s.memory l := by
  induction ts generalizing s with
  | nil => rfl
  | cons t ts ih =>
    have ht := hb t (by simp)
    have he : row*1024+t%1024=t := by omega
    exact (ih _ (by intro u hu; exact hb u (by simp [hu])) (by intro u hu; exact hprivate u (by simp [hu]))
      (by intro u hu; exact houtput u (by simp [hu]))).trans
      (norm_lane_memory_frame guarded ops input row (t%1024) s l (by simpa only [he] using hprivate t (by simp))
        (houtput t (by simp)))

def normScalarAccesses (guarded : Bool) (ts : List Nat) : Nat :=
  (ts.map fun t => if guarded then (if t%1024<81 then 201 else 197) else (if t%1024<81 then 213 else 211)).sum

theorem norm_scalar_fold_trace_length (guarded : Bool) (ops : Ops α) (input : Nat → Nat → α)
    (row : Nat) (ts : List Nat) (s : State α) :
    (normScalarFold guarded ops input row ts s).trace.length=s.trace.length+normScalarAccesses guarded ts := by
  induction ts generalizing s with
  | nil => simp [normScalarFold,normScalarAccesses]
  | cons t ts ih =>
    change (normScalarFold guarded ops input row ts (normLaneStep guarded ops input row t s)).trace.length=_
    rewrite [ih]
    change (normLaneState guarded ops input row (t%1024) s).trace.length+normScalarAccesses guarded ts=_
    rewrite [norm_lane_trace_exact guarded ops input row (t%1024) s (Nat.mod_lt _ (by decide))]
    simp only [normScalarAccesses,List.map_cons,List.sum_cons]
    omega

#print axioms norm_scalar_fold_output_other
#print axioms norm_scalar_fold_output_member
#print axioms norm_scalar_fold_memory_frame
#print axioms norm_scalar_fold_trace_length
end LarkNativeSoftmax
