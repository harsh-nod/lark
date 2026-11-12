import Lark.NativeSglangRmsNormPartialEvents

/-! Shared values left by guarded logical leaders. These frame lemmas support
the following complete-block fold; they use the exact source-ordered sums.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
open LarkReduction (setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold

theorem last_partial_written_value (repaired : Bool) (ops : Ops α) (t : Nat)
    (a b : α) (s : State α) (write : repaired=false ∨ (t%1024)%32=0) :
    (lastPartial repaired ops t a b s).memory (partialSlot t ((t%1024)/32))=some (ops.add a b) := by
  cases repaired with
  | false => simp [lastPartial,partialTail,partialWrite,addAfter,setReg,advance,record]
  | true =>
      have hz : (t%1024)%32=0 := by simpa using write
      simp only [lastPartial,partialTail,↓reduceIte,if_pos hz,partialWrite,addAfter,setReg,advance,record]

theorem fixed_nonleader_memory (ops : Ops α) (t : Nat) (a b : α) (s : State α)
    (hn : (t%1024)%32≠0) : (lastPartial true ops t a b s).memory=s.memory := by
  simp only [lastPartial,partialTail,↓reduceIte,if_neg hn]
  rfl

theorem partial_fold_cons (repaired : Bool) (ops : Ops α) (a b : Nat → α) (t : Nat)
    (ts : List Nat) (s : State α) :
    partialFold repaired ops a b (t::ts) s=partialFold repaired ops a b ts (lastPartial repaired ops t (a t) (b t) s) := by
  simp only [partialFold,List.foldl_cons]

theorem fixed_fold_memory_unchanged (ops : Ops α) (a b : Nat → α) (ts : List Nat)
    (s : State α) (l : Location)
    (outside : ∀ t∈ts,(t%1024)%32=0 → l≠partialSlot t ((t%1024)/32)) :
    (partialFold true ops a b ts s).memory l=s.memory l := by
  induction ts generalizing s with
  | nil => simp only [partialFold,List.foldl_nil]
  | cons t ts ih =>
      have h := ih (lastPartial true ops t (a t) (b t) s) (fun u hu => outside u (by simp [hu]))
      rw [partial_fold_cons]
      rw [h]
      by_cases hz : (t%1024)%32=0
      · exact last_partial_memory true ops t (a t) (b t) s l (outside t (by simp) hz)
      · rw [fixed_nonleader_memory ops t (a t) (b t) s hz]

theorem fixed_fold_written_value (ops : Ops α) (a b : Nat → α) (ts : List Nat) (s : State α)
    (hn : ts.Nodup) (t : Nat) (ht : t∈ts) (leader : (t%1024)%32=0)
    (unique : ∀ u∈ts,u≠t → (u%1024)%32=0 → partialSlot u ((u%1024)/32)≠partialSlot t ((t%1024)/32)) :
    (partialFold true ops a b ts s).memory (partialSlot t ((t%1024)/32))=some (ops.add (a t) (b t)) := by
  induction ts generalizing s with
  | nil => simp at ht
  | cons u ts ih =>
      obtain ⟨hnot,hnodup⟩ := List.nodup_cons.mp hn
      rw [partial_fold_cons]
      rcases List.mem_cons.mp ht with he | hm
      · subst t
        have hf := fixed_fold_memory_unchanged ops a b ts (lastPartial true ops u (a u) (b u) s)
          (partialSlot u ((u%1024)/32)) (by
            intro v hv hlead
            apply Ne.symm
            apply unique v (by simp [hv]) _ hlead
            intro he; subst v; exact hnot hv)
        exact hf.trans (last_partial_written_value true ops u (a u) (b u) s (Or.inr leader))
      · exact ih (lastPartial true ops u (a u) (b u) s) hnodup hm
          (fun v hv => unique v (by simp [hv]))

theorem fixed_wave_partial_shared_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp lane : Nat) (s : State α) (hw : warp<16) (hl : lane<64) (leader : lane%32=0) :
    (wavePartial p true ops input row warp s).memory ⟨.shared,row,0,warp*2+lane/32⟩=
      some (reductionValues ops (waveBaseValues ops input row warp) 5 lane) := by
  let t := cohortBase row warp+lane
  have ht := (cohort_mem row warp 64 t).mpr ⟨lane,hl,rfl⟩
  have coords := cohort_arithmetic row warp lane hw hl
  have hlead : (t%1024)%32=0 := by dsimp only [t]; omega
  have unique : ∀ u∈cohortThreads row warp 64,u≠t → (u%1024)%32=0 →
      partialSlot u ((u%1024)/32)≠partialSlot t ((t%1024)/32) := by
    intro u hu hne hu0 he
    obtain ⟨other,ho,rfl⟩ := (cohort_mem row warp 64 u).mp hu
    have hc := cohort_arithmetic row warp other hw ho
    have hs := congrArg Location.offset he
    change ((cohortBase row warp+other)%1024)/32=(t%1024)/32 at hs
    dsimp only [t] at hs hne
    omega
  have h := fixed_fold_written_value ops (wavePartialA p ops input row warp) (wavePartialB p ops input row warp)
    (cohortThreads row warp 64) (waveLastSnapshot p ops input row warp s) (cohort_nodup row warp 64) t ht hlead unique
  have hloc : partialSlot t ((t%1024)/32)=⟨.shared,row,0,warp*2+lane/32⟩ :=
    partial_access_location (fun _ => {}) row warp lane hw hl
  rw [hloc] at h
  simpa only [t,wavePartial,wavePartialA,wavePartialB,(cohort_coords p row warp lane hw hl).2,
    reductionValues,reductionMask] using h

#print axioms last_partial_written_value
#print axioms fixed_nonleader_memory
#print axioms partial_fold_cons
#print axioms fixed_fold_memory_unchanged
#print axioms fixed_fold_written_value
#print axioms fixed_wave_partial_shared_value
end LarkNativeSglangRmsNorm
