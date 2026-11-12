import Lark.NativeSglangRmsNormWaveRace

/-! Exact first-store access lists: every original lane writes, while the
repair records exactly the two logical leaders. Counts retain prior trace.
-/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
attribute [local irreducible] prefixFold reductionSnapshot partialFold

def partialAccess (epochs : Nat → Epoch) (t : Nat) : Access :=
  ⟨t,partialSlot t ((t%1024)/32),true,epochs t⟩

theorem partial_events_append (repaired : Bool) (epochs : Nat → Epoch) (xs ys : List Nat) :
    partialEvents repaired epochs (xs++ys)=partialEvents repaired epochs ys ++ partialEvents repaired epochs xs := by
  induction xs with
  | nil => simp [partialEvents]
  | cons t ts ih => simp only [List.cons_append,partialEvents,ih,List.append_assoc]

theorem fixed_prefix_events (epochs : Nat → Epoch) (row warp n : Nat) (hw : warp<16) (hn : n≤64) :
    partialEvents true epochs (cohortThreads row warp n)=
      if n=0 then [] else if n≤32 then [partialAccess epochs (cohortBase row warp)]
      else [partialAccess epochs (cohortBase row warp+32),partialAccess epochs (cohortBase row warp)] := by
  induction n with
  | zero => simp [cohortThreads,partialEvents]
  | succ n ih =>
      have hsplit : cohortThreads row warp (n+1)=cohortThreads row warp n ++ [cohortBase row warp+n] := by
        simp only [cohortThreads,List.range_succ,List.map_append,List.map_cons,List.map_nil]
      have hc := cohort_arithmetic row warp n hw (by omega)
      have hm : ((cohortBase row warp+n)%1024)%32=n%32 := by omega
      rw [hsplit,partial_events_append]
      simp only [partialEvents,List.nil_append]
      rw [hm]
      have ih := ih (by omega)
      by_cases hz : n=0
      · subst n
        simp [partialEvents,cohortThreads,partialAccess]
      by_cases h32 : n=32
      · subst n
        simp [ih,partialAccess]
      have hmod : n%32≠0 := by omega
      have guard : True ∧ n%32≠0 := ⟨True.intro,hmod⟩
      rw [if_pos guard,List.nil_append,ih]
      by_cases hsmall : n<32
      · simp only [if_neg hz,if_pos (show n≤32 by omega),
          if_neg (show n+1≠0 by omega),if_pos (show n+1≤32 by omega)]
      · simp only [if_neg hz,if_neg (show ¬n≤32 by omega),
          if_neg (show n+1≠0 by omega),if_neg (show ¬n+1≤32 by omega)]

theorem fixed_wave_events (epochs : Nat → Epoch) (row warp : Nat) (hw : warp<16) :
    partialEvents true epochs (cohortThreads row warp 64)=
      [partialAccess epochs (cohortBase row warp+32),partialAccess epochs (cohortBase row warp)] := by
  simpa only [show (64:Nat)≠0 by decide,show ¬(64:Nat)≤32 by decide,↓reduceIte] using
    fixed_prefix_events epochs row warp 64 hw (by decide)

theorem partial_access_location (epochs : Nat → Epoch) (row warp lane : Nat) (hw : warp<16) (hl : lane<64) :
    (partialAccess epochs (cohortBase row warp+lane)).location=⟨.shared,row,0,warp*2+lane/32⟩ := by
  have h := cohort_arithmetic row warp lane hw hl
  have hd : ((cohortBase row warp+lane)%1024)/32=warp*2+lane/32 := by omega
  simp only [partialAccess,partialSlot,h.1,hd]

theorem original_wave_partial_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) :
    (wavePartial p false ops input row warp s).trace.length=s.trace.length+5184 := by
  rw [wave_partial_trace,List.length_append,original_partial_events_length]
  have hp := prefix_fold_trace_length ops input (cohortThreads row warp 64) s
  have hc : (cohortThreads row warp 64).length=64 := by simp only [cohortThreads,List.length_map,List.length_range]
  change (cohortThreads row warp 64).length+(prefixFold ops input (cohortThreads row warp 64) s).trace.length=_
  rw [hp,hc]
  omega

theorem fixed_wave_partial_trace_length (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (row warp : Nat) (s : State α) (hw : warp<16) :
    (wavePartial p true ops input row warp s).trace.length=s.trace.length+5122 := by
  rw [wave_partial_trace,fixed_wave_events s.epochs row warp hw,List.length_append]
  have hp := prefix_fold_trace_length ops input (cohortThreads row warp 64) s
  have hc : (cohortThreads row warp 64).length=64 := by simp only [cohortThreads,List.length_map,List.length_range]
  change 2+(prefixFold ops input (cohortThreads row warp 64) s).trace.length=_
  rw [hp,hc]
  omega

#print axioms partial_events_append
#print axioms fixed_prefix_events
#print axioms fixed_wave_events
#print axioms partial_access_location
#print axioms original_wave_partial_trace_length
#print axioms fixed_wave_partial_trace_length
end LarkNativeSglangRmsNorm
