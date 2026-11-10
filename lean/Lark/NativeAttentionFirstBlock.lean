import Lark.NativeAttentionFirstFold

/-! Actual native 32-thread/partial-wave64 scheduling through the first block
cut. Later barrier resumes and attention computation are not asserted here. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem block_mem (p : Shape) (b t : Nat) :
    t ∈ blockThreads (geometry p) b ↔ ∃ lane, lane < 32 ∧ t = b * 32 + lane := by
  constructor
  · intro ht
    obtain ⟨lane, hm, he⟩ := List.mem_map.mp ht
    exact ⟨lane, List.mem_range.mp hm, he.symm⟩
  · rintro ⟨lane, ht, rfl⟩
    exact List.mem_map.mpr ⟨lane, List.mem_range.mpr ht, rfl⟩

theorem block_nodup (p : Shape) (b : Nat) : (blockThreads (geometry p) b).Nodup := by
  unfold blockThreads
  apply List.pairwise_map.mpr
  exact List.Pairwise.imp (R := fun a b : Nat => a ≠ b) (by intro a b hab; omega) List.nodup_range

theorem block_nonempty (p : Shape) (b : Nat) : blockThreads (geometry p) b ≠ [] := by
  have hm : b * 32 ∈ blockThreads (geometry p) b := (block_mem p b _).mpr ⟨0, by decide, by omega⟩
  intro he
  rw [he] at hm
  cases hm

theorem native_warp_threads (p : Shape) (b : Nat) :
    warpThreads (geometry p) b 0 = blockThreads (geometry p) b := by
  have hf : (List.range 32).filter (fun t => t / 64 == 0) = List.range 32 := by
    apply List.filter_eq_self.mpr
    intro t ht
    have ht := List.mem_range.mp ht
    simp [Nat.div_eq_of_lt (by omega : t < 64)]
  simp only [warpThreads, blockThreads, geometry, hf]

theorem converged_block (ts : List Nat) (s : State α) (hne : ts ≠ [])
    (hp : ∀ t ∈ ts, s.pc t = 20) : converged program ts s = some .block := by
  cases ts with
  | nil => contradiction
  | cons t ts =>
      have ht := hp t (by simp)
      have hall : (t :: ts).all (fun u => s.pc u == s.pc t) = true := by
        apply List.all_eq_true.mpr
        intro u hu
        simp [hp u hu, ht]
      have hall' : (t :: ts).all (fun u => s.pc u == 20) = true := by simpa [ht] using hall
      simp only [converged, List.head?_cons, bind, pure, Option.bind, hall, ↓reduceIte,
        parked, ht, hall']
      rfl

def firstBlock (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) : State α :=
  firstFold ops input (blockThreads (geometry p) b) s

theorem first_block_epochs (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) :
    (firstBlock p ops input b s).epochs = s.epochs :=
  first_fold_epochs ops input (blockThreads (geometry p) b) s

theorem first_block_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat) (s : State α) :
    converged program (blockThreads (geometry p) b) (firstBlock p ops input b s) = some .block := by
  apply converged_block _ _ (block_nonempty p b)
  intro t ht
  exact (first_fold_member ops input _ t s (block_nodup p b) ht).1

theorem first_block_warp (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat)
    (s : State α) (hb : b < p.groups) (hr : Reads p input s)
    (hp : ∀ t ∈ blockThreads (geometry p) b, s.pc t = 0) :
    runWarp ops (layout p) (geometry p) fuel program (warpThreads (geometry p) b 0) fuel.warp s =
      some (firstBlock p ops input b s) := by
  have hf := first_fold_run p ops input (blockThreads (geometry p) b) s (block_nodup p b)
    (by intro t ht; obtain ⟨lane, hl, rfl⟩ := (block_mem p b t).mp ht; omega) hr hp
  rw [native_warp_threads]
  change runWarp ops (layout p) (geometry p) fuel program (blockThreads (geometry p) b) 1 s = _
  rw [runWarp, hf]
  simp only [bind, Option.some_bind]
  have hc := first_block_cut p ops input b s
  change converged program (blockThreads (geometry p) b)
    (firstFold ops input (blockThreads (geometry p) b) s) = some .block at hc
  rw [hc]
  rfl

theorem first_block_fold_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (b : Nat)
    (s : State α) (hb : b < p.groups) (hr : Reads p input s)
    (hp : ∀ t ∈ blockThreads (geometry p) b, s.pc t = 0) :
    (List.range (((geometry p).block + (geometry p).warp - 1) / (geometry p).warp)).foldlM
      (fun s w => runWarp ops (layout p) (geometry p) fuel program
        (warpThreads (geometry p) b w) fuel.warp s) s = some (firstBlock p ops input b s) := by
  have hcount : ((geometry p).block + (geometry p).warp - 1) / (geometry p).warp = 1 := by
    change (32 + 64 - 1) / 64 = 1
    decide
  rw [hcount, show List.range 1 = [0] by decide]
  rw [List.foldlM_cons, first_block_warp p ops input b s hb hr hp]
  rfl

theorem initial_reads (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α) :
    Reads p input (initial (layout p) input outside) := by
  intro b hb i hi
  rcases hb with rfl | rfl | rfl
  all_goals exact initial_places (layout p) input outside _ i ⟨.input, p.groups * 32768⟩ (by rfl) rfl hi

/-- Every input and outside memory: the actual first warp fold of runBlock
converges at the source's first barrier, with all native output zeros and first
K/V tile values, unchanged inputs, and a race-free actual prefix trace. -/
theorem first_block_from_initial (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (outside : Location → Option α) (b : Nat) (hb : b < p.groups) :
    ∃ final,
      (List.range (((geometry p).block + (geometry p).warp - 1) / (geometry p).warp)).foldlM
        (fun s w => runWarp ops (layout p) (geometry p) fuel program
          (warpThreads (geometry p) b w) fuel.warp s) (initial (layout p) input outside) = some final ∧
      converged program (blockThreads (geometry p) b) final = some .block ∧
      (∀ t ∈ blockThreads (geometry p) b, final.pc t = 20 ∧ NativeIndices t final) ∧
      (∀ t ∈ blockThreads (geometry p) b, ∀ tile, tile < 4 → ∀ col, col < 256 →
        final.memory (globalCell 0 (globalAddress t tile col)) = some (zeroValue ops)) ∧
      (∀ t ∈ blockThreads (geometry p) b, ∀ buffer, buffer = 1 ∨ buffer = 2 → ∀ col, col < 256 →
        final.memory (sharedCell t buffer (sharedAddress t col)) =
          some (ops.fromHalf (input (buffer + 1) (globalAddress t 0 col)))) ∧
      Reads p input final ∧ final.epochs = (initial (layout p) input outside).epochs ∧
      raceFree (geometry p) final.trace = true := by
  let start := initial (layout p) input outside
  have hr := initial_reads p input outside
  have hg : TraceGood (firstBlock p ops input b start) :=
    first_fold_good ops input (blockThreads (geometry p) b) start (by intro t ht; rfl)
      (by intro a ha; cases ha)
  refine ⟨firstBlock p ops input b start,
    first_block_fold_run p ops input b start hb hr (by intro t ht; rfl),
    first_block_cut p ops input b start, ?_, ?_, ?_,
    first_fold_reads p ops input _ start hr, first_fold_epochs ops input _ start, race_free p _ hg⟩
  · intro t ht
    exact first_fold_member ops input _ t start (block_nodup p b) ht
  · intro t ht tile hi col hc
    exact first_fold_output ops input _ t tile col start (block_nodup p b) ht hi hc
  · intro t ht buffer hbuffer col hc
    exact first_fold_tile ops input _ t buffer col start (block_nodup p b) ht hbuffer hc

#print axioms first_block_warp
#print axioms first_block_fold_run
#print axioms first_block_from_initial
end LarkNativeAttention
