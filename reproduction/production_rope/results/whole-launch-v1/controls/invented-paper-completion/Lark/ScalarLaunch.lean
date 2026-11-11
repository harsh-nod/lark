import Lark.Nonlinear

/-!
The actual lane/warp/block/grid folds for a launch whose lanes independently
finish at one halt. A kernel supplies a proved lane simulation and invariant;
this library composes them over every thread, including partial final warps.
It does not assume race freedom, output correctness, or the lane simulation.
-/
namespace LarkScalarLaunch
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def fuel (lane : Nat) : Fuel := ⟨lane, 1, 1, 1⟩

def DonePreserved (halt : Nat) (before after : State α) : Prop :=
  ∀ t, before.pc t = halt → after.pc t = halt

theorem fold_progress (xs : List ι) (step : State α → ι → Option (State α))
    (post : State α → ι → State α) (targets : ι → List Nat)
    (I : State α → Prop) (halt : Nat) (s : State α) (hs : I s)
    (contract : ∀ k ∈ xs, ∀ st, I st →
      step st k = some (post st k) ∧ I (post st k) ∧
      (∀ t ∈ targets k, (post st k).pc t = halt) ∧
      DonePreserved halt st (post st k)) :
    xs.foldlM step s = some (xs.foldl post s) ∧ I (xs.foldl post s) ∧
    (∀ k ∈ xs, ∀ t ∈ targets k, (xs.foldl post s).pc t = halt) ∧
    DonePreserved halt s (xs.foldl post s) := by
  induction xs generalizing s with
  | nil => exact ⟨rfl, hs, by simp, by intro t ht; exact ht⟩
  | cons k ks ih =>
    obtain ⟨he, hi, hd, hm⟩ := contract k (by simp) s hs
    have tail := ih (post s k) hi (by
      intro j hj st hst
      exact contract j (by simp [hj]) st hst)
    refine ⟨?_, tail.2.1, ?_, ?_⟩
    · simpa only [List.foldlM_cons, he, Option.some_bind, List.foldl_cons] using tail.1
    · intro j hj t ht
      rcases List.mem_cons.mp hj with rfl | hj
      · exact tail.2.2.2 t (hd t ht)
      · exact tail.2.2.1 j hj t ht
    · intro t ht
      exact tail.2.2.2 t (hm t ht)

theorem converged_halt (p : List Instr) (halt : Nat) (ts : List Nat) (s : State α)
    (stop : p[halt]? = some .halt) (hne : ts ≠ [])
    (done : ∀ t ∈ ts, s.pc t = halt) : converged p ts s = some .halt := by
  cases ts with
  | nil => contradiction
  | cons t ts =>
    have ht := done t (by simp)
    have hall : (t :: ts).all (fun u => s.pc u == s.pc t) = true := by
      apply List.all_eq_true.mpr
      intro u hu
      simp [done u hu, ht]
    have hall' : (t :: ts).all (fun u => s.pc u == halt) = true := by simpa [ht] using hall
    simp only [converged, List.head?_cons, bind, pure, Option.bind, hall, ↓reduceIte,
      parked, ht, stop, hall']

theorem warpCount_member (block width j : Nat) (hw : 0 < width) (hj : j < block) :
    j / width < (block + width - 1) / width := by
  have hmul := Nat.div_mul_le_self j width
  have hle : (j / width + 1) * width ≤ block + width - 1 := by
    simp only [Nat.add_mul, Nat.one_mul]
    omega
  have hq := (Nat.le_div_iff_mul_le hw).mpr hle
  omega

theorem warpStart_bound (block width w : Nat) (hw : 0 < width)
    (hh : w < (block + width - 1) / width) : w * width < block := by
  have hle : w + 1 ≤ (block + width - 1) / width := by omega
  have hm := (Nat.le_div_iff_mul_le hw).mp hle
  simp only [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem warpThreads_ne (g : Geometry) (b w : Nat) (hw : 0 < g.warp)
    (hh : w < (g.block + g.warp - 1) / g.warp) : warpThreads g b w ≠ [] := by
  have hb := warpStart_bound g.block g.warp w hw hh
  have hm : b * g.block + w * g.warp ∈ warpThreads g b w := by
    apply List.mem_map.mpr
    refine ⟨w * g.warp, ?_, rfl⟩
    apply List.mem_filter.mpr
    exact ⟨List.mem_range.mpr hb, by simp [Nat.mul_div_cancel w hw]⟩
  intro he
  simp [he] at hm

theorem blockThreads_ne (g : Geometry) (b : Nat) (hb : 0 < g.block) :
    blockThreads g b ≠ [] := by
  have hm : b * g.block + 0 ∈ blockThreads g b := by
    exact List.mem_map.mpr ⟨0, List.mem_range.mpr hb, rfl⟩
  intro he
  simp [he] at hm

theorem warpThreads_subset (g : Geometry) (b w t : Nat)
    (ht : t ∈ warpThreads g b w) : t ∈ blockThreads g b := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  exact List.mem_map.mpr ⟨j, (List.mem_filter.mp hj).1, rfl⟩

theorem blockThreads_bound (g : Geometry) (b t : Nat) (hb : b < g.grid)
    (ht : t ∈ blockThreads g b) : t < g.grid * g.block := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  have hj' := List.mem_range.mp hj
  have hm := Nat.mul_le_mul_right g.block (show b + 1 ≤ g.grid by omega)
  simp only [Nat.add_mul, Nat.one_mul] at hm
  omega

theorem blockThreads_covered (g : Geometry) (b t : Nat) (hw : 0 < g.warp)
    (ht : t ∈ blockThreads g b) :
    ∃ w ∈ List.range ((g.block + g.warp - 1) / g.warp), t ∈ warpThreads g b w := by
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp ht
  refine ⟨j / g.warp, List.mem_range.mpr (warpCount_member _ _ _ hw (List.mem_range.mp hj)), ?_⟩
  apply List.mem_map.mpr
  exact ⟨j, List.mem_filter.mpr ⟨hj, by simp⟩, rfl⟩

theorem launchThreads_covered (g : Geometry) (t : Nat) (hb : 0 < g.block)
    (ht : t < g.grid * g.block) :
    ∃ b ∈ List.range g.grid, t ∈ blockThreads g b := by
  have hd : t / g.block < g.grid := (Nat.div_lt_iff_lt_mul hb).mpr ht
  refine ⟨t / g.block, List.mem_range.mpr hd, ?_⟩
  apply List.mem_map.mpr
  refine ⟨t % g.block, List.mem_range.mpr (Nat.mod_lt t hb), ?_⟩
  simpa [Nat.mul_comm] using Nat.div_add_mod t g.block

def LaneContract (ops : Ops α) (l : Layout) (g : Geometry) (lane halt : Nat)
    (p : List Instr) (post : State α → Nat → State α) (I : State α → Prop) : Prop :=
  ∀ s, I s → ∀ t, t < g.grid * g.block →
    runLane ops l g p t lane s = some (post s t) ∧ I (post s t) ∧
    (post s t).pc t = halt ∧ DonePreserved halt s (post s t)

def warpPost (g : Geometry) (post : State α → Nat → State α) (b w : Nat)
    (s : State α) : State α := (warpThreads g b w).foldl post s
def blockPost (g : Geometry) (post : State α → Nat → State α) (b : Nat)
    (s : State α) : State α :=
  (List.range ((g.block + g.warp - 1) / g.warp)).foldl
    (fun s w => warpPost g post b w s) s
def launchPost (g : Geometry) (post : State α → Nat → State α) (s : State α) : State α :=
  (List.range g.grid).foldl (fun s b => blockPost g post b s) s

theorem warp_simulation (ops : Ops α) (l : Layout) (g : Geometry) (lane halt : Nat)
    (p : List Instr) (post : State α → Nat → State α) (I : State α → Prop)
    (stop : p[halt]? = some .halt) (contract : LaneContract ops l g lane halt p post I)
    (s : State α) (hs : I s) (ts : List Nat) (hne : ts ≠ [])
    (bound : ∀ t ∈ ts, t < g.grid * g.block) :
    runWarp ops l g (fuel lane) p ts 1 s = some (ts.foldl post s) ∧
    I (ts.foldl post s) ∧ (∀ t ∈ ts, (ts.foldl post s).pc t = halt) ∧
    DonePreserved halt s (ts.foldl post s) := by
  have hf := fold_progress ts (fun s t => runLane ops l g p t lane s) post
    (fun t => [t]) I halt s hs (by
      intro t ht st hst
      obtain ⟨he, hi, hd, hm⟩ := contract st hst t (bound t ht)
      exact ⟨he, hi, by simpa using hd, hm⟩)
  have hd : ∀ t ∈ ts, (ts.foldl post s).pc t = halt := by
    intro t ht
    exact hf.2.2.1 t ht t (by simp)
  refine ⟨?_, hf.2.1, hd, hf.2.2.2⟩
  simp only [runWarp, fuel, hf.1, bind, pure, Option.bind,
    converged_halt p halt ts _ stop hne hd]
  rfl

theorem block_simulation (ops : Ops α) (l : Layout) (g : Geometry) (lane halt : Nat)
    (p : List Instr) (post : State α → Nat → State α) (I : State α → Prop)
    (stop : p[halt]? = some .halt) (contract : LaneContract ops l g lane halt p post I)
    (hbpos : 0 < g.block) (hw : 0 < g.warp) (b : Nat) (hb : b < g.grid)
    (s : State α) (hs : I s) :
    runBlock ops l g (fuel lane) p b 1 s = some (blockPost g post b s) ∧
    I (blockPost g post b s) ∧ (∀ t ∈ blockThreads g b, (blockPost g post b s).pc t = halt) ∧
    DonePreserved halt s (blockPost g post b s) := by
  have hf := fold_progress (List.range ((g.block + g.warp - 1) / g.warp))
    (fun s w => runWarp ops l g (fuel lane) p (warpThreads g b w) 1 s)
    (fun s w => warpPost g post b w s) (warpThreads g b) I halt s hs (by
      intro w hw' st hst
      exact warp_simulation ops l g lane halt p post I stop contract st hst
        (warpThreads g b w) (warpThreads_ne g b w hw (List.mem_range.mp hw'))
        (by intro t ht; exact blockThreads_bound g b t hb (warpThreads_subset g b w t ht)))
  have hd : ∀ t ∈ blockThreads g b, (blockPost g post b s).pc t = halt := by
    intro t ht
    obtain ⟨w, hw', hwt⟩ := blockThreads_covered g b t hw ht
    exact hf.2.2.1 w hw' t hwt
  refine ⟨?_, hf.2.1, hd, hf.2.2.2⟩
  have he : (List.range ((g.block + g.warp - 1) / g.warp)).foldlM
      (fun s w => runWarp ops l g (fuel lane) p (warpThreads g b w) 1 s) s =
      some (blockPost g post b s) := hf.1
  simp only [fuel] at he
  simp only [runBlock, fuel, he, bind, pure, Option.bind,
    converged_halt p halt (blockThreads g b) _ stop (blockThreads_ne g b hbpos) hd]
  rfl

theorem launch_simulation (ops : Ops α) (l : Layout) (g : Geometry) (lane halt : Nat)
    (p : List Instr) (post : State α → Nat → State α) (I : State α → Prop)
    (stop : p[halt]? = some .halt) (contract : LaneContract ops l g lane halt p post I)
    (hg : 0 < g.grid) (hb : 0 < g.block) (hw : 0 < g.warp)
    (s : State α) (hs : I s) :
    runLaunch ops l g (fuel lane) p s = some (launchPost g post s) ∧
    I (launchPost g post s) ∧ (∀ t, t < g.grid * g.block → (launchPost g post s).pc t = halt) := by
  have hf := fold_progress (List.range g.grid)
    (fun s b => runBlock ops l g (fuel lane) p b 1 s)
    (fun s b => blockPost g post b s) (blockThreads g) I halt s hs (by
      intro b hb' st hst
      exact block_simulation ops l g lane halt p post I stop contract hb hw b
        (List.mem_range.mp hb') st hst)
  have hd : ∀ t, t < g.grid * g.block → (launchPost g post s).pc t = halt := by
    intro t ht
    obtain ⟨b, hb', hbt⟩ := launchThreads_covered g t hb ht
    exact hf.2.2.1 b hb' t hbt
  have hne : List.range (g.grid * g.block) ≠ [] := by
    intro he
    have hh := congrArg List.length he
    simp at hh
    have := Nat.mul_pos hg hb
    omega
  refine ⟨?_, hf.2.1, hd⟩
  have he : (List.range g.grid).foldlM
      (fun s b => runBlock ops l g (fuel lane) p b 1 s) s =
      some (launchPost g post s) := hf.1
  simp only [fuel] at he
  simp only [runLaunch, show g.grid ≠ 0 by omega, show g.block ≠ 0 by omega,
    show g.warp ≠ 0 by omega, false_or, ↓reduceIte, fuel, runGrid, he,
    bind, pure, Option.bind,
    converged_halt p halt (List.range (g.grid * g.block)) _ stop hne
      (by intro t ht; exact hd t (List.mem_range.mp ht))]
  rfl

#print axioms launch_simulation
end LarkScalarLaunch
