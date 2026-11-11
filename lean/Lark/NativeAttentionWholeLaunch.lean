import Lark.NativeAttentionGridFold

/-! Actual native grid launch and all outputs of the source-ordered recurrence. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 1000
set_option maxHeartbeats 2000000

def gridState (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) : State α :=
  fullBlocks p ops input (List.range p.groups) s
theorem grid_state (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (s : State α) :
    gridState p ops input s = fullBlocks p ops input (List.range p.groups) s := rfl

theorem initial_grid_ready (p : Shape) (input : Nat → Nat → α) (outside : Location → Option α) :
    ∀ b ∈ List.range p.groups, GridBlockReady p b (initial (layout p) input outside) := by
  intro b hb
  exact ⟨List.mem_range.mp hb, (by intro t ht; rfl), (by intro t ht; rfl)⟩

theorem grid_reads_good (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    Reads p input (gridState p ops input (initial (layout p) input outside)) ∧
    TraceGood (gridState p ops input (initial (layout p) input outside)) :=
  Eq.mpr (congrArg (fun state : State α => Reads p input state ∧ TraceGood state)
    (grid_state p ops input (initial (layout p) input outside)))
    (full_blocks_reads_good p ops input (List.range p.groups) (initial (layout p) input outside) List.nodup_range
      (initial_reads p input outside) (by intro a ha; cases ha) (initial_grid_ready p input outside))

theorem grid_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (t : Nat) (ht : t < p.groups * 32) : (gridState p ops input (initial (layout p) input outside)).pc t = 90 := by
  have hb : t / 32 < p.groups := by omega
  have hm : t ∈ blockThreads (geometry p) (t / 32) :=
    (block_mem p (t / 32) t).mpr ⟨t % 32, Nat.mod_lt _ (by decide), by omega⟩
  exact (congrArg (fun state : State α => state.pc t) (grid_state p ops input (initial (layout p) input outside))).trans
    (full_blocks_pc p ops input (List.range p.groups) (t / 32) t (initial (layout p) input outside)
      List.nodup_range (initial_reads p input outside) (by intro a ha; cases ha) (initial_grid_ready p input outside) (List.mem_range.mpr hb) hm)

theorem grid_cut (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    converged program (List.range ((geometry p).grid * (geometry p).block)) (gridState p ops input (initial (layout p) input outside)) = some .halt := by
  have positive := p.positive
  apply converged_halt
  · intro he
    have hm : 0 ∈ List.range ((geometry p).grid * (geometry p).block) := List.mem_range.mpr (by change 0 < p.groups * 32; omega)
    rw [he] at hm
    cases hm
  · intro t ht
    exact grid_pc p ops input outside t (List.mem_range.mp ht)

theorem grid_run (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    runLaunch ops (layout p) (geometry p) fuel program (initial (layout p) input outside) =
      some (gridState p ops input (initial (layout p) input outside)) := by
  have valid : ¬((geometry p).grid = 0 ∨ (geometry p).block = 0 ∨ (geometry p).warp = 0) := by
    change ¬(p.groups = 0 ∨ 32 = 0 ∨ 64 = 0)
    have positive := p.positive
    omega
  have hfold : (List.range (geometry p).grid).foldlM
      (fun s b => runBlock ops (layout p) (geometry p) fuel program b fuel.block s) (initial (layout p) input outside) =
        some (gridState p ops input (initial (layout p) input outside)) :=
    (full_blocks_run p ops input (List.range p.groups) (initial (layout p) input outside) List.nodup_range
      (initial_reads p input outside) (by intro a ha; cases ha) (initial_grid_ready p input outside)).trans
      (congrArg some (grid_state p ops input (initial (layout p) input outside)).symm)
  rw [runLaunch, if_neg valid]
  change runGrid ops (layout p) (geometry p) fuel program 1 (initial (layout p) input outside) = _
  rw [runGrid, hfold]
  simp only [bind, Option.some_bind]
  rw [grid_cut p ops input outside]
  rfl

def outputValue (ops : Ops α) (input : Nat → Nat → α) (offset : Nat) : α :=
  (onlineValues ops input 4 (writer offset) (offset / 8192 % 4)).stored (offset % 256)
def sourceSpec (p : Shape) (ops : Ops α) (input : Nat → Nat → α) : List α :=
  (List.range (p.groups * 32768)).map (outputValue ops input)

theorem grid_value (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α)
    (offset : Nat) (hi : offset < p.groups * 32768) :
    (gridState p ops input (initial (layout p) input outside)).memory (globalCell 0 offset) = some (outputValue ops input offset) := by
  have ht := writer_bound p offset hi
  have hb : writer offset / 32 < p.groups := by omega
  have hm : writer offset ∈ blockThreads (geometry p) (writer offset / 32) :=
    (block_mem p _ _).mpr ⟨writer offset % 32, Nat.mod_lt _ (by decide), by omega⟩
  have hv := full_blocks_value p ops input (List.range p.groups) (writer offset / 32) (writer offset) (offset / 8192 % 4) (offset % 256)
    (initial (layout p) input outside) List.nodup_range (initial_reads p input outside) (by intro a ha; cases ha)
    (initial_grid_ready p input outside) (List.mem_range.mpr hb) hm (Nat.mod_lt _ (by decide)) (Nat.mod_lt _ (by decide))
  rw [global_address_inverse offset] at hv
  exact (congrArg (fun state : State α => state.memory (globalCell 0 offset)) (grid_state p ops input (initial (layout p) input outside))).trans hv

theorem grid_race_free (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (outside : Location → Option α) :
    raceFree (geometry p) (gridState p ops input (initial (layout p) input outside)).trace = true :=
  race_free p _ (grid_reads_good p ops input outside).2

#print axioms grid_run
#print axioms grid_pc
#print axioms grid_value
#print axioms grid_reads_good
#print axioms grid_race_free
end LarkNativeAttention
