import Lark.NativeQKNormRopeSplitFence

/-! The four actual split-half rotary XOR16 snapshots inside physical wave64.
Each snapshot reads the original normalized register and preserves the others. -/
namespace LarkNativeQKNormRope
open LarkNonlinear LarkCollective
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

theorem split_exchange_code (e : Nat) (he : e < 4) :
    (program true)[60 + e]? = some (.shuffle .xor (25 + e) (18 + 2 * e) (.const 16) 32) := by
  have table : ∀ k : Fin 4, (program true)[60 + k.val]? =
      some (.shuffle .xor (25 + k.val) (18 + 2 * k.val) (.const 16) 32) := by decide
  exact table ⟨e, he⟩

theorem split_parked_fold (p : Shape) (ops : Ops α) (ts : List Nat) (s : State α)
    (cut : LarkCollective.Cut) (hp : ∀ t ∈ ts, LarkCollective.parked (program true) s t = some cut) :
    ts.foldlM (fun u t => LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane u) s =
      some s := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      have lane : LarkCollective.runLane ops (layout p) (geometry p) (program true) t fuel.lane s = some s := by
        simp only [fuel, LarkCollective.runLane, hp t (by simp)]
      rw [List.foldlM_cons, lane]
      exact ih (by intro u hu; exact hp u (by simp [hu]))

def SplitExchangeReady (block warp n : Nat) (values : Nat → Nat → α) (s : State α) : Prop :=
  ∀ lane, lane < 64 →
    s.pc (cohortBase block warp + lane) = 60 + n ∧
    (∀ e, e < 4 → s.regs (cohortBase block warp + lane) (18 + 2 * e) = some (values lane e)) ∧
    (∀ e, e < n → s.regs (cohortBase block warp + lane) (25 + e) = some (values (xorPeer32 lane 16) e))

def splitExchange (p : Shape) (block warp e : Nat) (values : Nat → Nat → α) (s : State α) : State α :=
  shuffleUpdates (25 + e) (xorSnapshot p block warp 64 16 (fun lane => values lane e)) s

theorem split_exchange_ready (p : Shape) (block warp n : Nat) (values : Nat → Nat → α)
    (s : State α) (hw : warp < 4) (hn : n < 4) (ready : SplitExchangeReady block warp n values s) :
    SplitExchangeReady block warp (n + 1) values (splitExchange p block warp n values s) := by
  intro lane hl
  have fields := xor_shuffled_fields p block warp 64 16 lane (25 + n)
    (fun lane => values lane n) s hw (by decide) hl
  refine ⟨?_, ?_, ?_⟩
  · simpa only [(ready lane hl).1, show 60 + n + 1 = 60 + (n + 1) by omega] using fields.1
  · intro e he
    exact (xor_shuffled_reg p block warp 64 16 (25 + n) _ (18 + 2 * e) _ s (by omega)).trans
      ((ready lane hl).2.1 e he)
  · intro e he
    by_cases same : e = n
    · subst e; exact fields.2
    · exact (xor_shuffled_reg p block warp 64 16 (25 + n) _ (25 + e) _ s (by omega)).trans
        ((ready lane hl).2.2 e (by omega))

theorem split_exchange_step (p : Shape) (ops : Ops α) (block warp n extra : Nat)
    (values : Nat → Nat → α) (s : State α) (hw : warp < 4) (hn : n < 4)
    (ready : SplitExchangeReady block warp n values s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (cohortThreads block warp 64) (extra + 1) s =
      LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
        (cohortThreads block warp 64) extra (splitExchange p block warp n values s) := by
  have parked : ∀ t ∈ cohortThreads block warp 64, LarkCollective.parked (program true) s t = some .shuffle := by
    intro t ht
    obtain ⟨lane, hl, rfl⟩ := (cohort_mem block warp 64 t).mp ht
    simp only [LarkCollective.parked, (ready lane hl).1, split_exchange_code n hn]
  have next : LarkPartitionCollective.nextCohort (program true) (cohortThreads block warp 64) s =
      some (cohortThreads block warp 64) := by
    apply cohort_next true block warp 64 (60 + n) s (by decide) (fun lane hl => (ready lane hl).1)
    intro t ht
    simp only [LarkPartitionCollective.isShuffle, ht, split_exchange_code n hn]
  rw [run_warp_continue, split_parked_fold p ops _ s .shuffle parked]
  simp only [Option.some_bind]
  rw [continue_shuffle p true ops _ _ extra s next]
  rw [cohort_xor_shuffle p true block warp 64 16 (60 + n) (25 + n) (18 + 2 * n)
    s (fun lane => values lane n) hw (Or.inr rfl) (by decide)
    (fun lane hl => (ready lane hl).1) (fun lane hl => (ready lane hl).2.1 n hn) (split_exchange_code n hn)]
  rfl

def splitExchanges (p : Shape) (block warp : Nat) (values : Nat → Nat → α) :
    Nat → Nat → State α → State α
  | _, 0, s => s
  | n, remaining + 1, s => splitExchanges p block warp values (n + 1) remaining
      (splitExchange p block warp n values s)

theorem split_exchanges_ready (p : Shape) (block warp n remaining : Nat) (values : Nat → Nat → α)
    (s : State α) (hw : warp < 4) (hn : n + remaining ≤ 4) (ready : SplitExchangeReady block warp n values s) :
    SplitExchangeReady block warp (n + remaining) values (splitExchanges p block warp values n remaining s) := by
  induction remaining generalizing n s with
  | zero => simpa only [splitExchanges, Nat.add_zero] using ready
  | succ remaining ih =>
      have later := ih (n + 1) _ (by omega) (split_exchange_ready p block warp n values s hw (by omega) ready)
      simpa only [splitExchanges, show n + 1 + remaining = n + (remaining + 1) by omega] using later

theorem split_exchanges_run (p : Shape) (ops : Ops α) (block warp n remaining extra : Nat)
    (values : Nat → Nat → α) (s : State α) (hw : warp < 4) (hn : n + remaining ≤ 4)
    (ready : SplitExchangeReady block warp n values s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (cohortThreads block warp 64) (extra + remaining) s =
      LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
        (cohortThreads block warp 64) extra (splitExchanges p block warp values n remaining s) := by
  induction remaining generalizing n s with
  | zero => rfl
  | succ remaining ih =>
      rw [show extra + (remaining + 1) = (extra + remaining) + 1 by omega,
        split_exchange_step p ops block warp n (extra + remaining) values s hw (by omega) ready]
      exact ih (n + 1) _ (by omega) (split_exchange_ready p block warp n values s hw (by omega) ready)

theorem split_exchanges_preserves (p : Shape) (block warp n remaining : Nat) (values : Nat → Nat → α)
    (s : State α) :
    (splitExchanges p block warp values n remaining s).memory = s.memory ∧
    (splitExchanges p block warp values n remaining s).indices = s.indices ∧
    (splitExchanges p block warp values n remaining s).epochs = s.epochs ∧
    (splitExchanges p block warp values n remaining s).trace = s.trace := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl, rfl, rfl⟩
  | succ remaining ih => exact ih (n + 1) (splitExchange p block warp n values s)

theorem split_exchanges_other (p : Shape) (block warp n remaining t : Nat) (values : Nat → Nat → α)
    (s : State α) (ht : t ∉ cohortThreads block warp 64) :
    (splitExchanges p block warp values n remaining s).pc t = s.pc t ∧
    (splitExchanges p block warp values n remaining s).regs t = s.regs t := by
  induction remaining generalizing n s with
  | zero => exact ⟨rfl, rfl⟩
  | succ remaining ih =>
      have later := ih (n + 1) (splitExchange p block warp n values s)
      have first := xor_shuffled_other p block warp 64 16 (25 + n) t (fun lane => values lane n) s ht
      exact ⟨later.1.trans first.1, later.2.trans first.2⟩

def splitWaveNormal (ops : Ops α) (input : Nat → Nat → α) (block warp lane e : Nat) : α :=
  let t := cohortBase block warp + lane
  normalizedValue ops input t (weightBuffer t) (normalScale ops (waveValues ops input block warp 5 lane)) e

def splitExchanged (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) : State α :=
  splitExchanges p block warp (splitWaveNormal ops input block warp) 0 4
    (splitFirstFence p ops input block warp s)

theorem split_exchanged_ready (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hw : warp < 4) :
    SplitExchangeReady block warp 4 (splitWaveNormal ops input block warp) (splitExchanged p ops input block warp s) := by
  apply split_exchanges_ready p block warp 0 4 _ _ hw (by decide)
  intro lane hl
  refine ⟨split_first_fence_pc p ops input block warp lane s hl, ?_, ?_⟩
  · intro e he; exact split_first_fence_value p ops input block warp lane e s hl he
  · intro e he; omega

theorem native_split_exchanges (p : Shape) (ops : Ops α) (input : Nat → Nat → α) (block warp : Nat)
    (s : State α) (hb : block < p.rows * 5) (hw : warp < 4)
    (hp : ∀ t ∈ cohortThreads block warp 64, s.pc t = 0) (hr : Reads p input s) :
    LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
      (warpThreads (geometry p) block warp) fuel.warp s =
      LarkPartitionCollective.runWarp ops (layout p) (geometry p) fuel (program true)
        (cohortThreads block warp 64) 6 (splitExchanged p ops input block warp s) := by
  rw [native_split_first_fence p ops input block warp s hb hw hp hr]
  apply split_exchanges_run p ops block warp 0 4 6 _ _ hw (by decide)
  intro lane hl
  refine ⟨split_first_fence_pc p ops input block warp lane s hl, ?_, ?_⟩
  · intro e he; exact split_first_fence_value p ops input block warp lane e s hl he
  · intro e he; omega

#print axioms split_exchange_code
#print axioms split_parked_fold
#print axioms split_exchange_ready
#print axioms split_exchange_step
#print axioms split_exchanges_ready
#print axioms split_exchanges_run
#print axioms split_exchanges_preserves
#print axioms split_exchanges_other
#print axioms split_exchanged_ready
#print axioms native_split_exchanges
end LarkNativeQKNormRope
