import Lark.NativeSglangRmsNormTrace

/-! Each scalar prefix writes only its own input/weight private caches.
Other threads' machine fields and all global/shared memory are framed. -/
namespace LarkNativeSglangRmsNorm
open LarkNonlinear
open LarkReduction (setIndex setReg)
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def OutsidePrivate (t : Nat) (l : Location) : Prop :=
  l.space ≠ .local ∨ l.owner ≠ t ∨ 2 ≤ l.buffer

structure ThreadFrame (t : Nat) (before after : State α) : Prop where
  pc : ∀ u, u ≠ t → after.pc u = before.pc u
  indices : ∀ u, u ≠ t → after.indices u = before.indices u
  regs : ∀ u, u ≠ t → after.regs u = before.regs u
  memory : ∀ l, OutsidePrivate t l → after.memory l = before.memory l

theorem ThreadFrame.refl (t : Nat) (s : State α) : ThreadFrame t s s :=
  ⟨fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl,fun _ _ => rfl⟩

theorem ThreadFrame.trans {t : Nat} {s a b : State α}
    (first : ThreadFrame t s a) (second : ThreadFrame t a b) : ThreadFrame t s b :=
  ⟨fun u hu => (second.pc u hu).trans (first.pc u hu),
   fun u hu => (second.indices u hu).trans (first.indices u hu),
   fun u hu => (second.regs u hu).trans (first.regs u hu),
   fun l hl => (second.memory l hl).trans (first.memory l hl)⟩

theorem outside_not_private (t buffer slot : Nat) (l : Location) (hb : buffer < 2)
    (outside : OutsidePrivate t l) : l ≠ privateCell t buffer slot := by
  intro he
  subst l
  simp [OutsidePrivate,privateCell] at outside
  omega

theorem advance_frame (t pc : Nat) (s : State α) : ThreadFrame t s (advance s t pc) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u hu; simp [advance,hu]
  · intro u hu; rfl
  · intro u hu; rfl
  · intro l hl; rfl

theorem set_index_frame (t q : Nat) (value : Int) (pc : Nat) (s : State α) :
    ThreadFrame t s (setIndex s t q value pc) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u hu; simp [setIndex,advance,hu]
  · intro u hu; funext r; simp [setIndex,advance,hu]
  · intro u hu; rfl
  · intro l hl; rfl

theorem sum_started_frame (ops : Ops α) (t : Nat) (s : State α) :
    ThreadFrame t s (sumStarted ops t s) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u hu; simp [sumStarted,setIndex,setReg,advance,hu]
  · intro u hu; funext r; simp [sumStarted,setIndex,setReg,advance,hu]
  · intro u hu; funext r; simp [sumStarted,setIndex,setReg,advance,hu]
  · intro l hl; rfl

theorem initialized_frame (t : Nat) (s : State α) : ThreadFrame t s (initialized t s) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u hu; exact (initialized_other t u s hu).1
  · intro u hu; exact (initialized_other t u s hu).2.1
  · intro u hu; exact (initialized_other t u s hu).2.2
  · intro l hl; rfl

theorem input_after_frame (input : Nat → Nat → α) (row tid iteration component t : Nat) (s : State α) :
    ThreadFrame t s (inputCacheAfter input row tid iteration component t s) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u hu; simp [inputCacheAfter,setIndex,cacheWritten,record,advance,hu]
  · intro u hu; funext r; simp [inputCacheAfter,setIndex,cacheWritten,record,advance,hu]
  · intro u hu; rfl
  · intro l hl
    rw [input_cache_memory]
    simp only [if_neg (outside_not_private t 0 _ l (by decide) hl)]

theorem input_components_frame (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (s : State α) :
    ThreadFrame t s (inputCacheComponents input row tid iteration t component remaining s) := by
  induction remaining generalizing component s with
  | zero => exact ThreadFrame.refl t s
  | succ remaining ih =>
      exact (input_after_frame input row tid iteration component t s).trans
        (ih (component + 1) (inputCacheAfter input row tid iteration component t s))

theorem input_round_frame (input : Nat → Nat → α) (row tid iteration t : Nat) (s : State α) :
    ThreadFrame t s (inputCacheRound input row tid iteration t s) := by
  let entry := inputCacheEntry t s
  let copied := inputCacheComponents input row tid iteration t 0 8 entry
  have f0 := (advance_frame t 6 s).trans (set_index_frame t 5 0 7 (advance s t 6))
  have f1 := input_components_frame input row tid iteration t 0 8 entry
  have f2 := (advance_frame t 14 copied).trans
    ((set_index_frame t 4 ((iteration + 1 : Nat) : Int) 15 (advance copied t 14)).trans
      (advance_frame t 5 _))
  exact f0.trans (f1.trans f2)

theorem input_preloads_frame (input : Nat → Nat → α) (t : Nat) (s : State α) :
    ThreadFrame t s (inputPreloads input t s) := by
  let s0 := initialized t s
  let s1 := inputCacheRound input (t / 1024) (t % 1024) 0 t s0
  let s2 := inputCacheRound input (t / 1024) (t % 1024) 1 t s1
  exact (initialized_frame t s).trans
    ((input_round_frame input (t / 1024) (t % 1024) 0 t s0).trans
      ((input_round_frame input (t / 1024) (t % 1024) 1 t s1).trans (advance_frame t 16 s2)))

theorem weight_after_frame (input : Nat → Nat → α) (tid iteration component t : Nat) (s : State α) :
    ThreadFrame t s (weightCacheAfter input tid iteration component t s) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u hu; simp [weightCacheAfter,setIndex,cacheWritten,record,advance,hu]
  · intro u hu; funext r; simp [weightCacheAfter,setIndex,cacheWritten,record,advance,hu]
  · intro u hu; rfl
  · intro l hl
    rw [weight_cache_memory]
    simp only [if_neg (outside_not_private t 1 _ l (by decide) hl)]

theorem weight_components_frame (input : Nat → Nat → α)
    (row tid iteration t component remaining : Nat) (s : State α) :
    ThreadFrame t s (weightCacheComponents input row tid iteration t component remaining s) := by
  induction remaining generalizing component s with
  | zero => exact ThreadFrame.refl t s
  | succ remaining ih =>
      exact (weight_after_frame input tid iteration component t s).trans
        (ih (component + 1) (weightCacheAfter input tid iteration component t s))

theorem weight_round_frame (input : Nat → Nat → α) (row tid iteration t : Nat) (s : State α) :
    ThreadFrame t s (weightCacheRound input row tid iteration t s) := by
  let entry := weightCacheEntry t s
  let copied := weightCacheComponents input row tid iteration t 0 8 entry
  have f0 := (advance_frame t 18 s).trans (set_index_frame t 10 0 19 (advance s t 18))
  have f1 := weight_components_frame input row tid iteration t 0 8 entry
  have f2 := (advance_frame t 25 copied).trans
    ((set_index_frame t 9 ((iteration + 1 : Nat) : Int) 26 (advance copied t 25)).trans
      (advance_frame t 17 _))
  exact f0.trans (f1.trans f2)

theorem preloads_frame (input : Nat → Nat → α) (t : Nat) (s : State α) :
    ThreadFrame t s (preloads input t s) := by
  let si := inputPreloads input t s
  let s0 := setIndex si t 9 0 17
  let s1 := weightCacheRound input (t / 1024) (t % 1024) 0 t s0
  let s2 := weightCacheRound input (t / 1024) (t % 1024) 1 t s1
  exact (input_preloads_frame input t s).trans ((set_index_frame t 9 0 17 si).trans
    ((weight_round_frame input (t / 1024) (t % 1024) 0 t s0).trans
      ((weight_round_frame input (t / 1024) (t % 1024) 1 t s1).trans (advance_frame t 27 s2))))

theorem pair_after_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration pair t : Nat) (acc : α) (s : State α) :
    ThreadFrame t s (pairAfter ops input row tid iteration pair t acc s) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro u hu; exact (pair_other ops input row tid iteration pair t u acc s hu).1
  · intro u hu; exact (pair_other ops input row tid iteration pair t u acc s hu).2.1
  · intro u hu; exact (pair_other ops input row tid iteration pair t u acc s hu).2.2
  · intro l hl; rfl

theorem pairs_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t pair remaining : Nat) (acc : α) (s : State α) :
    ThreadFrame t s (pairs ops input row tid iteration t pair remaining acc s) := by
  induction remaining generalizing pair acc s with
  | zero => exact ThreadFrame.refl t s
  | succ remaining ih =>
      exact (pair_after_frame ops input row tid iteration pair t acc s).trans
        (ih (pair + 1) (ops.add acc (pairSquare ops input row tid iteration pair))
          (pairAfter ops input row tid iteration pair t acc s))

theorem round_frame (ops : Ops α) (input : Nat → Nat → α)
    (row tid iteration t : Nat) (acc : α) (s : State α) :
    ThreadFrame t s (roundAfter ops input row tid iteration t acc s) := by
  let entry := beginRound t s
  let copied := pairs ops input row tid iteration t 0 4 acc entry
  have f0 := (advance_frame t 31 s).trans (set_index_frame t 14 0 32 (advance s t 31))
  have f1 := pairs_frame ops input row tid iteration t 0 4 acc entry
  have f2 := (advance_frame t 42 copied).trans
    ((set_index_frame t 13 ((iteration + 1 : Nat) : Int) 43 (advance copied t 42)).trans
      (advance_frame t 30 _))
  exact f0.trans (f1.trans f2)

theorem prefix_frame (ops : Ops α) (input : Nat → Nat → α) (t : Nat) (s : State α) :
    ThreadFrame t s (prefixState ops input t s) := by
  let zero := ops.literal 0 1
  let s0 := sumStarted ops t (preloads input t s)
  let s1 := roundAfter ops input (t / 1024) (t % 1024) 0 t zero s0
  let s2 := roundAfter ops input (t / 1024) (t % 1024) 1 t
    (pairFold ops input (t / 1024) (t % 1024) 0 0 4 zero) s1
  exact (preloads_frame input t s).trans ((sum_started_frame ops t _).trans
    ((round_frame ops input (t / 1024) (t % 1024) 0 t zero s0).trans
      ((round_frame ops input (t / 1024) (t % 1024) 1 t _ s1).trans (advance_frame t 44 s2))))

theorem prefix_reads_frame (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t : Nat) (s : State α) (reads : Reads p input s) : Reads p input (prefixState ops input t s) := by
  have f := prefix_frame ops input t s
  constructor
  · intro i hi
    rw [f.memory (globalCell 1 i) (Or.inl (by simp [globalCell]))]
    exact reads.1 i hi
  · intro i hi
    rw [f.memory (globalCell 2 i) (Or.inl (by simp [globalCell]))]
    exact reads.2 i hi

theorem prefix_data_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (t u : Nat) (s : State α) (hu : u ≠ t) (ready : PrefixData p ops input u s) :
    PrefixData p ops input u (prefixState ops input t s) := by
  have f := prefix_frame ops input t s
  exact {
    pc := (f.pc u hu).trans ready.pc
    accumulator := (congrFun (f.regs u hu) 0).trans ready.accumulator
    reads := prefix_reads_frame p ops input t s ready.reads
    inputs := by
      intro k hk
      rw [f.memory (privateCell u 0 k) (Or.inr (Or.inl hu))]
      exact ready.inputs k hk
    weights := by
      intro k hk
      rw [f.memory (privateCell u 1 k) (Or.inr (Or.inl hu))]
      exact ready.weights k hk }

#print axioms ThreadFrame.trans
#print axioms outside_not_private
#print axioms input_after_frame
#print axioms input_components_frame
#print axioms input_round_frame
#print axioms input_preloads_frame
#print axioms weight_after_frame
#print axioms weight_components_frame
#print axioms weight_round_frame
#print axioms preloads_frame
#print axioms pair_after_frame
#print axioms pairs_frame
#print axioms round_frame
#print axioms prefix_frame
#print axioms prefix_reads_frame
#print axioms prefix_data_other
end LarkNativeSglangRmsNorm
