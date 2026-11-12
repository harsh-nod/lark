import Lark.NativeAwqGemmMMAElement

/-! All 256 native MFMA results are computed from the one old snapshot
before the machine applies any accumulator or PC update. -/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false
variable {α : Type}

def matrixCoordinates (p : Shape) (b : Nat) : List (Nat × Nat) :=
  (blockThreads (geometry p) b).flatMap (fun t => (List.range 4).map (fun e => (t,e)))

theorem matrix_coordinates_mem (p : Shape) (b t e : Nat) :
    (t,e)∈matrixCoordinates p b ↔ t∈blockThreads (geometry p) b ∧ e<4 := by
  simp [matrixCoordinates,List.mem_flatMap]

def matrixValues (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) : List ((Nat × Nat) × α) :=
  (matrixCoordinates p b).map (fun pair => ((pair.1,bank*4+pair.2),matrixValue p ops input tile b half bank acc pair.1 pair.2))

theorem matrix_values_execute (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) (hh : half<2) (hb : bank<banks p)
    (ready : ∀ t∈blockThreads (geometry p) b, OperandReady p ops input tile half bank t s)
    (hc : ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 → s.regs t (bank*4+e)=some (acc t e)) :
    LarkMFMA.mfmaValues ops (geometry p) (program p) (blockThreads (geometry p) b) s=
      some (matrixValues p ops input tile b half bank acc) := by
  have headMember : b*64∈blockThreads (geometry p) b :=
    List.mem_map.mpr ⟨0,by change 0∈List.range 64; decide,rfl⟩
  have headPC := (ready (b*64) headMember).pc
  rw [LarkMFMA.mfmaValues_of ops (geometry p) (program p) (blockThreads (geometry p) b) s
    (b*64) (bank*4) (leftBase p half) (rightBase p half bank) (bank*4)
    rfl (by change (64%64 : Nat)=0; decide) (by simp [blockThreads,geometry]) rfl
    (by rw [headPC]; exact matrix_instruction_site p half bank hh hb)]
  exact matrix_mapM_some (matrixCoordinates p b)
    (LarkMFMA.mfmaElement ops (geometry p) (blockThreads (geometry p) b) (bank*4) (leftBase p half) (rightBase p half bank) (bank*4) s)
    (fun pair => ((pair.1,bank*4+pair.2),matrixValue p ops input tile b half bank acc pair.1 pair.2)) (by
      intro pair hp
      have coordinate := (matrix_coordinates_mem p b pair.1 pair.2).mp hp
      exact matrix_element p ops input tile b half bank acc s pair.1 pair.2 coordinate.1 coordinate.2 ready hc)

def matrixState (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) : State α :=
  LarkMFMA.mfmaUpdates (matrixValues p ops input tile b half bank acc) s

theorem native_matrix_execute (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) (hh : half<2) (hb : bank<banks p)
    (ready : ∀ t∈blockThreads (geometry p) b, OperandReady p ops input tile half bank t s)
    (hc : ∀ t∈blockThreads (geometry p) b, ∀ e, e<4 → s.regs t (bank*4+e)=some (acc t e)) :
    LarkMFMA.runMFMA ops (geometry p) (program p) (blockThreads (geometry p) b) s=
      some (matrixState p ops input tile b half bank acc s) :=
  LarkMFMA.runMFMA_of ops (geometry p) (program p) (blockThreads (geometry p) b) s
    (matrixValues p ops input tile b half bank acc) (matrix_values_execute p ops input tile b half bank acc s hh hb ready hc)

theorem matrix_state_frames (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) :
    (matrixState p ops input tile b half bank acc s).memory=s.memory ∧
      (matrixState p ops input tile b half bank acc s).trace=s.trace ∧
        (matrixState p ops input tile b half bank acc s).indices=s.indices ∧
          (matrixState p ops input tile b half bank acc s).epochs=s.epochs := ⟨rfl,rfl,rfl,rfl⟩

def matrixKeys (p : Shape) (b bank : Nat) : List (Nat × Nat) :=
  (matrixCoordinates p b).map (fun pair => (pair.1,bank*4+pair.2))

theorem matrix_keys_mem (p : Shape) (b bank t e : Nat) (ht : t∈blockThreads (geometry p) b) (he : e<4) :
    (t,bank*4+e)∈matrixKeys p b bank :=
  List.mem_map.mpr ⟨(t,e),(matrix_coordinates_mem p b t e).mpr ⟨ht,he⟩,rfl⟩

theorem matrix_keys_iff (p : Shape) (b bank t r : Nat) :
    (t,r)∈matrixKeys p b bank ↔ t∈blockThreads (geometry p) b ∧ bank*4≤r ∧ r<bank*4+4 := by
  constructor
  · intro member
    rcases List.mem_map.mp member with ⟨⟨u,e⟩,hp,eq⟩
    have coordinate := (matrix_coordinates_mem p b u e).mp hp
    have sameThread := congrArg Prod.fst eq
    have sameReg := congrArg Prod.snd eq
    simp only [Prod.fst,Prod.snd] at sameThread sameReg
    subst u
    exact ⟨coordinate.1,by omega,by omega⟩
  · rintro ⟨ht,hlo,hhi⟩
    have he : r-bank*4<4 := by omega
    have equal : bank*4+(r-bank*4)=r := by omega
    simpa only [equal] using matrix_keys_mem p b bank t (r-bank*4) ht he

theorem matrix_values_keys (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) :
    matrixValues p ops input tile b half bank acc=
      (matrixKeys p b bank).map (fun key => (key,matrixValue p ops input tile b half bank acc key.1 (key.2-bank*4))) := by
  simp [matrixValues,matrixKeys,List.map_map,Nat.add_sub_cancel_left]

theorem matrix_lookup_map (xs : List (Nat × Nat)) (value : Nat × Nat → α) (key : Nat × Nat) (h : key∈xs) :
    List.lookup key (xs.map (fun k => (k,value k)))=some (value key) := by
  induction xs with
  | nil => simp at h
  | cons a xs ih =>
    by_cases same : key=a
    · subst key; simp
    · have member : key∈xs := by simpa [same] using h
      have different : (key==a)=false := by simp [same]
      simpa only [List.map_cons,List.lookup_cons,different] using ih member

theorem matrix_lookup_outside (xs : List (Nat × Nat)) (value : Nat × Nat → α) (key : Nat × Nat) (h : key∉xs) :
    List.lookup key (xs.map (fun k => (k,value k)))=none := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have different : key≠a := by intro same; exact h (List.mem_cons.mpr (Or.inl same))
    have rest : key∉xs := by intro member; exact h (List.mem_cons_of_mem a member)
    have neq : (key==a)=false := by simp [different]
    simpa only [List.map_cons,List.lookup_cons,neq] using ih rest

theorem matrix_state_regs (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) (t e : Nat)
    (ht : t∈blockThreads (geometry p) b) (he : e<4) :
    (matrixState p ops input tile b half bank acc s).regs t (bank*4+e)=
      some (matrixValue p ops input tile b half bank acc t e) := by
  change (match List.lookup (t,bank*4+e) (matrixValues p ops input tile b half bank acc) with
    | some value => some value | none => s.regs t (bank*4+e))=_
  rw [matrix_values_keys,matrix_lookup_map (matrixKeys p b bank) _ (t,bank*4+e) (matrix_keys_mem p b bank t e ht he)]
  simp [Nat.add_sub_cancel_left]

theorem matrix_state_regs_other (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) (t r : Nat)
    (hr : ¬(t∈blockThreads (geometry p) b ∧ bank*4≤r ∧ r<bank*4+4)) :
    (matrixState p ops input tile b half bank acc s).regs t r=s.regs t r := by
  have outside : (t,r)∉matrixKeys p b bank := by intro member; exact hr ((matrix_keys_iff p b bank t r).mp member)
  change (match List.lookup (t,r) (matrixValues p ops input tile b half bank acc) with
    | some value => some value | none => s.regs t r)=_
  rw [matrix_values_keys,matrix_lookup_outside (matrixKeys p b bank) _ (t,r) outside]

theorem matrix_values_any (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (t : Nat) :
    (matrixValues p ops input tile b half bank acc).any (fun pair => pair.1.1==t)=decide (t∈blockThreads (geometry p) b) := by
  apply Bool.eq_iff_iff.mpr
  simp [matrixValues,matrixCoordinates,List.any_eq_true,List.mem_flatMap]
  intro _
  exact ⟨0,by decide⟩

theorem matrix_state_pc (p : Shape) (ops : Ops α) (input : Nat → Nat → α)
    (tile b half bank : Nat) (acc : Nat → Nat → α) (s : State α) (t : Nat) :
    (matrixState p ops input tile b half bank acc s).pc t=
      if t∈blockThreads (geometry p) b then s.pc t+1 else s.pc t := by
  simp [matrixState,LarkMFMA.mfmaUpdates,matrix_values_any]

#print axioms matrix_coordinates_mem
#print axioms matrix_values_execute
#print axioms native_matrix_execute
#print axioms matrix_state_frames
#print axioms matrix_keys_mem
#print axioms matrix_keys_iff
#print axioms matrix_values_keys
#print axioms matrix_lookup_map
#print axioms matrix_lookup_outside
#print axioms matrix_state_regs
#print axioms matrix_state_regs_other
#print axioms matrix_values_any
#print axioms matrix_state_pc
end LarkNativeAwqGemm
