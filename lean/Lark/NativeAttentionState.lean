import Lark.NativeAttentionAddress
import Lark.Matrix

/-! State invariants and small actual-machine steps for the pinned native source. -/
namespace LarkNativeAttention
open LarkNonlinear
open LarkReduction (setIndex setReg int32_cast execute_index_of)
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def globalCell (buffer offset : Nat) : Location := ⟨.global, 0, buffer, offset⟩
def sharedCell (t buffer offset : Nat) : Location := ⟨.shared, t / 32, buffer, offset⟩

def Reads (p : Shape) (input : Nat → Nat → α) (s : State α) : Prop :=
  ∀ b, b = 1 ∨ b = 2 ∨ b = 3 → ∀ i, i < p.groups * 32768 →
    s.memory (globalCell b i) = some (input b i)

def NativeIndices (t : Nat) (s : State α) : Prop :=
  s.indices t 0 = some ((t / 32 : Nat) : Int) ∧
  s.indices t 1 = some ((t % 32 : Nat) : Int) ∧
  s.indices t 2 = some ((t / 32 * 32768 : Nat) : Int)

def TraceGood (s : State α) : Prop := ∀ a ∈ s.trace, Good a

def storeState (s : State α) (t : Nat) (l : Location) (v : α) (pc : Nat) : State α :=
  advance { record s t l true with memory := fun x => if x = l then some v else s.memory x } t pc

theorem store_memory (s : State α) (t : Nat) (l x : Location) (v : α) (pc : Nat) :
    (storeState s t l v pc).memory x = if x = l then some v else s.memory x := rfl

theorem store_indices (s : State α) (t : Nat) (l : Location) (v : α) (pc : Nat) :
    (storeState s t l v pc).indices = s.indices := rfl

theorem store_epochs (s : State α) (t : Nat) (l : Location) (v : α) (pc : Nat) :
    (storeState s t l v pc).epochs = s.epochs := rfl

theorem store_good (s : State α) (t : Nat) (l : Location) (v : α) (pc : Nat)
    (hs : TraceGood s) (ha : Good ⟨t, l, true, s.epochs t⟩) :
    TraceGood (storeState s t l v pc) := by
  intro a hm
  rcases List.mem_cons.mp hm with he | hm
  · exact he ▸ ha
  · exact hs a hm

theorem store_reads (p : Shape) (input : Nat → Nat → α) (s : State α) (t : Nat)
    (l : Location) (v : α) (pc : Nat) (hs : Reads p input s)
    (hl : ∀ b, b = 1 ∨ b = 2 ∨ b = 3 → ∀ i, globalCell b i ≠ l) :
    Reads p input (storeState s t l v pc) := by
  intro b hb i hi
  rw [store_memory, if_neg (hl b hb i)]
  exact hs b hb i hi

theorem indices_set (s : State α) (t r pc : Nat) (v : Int) (hr : 3 ≤ r)
    (hi : NativeIndices t s) : NativeIndices t (setIndex s t r v pc) := by
  rcases hi with ⟨h0, h1, h2⟩
  simp [NativeIndices, setIndex, advance, show 0 ≠ r by omega,
    show 1 ≠ r by omega, show 2 ≠ r by omega, h0, h1, h2]

theorem source_step (p : Shape) (ops : Ops α) (t pc extra : Nat) (i : Instr)
    (s next : State α) (hc : program[pc]? = some i) (hp : s.pc t = pc)
    (he : execute ops (layout p) (geometry p) t i s = some next) :
    runLane ops (layout p) (geometry p) program t (extra + 1) s =
      runLane ops (layout p) (geometry p) program t extra next := by
  apply LarkPointwise.lane_step ops (layout p) (geometry p) program t extra s next i
  · unfold parked
    rw [hp, hc]
    cases i <;> try rfl
    all_goals simp [execute] at he
  · simpa only [hp] using hc
  · exact he

def headerState (t : Nat) (s : State α) : State α :=
  let s := setIndex s t 0 ((t / 32 : Nat) : Int) 1
  let s := setIndex s t 1 ((t % 32 : Nat) : Int) 2
  setIndex s t 2 ((t / 32 * 32768 : Nat) : Int) 3

theorem header_fields (t : Nat) (s : State α) :
    NativeIndices t (headerState t s) ∧ (headerState t s).pc t = 3 ∧
    (headerState t s).memory = s.memory ∧ (headerState t s).epochs = s.epochs ∧
    (headerState t s).trace = s.trace := by
  simp [headerState, NativeIndices, setIndex, advance]

theorem header_eq (p : Shape) (ops : Ops α) (t extra : Nat) (s : State α)
    (ht : t < p.groups * 32) (hp : s.pc t = 0) :
    runLane ops (layout p) (geometry p) program t (extra + 3) s =
      runLane ops (layout p) (geometry p) program t extra (headerState t s) := by
  have hg : t / 32 < p.groups := by omega
  have hg32 : t / 32 < 2147483648 := by have h := p.bound; omega
  have hl32 : t % 32 < 2147483648 := by omega
  have hb32 : t / 32 * 32768 < 2147483648 := by have h := p.bound; omega
  let s1 := setIndex s t 0 ((t / 32 : Nat) : Int) 1
  let s2 := setIndex s1 t 1 ((t % 32 : Nat) : Int) 2
  have h1 := execute_index_of ops (layout p) (geometry p) t 0 1 .bid s ((t / 32 : Nat) : Int)
    (by simpa only [evalIndex, geometry] using int32_cast (t / 32) hg32) (by omega)
  have h2 := execute_index_of ops (layout p) (geometry p) t 1 2 .tid s1 ((t % 32 : Nat) : Int)
    (by simpa only [evalIndex, geometry] using int32_cast (t % 32) hl32)
    (by simp [s1, setIndex, advance])
  have hx := LarkMatrix.eval_mul_nat (geometry p) t s2 (.ivar 0) (.const 32768)
    (t / 32) 32768 (by simp [evalIndex, s2, s1, setIndex, advance]) (by rfl) hb32
  have h3 := execute_index_of ops (layout p) (geometry p) t 2 3
    (.mul (.ivar 0) (.const 32768)) s2 ((t / 32 * 32768 : Nat) : Int) hx
    (by simp [s2, setIndex, advance])
  have hstep1 := source_step p ops t 0 (extra + 2) (.index 0 .bid) s s1 (by rfl) hp h1
  have hstep2 := source_step p ops t 1 (extra + 1) (.index 1 .tid) s1 s2 (by rfl)
    (by simp [s1, setIndex, advance]) h2
  have hstep3 := source_step p ops t 2 extra (.index 2 (.mul (.ivar 0) (.const 32768)))
    s2 (headerState t s) (by rfl) (by simp [s2, setIndex, advance]) h3
  exact hstep1.trans (hstep2.trans hstep3)

#print axioms source_step
#print axioms header_eq
end LarkNativeAttention
