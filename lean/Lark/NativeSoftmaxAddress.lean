import Lark.NativeSoftmaxProgram

/-! Source-loop coverage, ownership and the clamped final-pass address pair. -/
namespace LarkNativeSoftmax
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def column (tid iteration component : Nat) : Nat := tid + (iteration * 8 + component) * 1024
def base (tid iteration : Nat) : Nat := tid + iteration * 8192
def clamped (col : Nat) : Nat := min 50256 col
def address (row col : Nat) : Nat := row * 50257 + col
def writer (offset : Nat) : Nat := offset / 50257 * 1024 + offset % 50257 % 1024
def globalCell (buffer offset : Nat) : Location := ⟨.global,0,buffer,offset⟩

theorem column_expansion (tid iteration component : Nat) :
    column tid iteration component = base tid iteration + component * 1024 := by
  simp [column,base,Nat.add_mul,Nat.mul_assoc,Nat.add_assoc]

theorem column_owner (tid iteration component : Nat) (ht : tid < 1024) :
    column tid iteration component % 1024 = tid := by
  simp [column,Nat.add_mod,Nat.mod_eq_of_lt ht]

theorem column_injective (tid iter comp other it co : Nat)
    (ht : tid < 1024) (ho : other < 1024) (hc : comp < 8) (hco : co < 8)
    (he : column tid iter comp = column other it co) :
    tid = other ∧ iter = it ∧ comp = co := by
  have hm := congrArg (· % 1024) he
  change column tid iter comp % 1024 = column other it co % 1024 at hm
  rewrite [column_owner tid iter comp ht,column_owner other it co ho] at hm
  subst other
  unfold column at he
  constructor
  · rfl
  · omega

theorem column_cover (col : Nat) (hc : col < 50257) :
    ∃ tid iteration component,
      tid < 1024 ∧ iteration < 7 ∧ component < 8 ∧ base tid iteration < 50257 ∧
      column tid iteration component = col := by
  refine ⟨col % 1024,col / 1024 / 8,col / 1024 % 8,by omega,by omega,by omega,?_,?_⟩
  · unfold base
    omega
  · unfold column
    omega

theorem clamped_bound (col : Nat) : clamped col < 50257 := by
  unfold clamped
  omega

theorem in_bounds_clamp (col : Nat) (h : col < 50257) : clamped col = col := by
  unfold clamped
  omega

theorem address_bound (p : Shape) (row col : Nat) (hr : row < p.rows) (hc : col < 50257) :
    address row col < p.rows * 50257 := by unfold address; omega

theorem address_writer (row tid iteration component : Nat)
    (ht : tid < 1024) (hc : column tid iteration component < 50257) :
    writer (address row (column tid iteration component)) = row * 1024 + tid := by
  have hd : address row (column tid iteration component) / 50257 = row := by unfold address; omega
  have hm : address row (column tid iteration component) % 50257 = column tid iteration component := by
    unfold address
    omega
  simp only [writer,hd,hm,column_owner tid iteration component ht]

theorem clamped_race_addresses :
    base 0 6 < 50257 ∧ base 80 6 < 50257 ∧
    50257 ≤ column 0 6 2 ∧ column 80 6 1 < 50257 ∧
    clamped (column 0 6 2) = 50256 ∧ column 80 6 1 = 50256 ∧
    writer 50256 = 80 := by decide

theorem guard_skips_bad_read : ¬ column 0 6 2 < 50257 := by decide

#print axioms column_expansion
#print axioms column_owner
#print axioms column_injective
#print axioms column_cover
#print axioms clamped_bound
#print axioms in_bounds_clamp
#print axioms address_bound
#print axioms address_writer
#print axioms clamped_race_addresses
#print axioms guard_skips_bad_read
end LarkNativeSoftmax
