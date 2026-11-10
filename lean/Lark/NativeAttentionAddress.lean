import Lark.NativeAttentionFootprint

/-! Bounds and ownership for the exact tiled source address formulas. These
facts are components, not a proof that the whole source executes them correctly. -/
namespace LarkNativeAttention
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

def globalAddress (t tile col : Nat) : Nat :=
  t / 32 * 32768 + tile * 8192 + t % 32 * 256 + col
def sharedAddress (t col : Nat) : Nat := t % 32 * 256 + col
def scoreAddress (t col : Nat) : Nat := t % 32 * 32 + col

theorem global_address_bound (p : Shape) (t tile col : Nat)
    (ht : t < p.groups * 32) (hi : tile < 4) (hc : col < 256) :
    globalAddress t tile col < p.groups * 32768 := by
  unfold globalAddress
  omega

theorem global_address_int32 (p : Shape) (t tile col : Nat)
    (ht : t < p.groups * 32) (hi : tile < 4) (hc : col < 256) :
    globalAddress t tile col < 2147483648 := by
  exact Nat.lt_trans (global_address_bound p t tile col ht hi hc) (global_span_int32 p)

theorem global_address_owner (t tile col : Nat) (hi : tile < 4) (hc : col < 256) :
    writer (globalAddress t tile col) = t := by
  unfold writer globalAddress
  omega

/-- Every declared output has a source row-tile/lane/column coordinate. -/
theorem global_address_inverse (offset : Nat) :
    globalAddress (writer offset) (offset / 8192 % 4) (offset % 256) = offset := by
  unfold globalAddress writer
  omega

theorem writer_bound (p : Shape) (offset : Nat) (hi : offset < p.groups * 32768) :
    writer offset < p.groups * 32 := by
  unfold writer
  omega

theorem shared_address_bound (t col : Nat) (hc : col < 256) :
    sharedAddress t col < 8192 := by
  unfold sharedAddress
  omega

theorem shared_address_owner (t col : Nat) (hc : col < 256) :
    sharedAddress t col / 256 = t % 32 := by
  unfold sharedAddress
  omega

theorem score_address_bound (t col : Nat) (hc : col < 32) :
    scoreAddress t col < 1024 := by
  unfold scoreAddress
  omega

theorem score_address_owner (t col : Nat) (hc : col < 32) :
    scoreAddress t col / 32 = t % 32 := by
  unfold scoreAddress
  omega

theorem global_location_of (l : Layout) (g : Geometry) (t buffer offset : Nat)
    (write : Bool) (buf : Buffer) (hb : l.global[buffer]? = some buf)
    (hw : (write && (buf.role == Role.input)) = false) (hi : offset < buf.size) :
    location l g t .global buffer (offset : Int) write = some ⟨.global, 0, buffer, offset⟩ := by
  have hnot : ¬ (write = true ∧ (buf.role == Role.input) = true) := by
    rintro ⟨hwrite, hinput⟩
    simp [hwrite, hinput] at hw
  simp [location, hb, hnot, hi]

theorem output_location (p : Shape) (t offset : Nat) (write : Bool)
    (hi : offset < p.groups * 32768) :
    location (layout p) (geometry p) t .global 0 (offset : Int) write =
      some ⟨.global, 0, 0, offset⟩ := by
  exact global_location_of (layout p) (geometry p) t 0 offset write
    ⟨.output, p.groups * 32768⟩ (by rfl)
    (by simp [show (Role.output == Role.input) = false by decide]) hi

theorem global_read_location_of (l : Layout) (g : Geometry) (t buffer offset : Nat)
    (buf : Buffer) (hb : l.global[buffer]? = some buf) (hi : offset < buf.size) :
    location l g t .global buffer (offset : Int) false = some ⟨.global, 0, buffer, offset⟩ := by
  simp [location, hb, hi]

theorem input_location (p : Shape) (t buffer offset : Nat)
    (hb : buffer = 1 ∨ buffer = 2 ∨ buffer = 3) (hi : offset < p.groups * 32768) :
    location (layout p) (geometry p) t .global buffer (offset : Int) false =
      some ⟨.global, 0, buffer, offset⟩ := by
  rcases hb with rfl | rfl | rfl
  all_goals
    exact global_read_location_of (layout p) (geometry p) t _ offset
      ⟨.input, p.groups * 32768⟩ (by rfl) hi

theorem shared_location (p : Shape) (t buffer offset : Nat) (write : Bool)
    (hb : buffer < 3) (hi : offset < 8192) :
    location (layout p) (geometry p) t .shared buffer (offset : Int) write =
      some ⟨.shared, t / 32, buffer, offset⟩ := by
  rcases (show buffer = 0 ∨ buffer = 1 ∨ buffer = 2 by omega) with rfl | rfl | rfl <;>
    simp [location, layout, geometry, hi]

theorem score_location (p : Shape) (t offset : Nat) (write : Bool) (hi : offset < 1024) :
    location (layout p) (geometry p) t .shared 3 (offset : Int) write =
      some ⟨.shared, t / 32, 3, offset⟩ := by
  simp [location, layout, geometry, hi]

theorem output_access_good (t tile col : Nat) (write : Bool) (epoch : Epoch)
    (hi : tile < 4) (hc : col < 256) :
    Good ⟨t, ⟨.global, 0, 0, globalAddress t tile col⟩, write, epoch⟩ := by
  exact Good.output rfl rfl rfl (global_address_owner t tile col hi hc).symm

theorem qi_access_good (t col : Nat) (write : Bool) (epoch : Epoch) (hc : col < 256) :
    Good ⟨t, ⟨.shared, t / 32, 0, sharedAddress t col⟩, write, epoch⟩ := by
  apply Good.privateShared rfl rfl (Or.inl rfl)
  simpa [privateWidth] using (shared_address_owner t col hc).symm

theorem score_access_good (t col : Nat) (write : Bool) (epoch : Epoch) (hc : col < 32) :
    Good ⟨t, ⟨.shared, t / 32, 3, scoreAddress t col⟩, write, epoch⟩ := by
  apply Good.privateShared rfl rfl (Or.inr rfl)
  simpa [privateWidth] using (score_address_owner t col hc).symm

theorem tile_store_access_good (t buffer col : Nat) (epoch : Epoch)
    (hb : buffer = 1 ∨ buffer = 2) (hc : col < 256) (he : epoch.block % 2 = 0) :
    Good ⟨t, ⟨.shared, t / 32, buffer, sharedAddress t col⟩, true, epoch⟩ := by
  exact Good.tileStore rfl rfl hb (shared_address_owner t col hc).symm he rfl

theorem private_access_good (t buffer offset : Nat) (write : Bool) (epoch : Epoch) :
    Good ⟨t, ⟨.local, t, buffer, offset⟩, write, epoch⟩ := by
  exact Good.localAccess rfl rfl

#print axioms global_address_int32
#print axioms global_address_owner
#print axioms global_address_inverse
#print axioms output_location
#print axioms output_access_good
#print axioms tile_store_access_good
end LarkNativeAttention
