import Lark.MFMA

/-! Pinned FP16 AWQ departure and explicit native wave64 fragment remapping.
These are source address/ownership components, not a complete execution proof.
Both upstream N64/N128 staging paths and padded shared row strides are retained.
-/
namespace LarkNativeAwqGemm
open LarkNonlinear
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000
set_option autoImplicit false

structure Shape where
  m : Nat
  k : Nat
  n : Nat
  m_pos : 0<m
  k_pos : 0<k
  n_pos : 0<n
  k_aligned : k%32=0
  n_aligned : n%64=0
  a_bound : m*k≤2147483648
  b_bound : k*n≤2147483648
  out_bound : m*n≤2147483648

def tileN (p : Shape) : Nat := if p.n%128=0 then 128 else 64
def columnTiles (p : Shape) : Nat := p.n/tileN p
def rowTiles (p : Shape) : Nat := (p.m+15)/16
def geometry (p : Shape) : Geometry := ⟨rowTiles p*columnTiles p,64,64⟩
def fuel (p : Shape) : Fuel := ⟨512,tileN p/8+1,2*(p.k/32)+1,1⟩
def layout (p : Shape) : Layout :=
  ⟨[⟨.input,p.m*p.k⟩,⟨.input,p.k*p.n⟩,⟨.output,p.m*p.n⟩],[640,32*(tileN p+8)],[]⟩

theorem tile_cases (p : Shape) : tileN p=64 ∨ tileN p=128 := by
  unfold tileN
  split
  · exact Or.inr rfl
  · exact Or.inl rfl

theorem tile_aligned (p : Shape) : p.n%tileN p=0 := by
  unfold tileN
  split
  · assumption
  · exact p.n_aligned

theorem column_tiles_positive (p : Shape) : 0<columnTiles p := by
  have hn := p.n_pos
  have ha := tile_aligned p
  rcases tile_cases p with ht | ht
  · unfold columnTiles
    rw [ht]
    rw [ht] at ha
    omega
  · unfold columnTiles
    rw [ht]
    rw [ht] at ha
    omega

theorem columns_exact (p : Shape) : columnTiles p*tileN p=p.n :=
  Nat.div_mul_cancel (Nat.dvd_of_mod_eq_zero (tile_aligned p))

theorem row_tiles_positive (p : Shape) : 0<rowTiles p := by
  have h := p.m_pos
  unfold rowTiles
  omega

def aStoreRow (t : Nat) : Nat := (t/32)*8+(t%32)/4
def aStoreCol (t e : Nat) : Nat := (t%32%4)*8+e
def aStoreAddress (t e : Nat) : Nat := aStoreRow t*40+aStoreCol t e
def aOwner (row col : Nat) : Nat := row/8*32+(row%8)*4+col/8

theorem a_store_coordinates (t e : Nat) (ht : t<64) (he : e<8) :
    aStoreRow t<16 ∧ aStoreCol t e<32 := by
  unfold aStoreRow aStoreCol
  omega

theorem a_store_bound (t e : Nat) (ht : t<64) (he : e<8) : aStoreAddress t e<640 := by
  have h := a_store_coordinates t e ht he
  unfold aStoreAddress
  omega

theorem a_store_owner (t e : Nat) (he : e<8) :
    aOwner (aStoreRow t) (aStoreCol t e)=t ∧ aStoreCol t e%8=e := by
  unfold aOwner aStoreRow aStoreCol
  omega

def bStoreRow (p : Shape) (t chunk : Nat) : Nat :=
  (t/32)*(256/tileN p)+(t%32)/(tileN p/8)+chunk*(512/tileN p)
def bStoreCol (p : Shape) (t e : Nat) : Nat := ((t%32)%(tileN p/8))*8+e
def bStoreAddress (p : Shape) (t chunk e : Nat) : Nat :=
  bStoreRow p t chunk*(tileN p+8)+bStoreCol p t e
def bOwner (p : Shape) (row col : Nat) : Nat :=
  ((row%(512/tileN p))/(256/tileN p))*32+
    ((row%(512/tileN p))%(256/tileN p))*(tileN p/8)+col/8
def bChunk (p : Shape) (row : Nat) : Nat := row/(512/tileN p)

theorem b_store_coordinates (p : Shape) (t chunk e : Nat)
    (ht : t<64) (hc : chunk<tileN p/16) (he : e<8) :
    bStoreRow p t chunk<32 ∧ bStoreCol p t e<tileN p := by
  rcases tile_cases p with hn | hn
  · simp only [bStoreRow,bStoreCol,hn] at *
    omega
  · simp only [bStoreRow,bStoreCol,hn] at *
    omega

theorem b_store_bound (p : Shape) (t chunk e : Nat)
    (ht : t<64) (hc : chunk<tileN p/16) (he : e<8) :
    bStoreAddress p t chunk e<32*(tileN p+8) := by
  have h := b_store_coordinates p t chunk e ht hc he
  rcases tile_cases p with hn | hn
  · simp only [bStoreAddress,hn] at *
    omega
  · simp only [bStoreAddress,hn] at *
    omega

theorem b_store_owner (p : Shape) (t chunk e : Nat)
    (ht : t<64) (he : e<8) :
    bOwner p (bStoreRow p t chunk) (bStoreCol p t e)=t ∧
      bChunk p (bStoreRow p t chunk)=chunk ∧ bStoreCol p t e%8=e := by
  rcases tile_cases p with hn | hn
  · simp only [bOwner,bChunk,bStoreRow,bStoreCol,hn] at *
    omega
  · simp only [bOwner,bChunk,bStoreRow,bStoreCol,hn] at *
    omega

def aFragment (t half e : Nat) : Nat := (t%16)*40+half*16+(t/16)*4+e
def bFragment (p : Shape) (t half bank e : Nat) : Nat :=
  (half*16+(t/16)*4+e)*(tileN p+8)+bank*16+t%16

theorem a_fragment_bound (t half e : Nat) (ht : t<64) (hh : half<2) (he : e<4) :
    aFragment t half e<640 := by
  unfold aFragment
  omega

theorem a_fragment_source (row k half : Nat) (hr : row<16) :
    aFragment (LarkMFMA.aLane row k) half (k%4)=row*40+half*16+k := by
  unfold aFragment LarkMFMA.aLane
  omega

theorem b_fragment_bound (p : Shape) (t half bank e : Nat)
    (ht : t<64) (hh : half<2) (hb : bank<tileN p/16) (he : e<4) :
    bFragment p t half bank e<32*(tileN p+8) := by
  rcases tile_cases p with hn | hn
  · simp only [bFragment,hn] at *
    omega
  · simp only [bFragment,hn] at *
    omega

theorem b_fragment_source (p : Shape) (k col half bank : Nat) (hc : col<16) :
    bFragment p (LarkMFMA.bLane k col) half bank (k%4)=
      (half*16+k)*(tileN p+8)+bank*16+col := by
  have hcol : LarkMFMA.bLane k col%16=col := by unfold LarkMFMA.bLane; omega
  have hk' : half*16+(LarkMFMA.bLane k col/16)*4+k%4=half*16+k := by
    unfold LarkMFMA.bLane
    omega
  simp only [bFragment,hcol,hk']

def outputLocalCol (t bank : Nat) : Nat := bank*16+t%16
def outputOwner (row col : Nat) : Nat := row/4*16+col%16

theorem output_coordinates (p : Shape) (t bank e : Nat)
    (ht : t<64) (hb : bank<tileN p/16) (he : e<4) :
    LarkMFMA.outputRow t e<16 ∧ outputLocalCol t bank<tileN p := by
  rcases tile_cases p with hn | hn
  · simp only [LarkMFMA.outputRow,outputLocalCol,hn] at *
    omega
  · simp only [LarkMFMA.outputRow,outputLocalCol,hn] at *
    omega

theorem output_owner (t bank e : Nat) (he : e<4) :
    outputOwner (LarkMFMA.outputRow t e) (outputLocalCol t bank)=t ∧
      outputLocalCol t bank/16=bank ∧ LarkMFMA.outputRow t e%4=e := by
  unfold outputOwner LarkMFMA.outputRow outputLocalCol
  omega

#print axioms tile_cases
#print axioms tile_aligned
#print axioms column_tiles_positive
#print axioms columns_exact
#print axioms row_tiles_positive
#print axioms a_store_coordinates
#print axioms a_store_bound
#print axioms a_store_owner
#print axioms b_store_coordinates
#print axioms b_store_bound
#print axioms b_store_owner
#print axioms a_fragment_bound
#print axioms a_fragment_source
#print axioms b_fragment_bound
#print axioms b_fragment_source
#print axioms output_coordinates
#print axioms output_owner
end LarkNativeAwqGemm
