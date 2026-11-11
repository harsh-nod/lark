import Lark.NativeSoftmaxMaxWaveCount

/-! Source-ordered tree and leaf witnesses for the descending unguarded
maximum reduction. No associativity, commutativity or idempotence is assumed.
Overflowing lanes retain their self source and still apply the operation. -/
namespace LarkNativeSoftmax
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

def downTree (combine : α → α → α) (values : Nat → α) : Nat → Nat → α
  | 0,lane => values lane
  | n+1,lane => combine (downTree combine values n lane)
      (downTree combine values n (downPeer32 lane (downDistance n)))

theorem wave_values_tree (ops : LarkNonlinear.Ops α) (input : Nat → Nat → α)
    (row warp n lane : Nat) :
    waveValues ops input row warp n lane =
      downTree ops.max (fun lane => threadMaximum ops input row (warp*64+lane)) n lane := by
  induction n generalizing lane with
  | zero => rfl
  | succ n ih => simp only [waveValues,downTree,ih]

def downLeaves (n lane : Nat) : List Nat := downTree List.append (fun lane => [lane]) n lane

theorem down_leaves_zero : downLeaves 5 0 =
    [0,16,8,24,4,20,12,28,2,18,10,26,6,22,14,30,1,17,9,25,5,21,13,29,3,19,11,27,7,23,15,31] := by decide

theorem down_leaves_second : downLeaves 5 32 =
    [32,48,40,56,36,52,44,60,34,50,42,58,38,54,46,62,33,49,41,57,37,53,45,61,35,51,43,59,39,55,47,63] := by decide

theorem down_leaves_self (half : Nat) (hh : half < 2) :
    downLeaves 5 (half*32+31) = List.replicate 32 (half*32+31) := by
  have table : ∀ h : Fin 2, downLeaves 5 (h.val*32+31) = List.replicate 32 (h.val*32+31) := by decide
  exact table ⟨half,hh⟩

theorem down_leaves_cover (half : Nat) (hh : half < 2) :
    (downLeaves 5 (half*32)).length = 32 ∧ (downLeaves 5 (half*32)).Nodup ∧
      ∀ lane : Fin 64, lane.val ∈ downLeaves 5 (half*32) ↔ lane.val/32 = half := by
  have table : ∀ h : Fin 2,
      (downLeaves 5 (h.val*32)).length = 32 ∧ (downLeaves 5 (h.val*32)).Nodup ∧
        ∀ lane : Fin 64, lane.val ∈ downLeaves 5 (h.val*32) ↔ lane.val/32 = h.val := by decide
  exact table ⟨half,hh⟩

theorem first_wave_partial_tree (p : Shape) (ops : LarkNonlinear.Ops α) (input : Nat → Nat → α)
    (row warp half : Nat) (s : LarkNonlinear.State α) (hw : warp < 16) (hh : half < 2) :
    (firstWave p ops input row warp s).memory ⟨.shared,row,0,warp*2+half⟩ =
      some (downTree ops.max (fun lane => threadMaximum ops input row (warp*64+lane)) 5 (half*32)) := by
  rewrite [first_wave_partial p ops input row warp half s hw hh,wave_values_tree]
  rfl

#print axioms wave_values_tree
#print axioms down_leaves_zero
#print axioms down_leaves_second
#print axioms down_leaves_self
#print axioms down_leaves_cover
#print axioms first_wave_partial_tree
end LarkNativeSoftmax
