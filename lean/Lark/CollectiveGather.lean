import Lark.Collective

/-! A generic register-read decomposition of the unchanged snapshot shuffle. -/
namespace LarkCollective.Gather
open LarkNonlinear
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

def readValue (g : Geometry) (ts : List Nat) (s : State α) (kind : ShuffleKind)
    (src : Nat) (selector : Index) (width t : Nat) : Option (Nat × α) := do
  let arg ← evalIndex g t s selector
  if arg < 0 then none else do
    let lane := (t % g.block) % 64
    let selected ← sourceLane kind width lane arg.toNat
    let owner := (t / g.block) * g.block + ((t % g.block) / 64) * 64
    let source := owner + selected
    if !(ts.contains source) then none else do
      let v ← s.regs source src
      pure (t, v)

theorem values_eq (g : Geometry) (p : List Instr) (ts : List Nat) (s : State α)
    (first : Nat) (kind : ShuffleKind) (dest src : Nat) (selector : Index) (width : Nat)
    (guard : ¬ (g.warp ≠ 64 ∨ g.block % 64 ≠ 0 ∨ ts.length ≠ 64))
    (head : ts.head? = some first)
    (code : p[s.pc first]? = some (.shuffle kind dest src selector width)) :
    shuffleValues g p ts s =
      ((ts.mapM (readValue g ts s kind src selector width)).bind fun vs => some (dest, vs)) := by
  unfold shuffleValues
  rewrite [if_neg guard, head]
  simp only [bind, pure, Option.bind]
  rewrite [code]
  rfl

#print axioms values_eq
end LarkCollective.Gather
