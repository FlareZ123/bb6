import RecursiveResidual
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent50Q2800
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50RootFrontier BB6.Agent50RecursiveResidual
def decodeRow (n : Nat) : Option (Option Move) :=
  if n = 0 then none else (allMoves[n-1]?).map some
def decodeRows (ns : List Nat) : PackedTable := ns.map decodeRow
structure ClosedTree where
  rows : List Nat
  tree : Tree
  checked : tree.check 400 (unpackTable (decodeRows rows)) = true
  closed : tree.packedResiduals (unpackTable (decodeRows rows)) = []
def ClosedTree.table (e : ClosedTree) : PartialMachine :=
  unpackTable (decodeRows e.rows)
theorem ClosedTree.sound (e : ClosedTree) (m : Machine) (hm : compatible e.table m) :
    WeightedBound 400 m := by
  rcases Tree.packed_sound 400 e.tree (unpackTable (decodeRows e.rows)) e.checked m hm with h | ⟨q,hq,_⟩
  · exact h
  · rw [e.closed] at hq
    simp at hq
#print axioms ClosedTree.sound
end BB6.Agent50Q2800
