import Raw39SemanticChunks
namespace BB6.Agent43Raw391LEBoundLift
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent11SemanticChunks

theorem mono {B C : Nat} {p : PartialMachine} (hBC : B ≤ C) (h : Bound B p) : Bound C p := by
  intro m hm k d hk hd
  exact Nat.le_trans (h m hm k d hk hd) hBC

#print axioms mono
end BB6.Agent43Raw391LEBoundLift
