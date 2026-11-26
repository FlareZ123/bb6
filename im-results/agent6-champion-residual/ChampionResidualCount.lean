import RootedFrontierCount

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent6ChampionResidualCount

open BB6.Agent31FourHoleFrontier

/-- Number of explicitly closed ordinary leaves in a rooted frontier. -/
def frontierClosedLeaves {B : Nat} {p : PartialMachine} :
    RootedFrontier B p → Nat
  | .residual _ => 0
  | .closed _ _ => 1
  | .expand _ _ _ _ children =>
      (allMoves.map fun mv => frontierClosedLeaves (children mv)).sum

/-- Number of expanded first-hole nodes in a rooted frontier. -/
def frontierExpandedNodes {B : Nat} {p : PartialMachine} :
    RootedFrontier B p → Nat
  | .residual _ => 0
  | .closed _ _ => 0
  | .expand _ _ _ _ children =>
      1 + (allMoves.map fun mv => frontierExpandedNodes (children mv)).sum

private theorem sum_map_add {α : Type} (xs : List α) (f g : α → Nat) :
    (xs.map f).sum + (xs.map g).sum =
      (xs.map (fun x => f x + g x)).sum := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      omega

private theorem sum_map_mul_add_one {α : Type} (xs : List α) (f : α → Nat) :
    (xs.map (fun x => 23 * f x + 1)).sum =
      23 * (xs.map f).sum + xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [ih]
      omega

/-- Every full 24-way expansion contributes exactly 23 residual-or-closed
    leaves per expanded node, plus its single root leaf. -/
theorem residuals_closed_expanded {B : Nat} {p : PartialMachine}
    (frontier : RootedFrontier B p) :
    (residuals frontier).length + frontierClosedLeaves frontier =
      23 * frontierExpandedNodes frontier + 1 := by
  induction frontier with
  | residual path =>
      simp [residuals, frontierClosedLeaves, frontierExpandedNodes]
  | closed path cert =>
      simp [residuals, frontierClosedLeaves, frontierExpandedNodes]
  | @expand p n c path hrun hhole hweight children ih =>
      let f := fun mv : Move => (residuals (children mv)).length
      let g := fun mv : Move => frontierClosedLeaves (children mv)
      let h := fun mv : Move => frontierExpandedNodes (children mv)
      have hsum :
          (allMoves.map (fun mv => f mv + g mv)).sum =
            (allMoves.map (fun mv => 23 * h mv + 1)).sum := by
        apply congrArg List.sum
        apply List.map_congr_left
        intro mv hmem
        exact ih mv
      have hlen :
          (residuals (.expand path hrun hhole hweight children)).length =
            (allMoves.map f).sum := by
        simp [residuals, f, List.length_flatMap, List.length_map]
      rw [hlen]
      change (allMoves.map f).sum + (allMoves.map g).sum =
        23 * (1 + (allMoves.map h).sum) + 1
      calc
        (allMoves.map f).sum + (allMoves.map g).sum =
            (allMoves.map (fun mv => f mv + g mv)).sum :=
          sum_map_add allMoves f g
        _ = (allMoves.map (fun mv => 23 * h mv + 1)).sum := hsum
        _ = 23 * (allMoves.map h).sum + allMoves.length :=
          sum_map_mul_add_one allMoves h
        _ = 23 * (1 + (allMoves.map h).sum) + 1 := by
          rw [allMoves_length]
          omega

#print axioms residuals_closed_expanded

end BB6.Agent6ChampionResidualCount
