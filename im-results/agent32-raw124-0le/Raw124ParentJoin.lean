import ResidualCover
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent32Raw124ParentJoin
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent16ResidualCover

abbrev parent124 : PartialMachine :=
  refine (pathEnd root 2 (path.take 4)).1 (4,true) (some ⟨true,false,5⟩)
abbrev child (mv : Move) : PartialMachine := refine parent124 (5,true) (some mv)

theorem first_query : zipQueryOK 13 parent124 7 (5,true) = true := by decide
theorem root_first : parent124 initialSlot = some (some ⟨true,true,1⟩) := by decide

theorem root_halt (m : Machine) (hm : compatible parent124 m) (hh : m (5,true) = none) :
    WeightedBound 13 m := by
  obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound first_query
  cases hr : knownRun parent124 7 with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = (5,true) := by simpa [hr] using hread
    have hc : compatible (refine parent124 (5,true) none) m := by
      simpa [hh] using BB6Coverage.compatible_refine parent124 m (5,true) hm
    exact first_hole_weighted_halt 13 parent124 7 c root_first hr
      (by simpa [hs] using hhole)
      (by simpa [hs] using weightOK_sound parent124 (5,true) 7 13 hw) m
      (by simpa [hs] using hc)

/-- The exact 25-way first query; no unproved certificate can discharge a child. -/
theorem cover_of_children (B : Nat) (hB : 13 ≤ B)
    (hc : ∀ mv, ∀ m, compatible (child mv) m → WeightedBound B m) :
    Cover (WeightedBound B) parent124 := by
  apply Cover.leaf
  intro m hm
  cases ht : m (5,true) with
  | none =>
    exact fun k d hk hd => Nat.le_trans (root_halt m hm ht k d hk hd) hB
  | some mv =>
    exact hc mv m (by simpa [child,ht] using BB6Coverage.compatible_refine parent124 m (5,true) hm)

def liftAccepted {A B : Nat} (h : A ≤ B) (p : PartialMachine)
    (hb : ∀ m, compatible p m → WeightedBound A m) : Accepted B :=
  ⟨p,fun m hm k d hk hd => Nat.le_trans (hb m hm k d hk hd) h⟩

theorem cover_of_accepted {B : Nat} (hB : 13 ≤ B) (as : List (Accepted B))
    (h : allMoves (fun mv => covered as (child mv)) = true) : Cover (WeightedBound B) parent124 :=
  cover_of_children B hB (fun mv => covered_sound (allMoves_sound _ h mv))

#print axioms root_halt
#print axioms cover_of_children
#print axioms cover_of_accepted
end BB6.Agent32Raw124ParentJoin
