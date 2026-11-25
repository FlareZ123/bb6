import Combined109Roster

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13CrossRouteHeldLeaf109

open BB6Coverage
open BB6.Agent50TNFPilot
open BB6.Agent31FourHoleRoster
open BB6.Agent47Combined109

/-- The depth-one first-one residual at B0=1LC:
    A0 is fixed by firstOneCylinder and this refines B0 to 1LC. -/
def firstOneB0_1LC : PartialMachine :=
  BB6Coverage.refine BB6.Agent50TNFPilot.root
    (⟨1, by decide⟩, false)
    (some ⟨true, false, ⟨2, by decide⟩⟩)

/-- This parent is not one of the fifteen already accepted whole-cylinder
    cuts (raw 66/70/80 and raw 86/87/88/91/92/93/97/98/100/101/102/104). -/
theorem firstOneB0_1LC_not_covered :
    BB6.Agent47Combined109.covered firstOneB0_1LC = false := by decide

/-- The B0=1LC parent is an actual member of the 109 residual roster,
    not an unrelated first-one branch. -/
theorem firstOneB0_1LC_in_reducedRoster :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster,
      BB6.Agent31FourHoleRoster.sameTable e.2 firstOneB0_1LC = true := by decide

/-- The roster entry is exactly this parent table, not merely a compatible
    intersection with it. -/
theorem firstOneB0_1LC_exact_member :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster,
      e.2 = firstOneB0_1LC := by
  obtain ⟨e, he, hsame⟩ := firstOneB0_1LC_in_reducedRoster
  exact ⟨e, he, BB6.Agent31FourHoleRoster.sameTable_sound hsame⟩

#print axioms firstOneB0_1LC_not_covered
#print axioms firstOneB0_1LC_in_reducedRoster
#print axioms firstOneB0_1LC_exact_member

end BB6.Agent13CrossRouteHeldLeaf109
