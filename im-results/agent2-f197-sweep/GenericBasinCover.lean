import GenericBasin
import CoverBridge

namespace F197.CoverBridge
open BB6Coverage (Machine compatible)

/-- All 25 legal completions of F197's missing C1 transition inherit the
    source-certified generic-epoch infinite basin, uniformly for any finite
    aligned rope with positive head and every k>=45. -/
theorem original_generic_odd_basin_live
    (m : Machine) (hm : compatible table m)
    (c : BB6Coverage.Config)
    (k : Nat) (Y : F197.Agent2Counter.Word) (r : F197.Agent2Self.Rope)
    (hk : 45 ≤ k) (hr : F197.Agent2Self.ropeOK r = true)
    (hY : F197.Agent2Self.okHead Y = true)
    (hc : Related c
      (F197.Agent2Self.rstate (2*(2*k+2)+1)
        (F197.Agent2Self.M++F197.Agent2Self.GS++Y) r)) :
    ∀ t : Nat, BB6Coverage.run m t c ≠ none := by
  intro t
  have hn := F197.Agent2Self.generic_odd_basin_live k Y r hk hr hY t
  cases hs : F197.run t
      (F197.Agent2Self.rstate (2*(2*k+2)+1)
        (F197.Agent2Self.M++F197.Agent2Self.GS++Y) r) with
  | none => exact False.elim (hn hs)
  | some v =>
    obtain ⟨d,hd,_⟩ := run_related m hm t c _ v hc hs
    simp [hd]

#print axioms original_generic_odd_basin_live
end F197.CoverBridge
