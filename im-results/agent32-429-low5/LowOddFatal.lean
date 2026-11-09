import LowOddPhysical
import W5FatalMidA
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429LowOddFatal
open BB6Coverage BB6Bubble BB429PhysicalFrontier BB429JPhysical
open BB429High3Ladder BB429FirstGateRays BB429FirstGateRaw
open BB429FirstGateMidA BB429LowOddPhysical

/-- The low-odd output has exactly three high3 branches before its fatal
    boundary for the affine seed v=15n+63. -/
def seedV (n : Nat) : Nat := 15*n+63

theorem seed_matches_fatal_ancestor (n : Nat) :
    4*seedV n+2 = anc (2*n+6) 3 := by
  have h := anc_formula (2*n+6) 3 (by omega)
  have hp : (2:Nat)^3=8 := by decide
  rw [hp] at h
  dsimp [seedV]
  omega

/-- Infinite family of genuine-original-table *synthetic prepared tapes*
    that pass through a parametric deficit-(4n+5) low branch,
    three high-three branches, and the fatal C/D gate.
    This does not assert that any of these tapes arises from blank tape. -/
theorem raw_lowodd_then_three_high_fatal (n : Nat) :
    BB6Coverage.run target429
      ((4*(seedV n)*(seedV n)+22*(seedV n)+22*n+100) +
        (branchCostSum (2*n+6) 3 + branchCost (branchU (2*n+6) 3)))
      (jConfig (17*n+66) (30*n+127)) = none := by
  let v : Nat := seedV n
  have hu : v+2*n+3=17*n+66 := by dsimp [v,seedV]; omega
  have hw : 2*v+1=30*n+127 := by dsimp [v,seedV]; omega
  have hinput : jConfig (17*n+66) (30*n+127) =
      {state:=A,head:=0,tape:=jTape (v+2*n+3) (2*v+1)} := by
    simp only [jConfig,hu,hw]
  obtain ⟨c',hpre,hrep,_⟩ := lowOdd_raw_head v n
  have hanc : 4*v+2=anc (2*n+6) 3 := by
    simpa only [v] using seed_matches_fatal_ancestor n
  have hraw : BB6Coverage.run target429
      (branchCostSum (2*n+6) 3+branchCost (branchU (2*n+6) 3))
      (jConfig (2*n+6) (4*v+2)) = none := by
    rw [hanc]
    exact raw_fatal_anc (2*n+6) 3 (by omega)
  have hpost := represented_junc_halts (2*n+6) (4*v+2)
      (branchCostSum (2*n+6) 3+branchCost (branchU (2*n+6) 3))
      c' hrep hraw
  rw [hinput,BB6Bubble.run_add',hpre]
  exact hpost

#print axioms seed_matches_fatal_ancestor
#print axioms raw_lowodd_then_three_high_fatal
end BB429LowOddFatal
