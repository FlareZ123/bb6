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

/-- Exponential two-counter family for exactly 4t+3 high-three
    successors after the source-certified low-odd physical return. -/
def seedVT (n t : Nat) : Nat :=
  (2*n+9)*2^(4*t+3) - (n+3*t+9)

theorem seedVT_bound (n t : Nat) :
    n+3*t+9 ≤ (2*n+9)*2^(4*t+3) := by
  have hp : 4*t+4 ≤ 2^(4*t+3) := by
    simpa [show 4*t+3+1=4*t+4 by omega] using two_pow_ge (4*t+3)
  have hpos : 1 ≤ 2^(4*t+3) := by omega
  have h1 := Nat.mul_le_mul_left (2*n) hpos
  have h2 := Nat.mul_le_mul_left 9 hp
  rw [Nat.add_mul]
  omega

theorem seedVT_formula (n t : Nat) :
    seedVT n t + (n+3*t+9) = (2*n+9)*2^(4*t+3) := by
  dsimp [seedVT]
  exact Nat.sub_add_cancel (seedVT_bound n t)

theorem seedVT_anc (n t : Nat) :
    4*seedVT n t+2 = anc (2*n+6) (4*t+3) := by
  have ha := anc_formula (2*n+6) (4*t+3) (by omega)
  have hv := seedVT_formula n t
  have hmul : 4*((2*n+6)+3)*2^(4*t+3) =
      4*((2*n+9)*2^(4*t+3)) := by
    rw [show (2*n+6)+3=2*n+9 by omega]
    rw [Nat.mul_assoc]
  rw [hmul] at ha
  omega

/-- For arbitrary natural parameters n,t, the literal original #429
    machine starting at the fully specified, nonblank J tape first
    crosses a deficit-(4n+5) low branch and then exactly (4t+3)
    high-three branches to a fatal gate. No root reachability claim. -/
theorem raw_lowodd_then_high_fatal (n t : Nat) :
    BB6Coverage.run target429
      ((4*(seedVT n t)*(seedVT n t)+22*(seedVT n t)+22*n+100) +
        (branchCostSum (2*n+6) (4*t+3) +
          branchCost (branchU (2*n+6) (4*t+3))))
      (jConfig (seedVT n t+2*n+3) (2*(seedVT n t)+1)) = none := by
  let v : Nat := seedVT n t
  obtain ⟨c',hpre,hrep,_⟩ := lowOdd_raw_head v n
  have hanc : 4*v+2=anc (2*n+6) (4*t+3) := by
    simpa only [v] using seedVT_anc n t
  have hraw : BB6Coverage.run target429
      (branchCostSum (2*n+6) (4*t+3) +
        branchCost (branchU (2*n+6) (4*t+3)))
      (jConfig (2*n+6) (4*v+2)) = none := by
    rw [hanc]
    exact raw_fatal_anc (2*n+6) (4*t+3) (by omega)
  have hpost := represented_junc_halts (2*n+6) (4*v+2)
      (branchCostSum (2*n+6) (4*t+3) +
        branchCost (branchU (2*n+6) (4*t+3)))
      c' hrep hraw
  change BB6Coverage.run target429
      ((4*v*v+22*v+22*n+100) +
        (branchCostSum (2*n+6) (4*t+3) +
          branchCost (branchU (2*n+6) (4*t+3))))
      {state:=A,head:=0,tape:=jTape (v+2*n+3) (2*v+1)} = none
  rw [BB6Bubble.run_add',hpre]
  exact hpost

#print axioms seedVT_anc
#print axioms raw_lowodd_then_high_fatal

#print axioms seed_matches_fatal_ancestor
#print axioms raw_lowodd_then_three_high_fatal
end BB429LowOddFatal
