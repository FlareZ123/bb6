import Agent49DrainDigitLengthBound
import Agent1SignedCoordinateNormalForm
import SourceDerivedReset

open BB6.Agent49DrainDigitLengthBound
open BB6.Agent1DrainDigitStatsSource
open BB6.Agent49ParitySource
open BB6.Agent1SignedCoordinateNormalForm
open BB6.SourceDerivedReset

namespace BB6.Agent24SourceDerivedResetBridge

/-- Translate the source cocycle's sector/branch pair to the finite
correction-table index used by the source-derived reset proof. -/
def sectorBranchOf : Sector → Branch → SectorBranch
  | .LO, .L => .LO_L
  | .LE, .L => .LE_L
  | .RO, .L => .RO_L
  | .RE, .L => .RE_L
  | .LO, .R => .LO_R
  | .LE, .R => .LE_R
  | .RO, .R => .RO_R
  | .RE, .R => .RE_R

/-- The reset proof's correction table is exactly the original signed
coordinate cocycle's C correction, for all eight sector/branch pairs. -/
theorem sourceCorrectionC_eq_corrC
    (s : Sector) (br : Branch) (D R : Int) :
    sourceCorrectionC (sectorBranchOf s br) D R = corrC s br D R := by
  cases s <;> cases br <;> rfl

/-- The reset proof's correction table is exactly the original signed
coordinate cocycle's F correction, for all eight sector/branch pairs. -/
theorem sourceCorrectionF_eq_corrF
    (s : Sector) (br : Branch) (D R : Int) :
    sourceCorrectionF (sectorBranchOf s br) D R = corrF s br D R := by
  cases s <;> cases br <;> rfl

/-- A root-mass bound b ≤ q+3, q ≤ S supplies the mass-indexed
source-drain correction bounds used by the source-derived reset lemma.
The separate hbudget premise is the authentic drainB recursion guard. -/
theorem drain_corrections_at_root_mass
    (q S b a d aa dd : Nat) (s : Sector) (br : Branch)
    (hqS : q ≤ S) (hb : b ≤ q + 3)
    (hbudget : b ≤ ternaryOnes a)
    (hdrain : drainB a b d = some (.D aa dd)) :
    ∃ r : Nat,
      (a : Int) - (aa : Int) =
        ((drainDigitSummary b).length : Int) -
          2 * ((drainDigitStats b).twos : Int) ∧
      2 * aa + dd = 2 * a + d + 3 * b + 2 * r ∧
      r = (drainDigitStats b).ones + (drainDigitStats b).twos ∧
      -(34 * (massIndex S : Int) + 122) ≤
        sourceCorrectionC (sectorBranchOf s br)
          ((a : Int) - (aa : Int)) (r : Int) ∧
      sourceCorrectionC (sectorBranchOf s br)
          ((a : Int) - (aa : Int)) (r : Int) ≤
        34 * (massIndex S : Int) + 122 ∧
      -(34 * (massIndex S : Int) + 122) ≤
        sourceCorrectionF (sectorBranchOf s br)
          ((a : Int) - (aa : Int)) (r : Int) ∧
      sourceCorrectionF (sectorBranchOf s br)
          ((a : Int) - (aa : Int)) (r : Int) ≤
        34 * (massIndex S : Int) + 122 := by
  have hmass : b ≤ ternaryOnes (massIndex S) :=
    rootDrainInput_mass_bound q S b hqS hb
  obtain ⟨hdrop, r, hweighted, hcount, hClo, hChi, hFlo, hFhi⟩ :=
    drainB_digit_source_correction_interface_mass
      b a d aa dd (massIndex S) s br hbudget hmass hdrain
  refine ⟨r, hdrop, hweighted, hcount, ?_, ?_, ?_, ?_⟩
  · rw [sourceCorrectionC_eq_corrC]
    exact hClo
  · rw [sourceCorrectionC_eq_corrC]
    exact hChi
  · rw [sourceCorrectionF_eq_corrF]
    exact hFlo
  · rw [sourceCorrectionF_eq_corrF]
    exact hFhi

#print axioms sourceCorrectionC_eq_corrC
#print axioms sourceCorrectionF_eq_corrF
#print axioms drain_corrections_at_root_mass

end BB6.Agent24SourceDerivedResetBridge
