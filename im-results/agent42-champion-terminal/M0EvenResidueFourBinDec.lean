import S1Encoder
import Lean.Elab.Tactic.Omega

/-!
# Residue-four low-block decomposition for the S1 source encoder

For n = 8*q+4, the complemented binary counter begins d1,d1,d0.
This exposes the fixed left-facing frame needed by the M0-even residue-four
finite bridge, without making assumptions about the high tail.
-/

namespace BB6Coverage.Agent42M0EvenResidueFourBridge

open BB6Coverage.Agent8S1Encoder

/-- The first three BinDec blocks for the n = 8*q+4 residue. -/
theorem m0EvenFour_binDec_prefix (L q : Nat)
    (hL : 3 ≤ L) (hq : 8*q+4 < 2^L) :
    binDec L (8*q+4) =
      d1 ++ d1 ++ d0 ++ binDec (L-3) q := by
  have hL1 : (L-1)+1 = L := by omega
  have hL2 : (L-2)+1 = L-1 := by omega
  have hL3 : (L-3)+1 = L-2 := by omega
  have hq1 : 4*q+2 < 2^(L-1) := by
    rw [← hL1, Nat.pow_succ] at hq
    omega
  have hq2 : 2*q+1 < 2^(L-2) := by
    rw [← hL2, Nat.pow_succ] at hq1
    omega
  have hq3 : q < 2^(L-3) := by
    rw [← hL3, Nat.pow_succ] at hq2
    omega
  have hmul1 : 2*(4*q+2) = 8*q+4 := by omega
  have hmul2 : 2*(2*q+1) = 4*q+2 := by omega
  have h1 :
      binDec L (8*q+4) =
        d1 ++ binDec (L-1) (4*q+2) := by
    simpa only [hL1, hmul1] using
      (binDec_even (L-1) (4*q+2) hq1)
  have h2 :
      binDec (L-1) (4*q+2) =
        d1 ++ binDec (L-2) (2*q+1) := by
    simpa only [hL2, hmul2] using
      (binDec_even (L-2) (2*q+1) hq2)
  have h3 :
      binDec (L-2) (2*q+1) =
        d0 ++ binDec (L-3) q := by
    simpa only [hL3] using
      (binDec_odd (L-3) q hq3)
  rw [h1, h2, h3]

/-- The full S1 left-facing source word after exposing the residue-four
low blocks. The arbitrary high tail remains packaged as BinDec (L-3) q. -/
theorem m0EvenFour_s1LeftFacing (L q a : Nat)
    (hL : 3 ≤ L) (hq : 8*q+4 < 2^L) :
    s1LeftFacing L (8*q+4) 0 a 0 =
      d1pow a ++ markerWord 0 ++ d0 ++ d1 ++ d1 ++ d0 ++
        binDec (L-3) q ++ lh := by
  simp [s1LeftFacing, binDec_zero, m0EvenFour_binDec_prefix,
    List.append_assoc]

#print axioms m0EvenFour_binDec_prefix
#print axioms m0EvenFour_s1LeftFacing

end BB6Coverage.Agent42M0EvenResidueFourBridge
