import Q4Suffix
import Lean.Elab.Tactic.Omega

/-!
# Binary interfaces for the m=1, n=8*q+1 q4 source row

These lemmas isolate the low-order source/target words and the q4
suffix's exact target-left identity.  The source q4 prefix and its
arbitrary-width half-line lift are separate obligations.
-/

namespace BB6Coverage.Agent48M1OddResidueOneTargetLeft

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8Q4Suffix

/-- Low-three-bit expansion for the marker-1 residue-one source. -/
theorem binDec_residue1 (L q : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+1 < 2^L) :
    binDec L (8*q+1) =
      d0 ++ d1 ++ d1 ++ binDec (L-3) q := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    rw [show L = (L-3)+3 by omega, Nat.pow_add]
    simp [show (2:Nat)^3 = 8 by decide, Nat.mul_comm]
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    rw [show L-1 = (L-3)+2 by omega, Nat.pow_add]
    simp [show (2:Nat)^2 = 4 by decide, Nat.mul_comm]
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    rw [show L-2 = (L-3)+1 by omega, Nat.pow_add]
    simp [show (2:Nat)^1 = 2 by decide, Nat.mul_comm]
  have hk : q < 2^(L-3) := by rw [hpow3] at hbound; omega
  have hq1 : 4*q < 2^(L-1) := by
    rw [hpow2]
    rw [hpow3] at hbound
    omega
  have hq2 : 2*q < 2^(L-2) := by
    rw [hpow1]
    rw [hpow3] at hbound
    omega
  have h1 : binDec L (8*q+1) =
      d0 ++ binDec (L-1) (4*q) := by
    rw [show L = (L-1)+1 by omega,
      show 8*q+1 = 2*(4*q)+1 by omega]
    exact binDec_odd (L-1) (4*q) hq1
  have h2 : binDec (L-1) (4*q) =
      d1 ++ binDec (L-2) (2*q) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*q = 2*(2*q) by omega]
    exact binDec_even (L-2) (2*q) hq2
  have h3 : binDec (L-2) (2*q) =
      d1 ++ binDec (L-3) q := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_even (L-3) q hk
  rw [h1,h2,h3]
  simp [List.append_assoc]

/-- Low-three-bit expansion for the marker-0 successor n=8*q. -/
theorem binDec_residue0 (L q : Nat) (hL : 3 ≤ L)
    (hbound : 8*q < 2^L) :
    binDec L (8*q) =
      d1 ++ d1 ++ d1 ++ binDec (L-3) q := by
  have hpow3 : 2^L = 8 * 2^(L-3) := by
    rw [show L = (L-3)+3 by omega, Nat.pow_add]
    simp [show (2:Nat)^3 = 8 by decide, Nat.mul_comm]
  have hpow2 : 2^(L-1) = 4 * 2^(L-3) := by
    rw [show L-1 = (L-3)+2 by omega, Nat.pow_add]
    simp [show (2:Nat)^2 = 4 by decide, Nat.mul_comm]
  have hpow1 : 2^(L-2) = 2 * 2^(L-3) := by
    rw [show L-2 = (L-3)+1 by omega, Nat.pow_add]
    simp [show (2:Nat)^1 = 2 by decide, Nat.mul_comm]
  have hk : q < 2^(L-3) := by
    rw [hpow3] at hbound
    omega
  have hq1 : 4*q < 2^(L-1) := by
    rw [hpow2]
    omega
  have hq2 : 2*q < 2^(L-2) := by
    rw [hpow1]
    omega
  have h1 : binDec L (8*q) =
      d1 ++ binDec (L-1) (4*q) := by
    rw [show L = (L-1)+1 by omega,
      show 8*q = 2*(4*q) by omega]
    exact binDec_even (L-1) (4*q) hq1
  have h2 : binDec (L-1) (4*q) =
      d1 ++ binDec (L-2) (2*q) := by
    rw [show L-1 = (L-2)+1 by omega,
      show 4*q = 2*(2*q) by omega]
    exact binDec_even (L-2) (2*q) hq2
  have h3 : binDec (L-2) (2*q) =
      d1 ++ binDec (L-3) q := by
    rw [show L-2 = (L-3)+1 by omega]
    exact binDec_even (L-3) q hk
  rw [h1,h2,h3]
  simp [List.append_assoc]

/-- The q4 cut word at the original head for the m=1, n=8*q+1 row. -/
def m1OddResidueOneLeftFacing (L q a : Nat) : List Bool :=
  [true] ++ d1pow a ++ markerWord 0 ++
    d0 ++ d1 ++ d1 ++ d1 ++ binDec (L-3) q ++ lh

/-- The generic q4 suffix transforms this cut word into the exact
m=0,n=8*q target left-facing stream. -/
theorem m1OddResidueOneSuffixTargetLeft
    (L q a b : Nat) (hL : 3 ≤ L)
    (hbound : 8*q+1 < 2^L) :
    s1LeftFacing L (8*q) 0 (a+b+2) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m1OddResidueOneLeftFacing L q a).drop 1 := by
  have hbin := binDec_pow2_sub_one a b
  have hbin0 : binDec L (8*q) =
      d1 ++ d1 ++ d1 ++ binDec (L-3) q :=
    binDec_residue0 L q hL (by omega)
  unfold s1LeftFacing m1OddResidueOneLeftFacing
  rw [hbin,hbin0]
  rw [d1pow_add_right a 2]
  simp [List.drop,List.append_assoc]

#print axioms binDec_residue1
#print axioms binDec_residue0
#print axioms m1OddResidueOneSuffixTargetLeft

end BB6Coverage.Agent48M1OddResidueOneTargetLeft
