import TM63RootResidueThree
import M2EvenResidueSixteen
import Lean.Elab.Tactic.Omega

/-!
# Candidate authentic-root extension through middle row 16

The middle-15 endpoint has marker 2 and binary counter 16*r, where r is
the odd half-quotient from the exact first-section arithmetic. Since r is
odd, 16*r=32*k+16. This module composes the new source-exact m=2,
n=32*k+16 counted increment to reach the marker-1 successor.

This is a candidate finite blank-root prefix only. It is not a proof that
the champion halts, and it remains uncertified until the imported source
modules compile against the original machine and pass transitive axiom
audits.
-/

namespace BB6Coverage.Agent41TM63RootResidueZero

open BB6ChampionArithmetic
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent48TM63RootResidueThree
open BB6Coverage.Agent41M2EvenResidueSixteen

set_option maxHeartbeats 3000000

/-- The half of the odd middle quotient is itself odd. -/
private theorem tm63_root_residue6_half_odd :
    tm63RootResidueSixK % 2 = 1 := by
  have hA : 5 ≤ tm63FirstSection.exponent :=
    tm63FirstSection_exponent_ge_five
  have hE : 2 ≤ tm63FirstSection.exponent-3 := by omega
  obtain ⟨t,ht⟩ :=
    Nat.exists_eq_add_of_le hE
  have hpow4 :
      (2^(tm63FirstSection.exponent-3)) % 4 = 0 := by
    rw [ht,Nat.pow_add]
    norm_num [Nat.mul_mod]
  have hprodMod :
      (31*2^(tm63FirstSection.exponent-3)) % 4 = 0 := by
    simp [Nat.mul_mod,hpow4]
  have hprodPos :
      0 < 31*2^(tm63FirstSection.exponent-3) := by
    positivity
  have hdiv :
      31*2^(tm63FirstSection.exponent-3) =
        4*(31*2^(tm63FirstSection.exponent-3)/4) := by
    have hh := Nat.mod_add_div
      (31*2^(tm63FirstSection.exponent-3)) 4
    rw [hprodMod] at hh
    omega
  have hqpos :
      0 < 31*2^(tm63FirstSection.exponent-3)/4 := by omega
  have hkform :
      tm63RootMiddleK =
        4*(31*2^(tm63FirstSection.exponent-3)/4-1)+3 := by
    unfold tm63RootMiddleK
    rw [hdiv]
    omega
  have hhalf :
      tm63RootMiddleK/2 =
        2*(31*2^(tm63FirstSection.exponent-3)/4-1)+1 := by
    rw [hkform]
    omega
  dsimp [tm63RootResidueSixK]
  rw [hhalf]
  omega

/-- Split the odd quotient into twice the new row parameter plus one. -/
def tm63RootResidueZeroK : Nat :=
  tm63RootResidueSixK / 2

private theorem tm63_root_residue6_split :
    tm63RootResidueSixK = 2*tm63RootResidueZeroK+1 := by
  have h := Nat.mod_add_div tm63RootResidueSixK 2
  rw [tm63_root_residue6_half_odd] at h
  dsimp [tm63RootResidueZeroK]
  omega

private theorem tm63_root_length_ge_five :
    5 ≤ tm63Length1 := by
  have hA := tm63FirstSection_exponent_ge_five
  dsimp [tm63Length1]
  omega

private theorem tm63_root_residue0_bound :
    32*tm63RootResidueZeroK+16 < 2^tm63Length1 := by
  have hroot := tm63_index1_lt_pow_length1
  have hindex : tm63Index1 = 16*tm63RootResidueSixK+15 := by
    simpa [tm63RootResidueSixK] using tm63_index1_eq_16k15
  rw [tm63_root_residue6_split] at hindex
  have hsmall :
      32*tm63RootResidueZeroK+16 < tm63Index1 := by
    rw [hindex]
    omega
  exact lt_trans hsmall hroot

private theorem tm63_middle_after15_a_pos :
    0 < tm63MiddleAfter15A := by
  simp [tm63MiddleAfter15A]

/-- Endpoint after the m=2,n=16*r counted increment. -/
def tm63MiddleAfter16A : Nat :=
  tm63MiddleAfter15A+tm63MiddleAfter15B+2

def tm63MiddleAfter16B : Nat :=
  2^tm63MiddleAfter15B-1

def tm63MiddleAfter16Head : Int :=
  tm63MiddleAfter15Head+5+3*tm63MiddleAfter15B

/-- Exact cumulative source-run length through the m=2,n=16*r row. -/
def tm63MiddleFirst16Moves : Nat :=
  tm63MiddleFirst15Moves+
    proposedIncrementCost 2 (16*tm63RootResidueSixK)
      tm63MiddleAfter15A tm63MiddleAfter15B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate blank-root original-machine prefix through middle row 16. -/
theorem tm63_blank_reaches_after_middle16 :
    run tm2 tm63MiddleFirst16Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-1) 1
        tm63MiddleAfter16A 0 tm63MiddleAfter16B
        tm63MiddleAfter16Head) := by
  have hsplit := tm63_root_residue6_split
  have hn :
      32*tm63RootResidueZeroK+16 =
        16*tm63RootResidueSixK := by omega
  have htarget :
      32*tm63RootResidueZeroK+15 =
        16*tm63RootResidueSixK-1 := by omega
  have hrow := m2Even_residue16_counted_increment_source
    tm63Length1 tm63RootResidueZeroK
    tm63MiddleAfter15A tm63MiddleAfter15B tm63MiddleAfter15Head
    tm63_root_length_ge_five tm63_root_residue0_bound
    tm63_middle_after15_a_pos
  have hrow' :
      run tm2
        (proposedIncrementCost 2 (16*tm63RootResidueSixK)
          tm63MiddleAfter15A tm63MiddleAfter15B)
        (s1Config tm63Length1 (16*tm63RootResidueSixK) 2
          tm63MiddleAfter15A 0 tm63MiddleAfter15B tm63MiddleAfter15Head) =
      some (s1Config tm63Length1 (16*tm63RootResidueSixK-1) 1
        tm63MiddleAfter16A 0 tm63MiddleAfter16B tm63MiddleAfter16Head) := by
    simpa [hn,htarget,tm63MiddleAfter16A,tm63MiddleAfter16B,
      tm63MiddleAfter16Head] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle15 hrow'
  simpa [tm63MiddleFirst16Moves] using hcomp

#print axioms tm63_root_residue6_half_odd
#print axioms tm63_root_residue0_bound
#print axioms tm63_blank_reaches_after_middle16

end BB6Coverage.Agent41TM63RootResidueZero
