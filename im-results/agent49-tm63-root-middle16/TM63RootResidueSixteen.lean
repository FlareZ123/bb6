import TM63RootResidueThree
import M2EvenResidueSixteen
import M1OddResidueSeven
import Lean.Elab.Tactic.Omega

/-!
# Authentic-root composition through TM63 middle row 16

This composes the candidate middle-15 endpoint with the new generic
m=2, n=32*k+16 counted source increment.  The root parameter is
n=16*r with r odd; the oddness follows from the exact formula
tm63RootMiddleK = 31*2^(A-3)-1 and A>=5.

Status: source-level root composition candidate.  It is not compiled
and depends on the still-uncompiled middle-15 and residue-16 source
modules.  No BB(6) score or halting claim is made.
-/

namespace BB6Coverage.Agent49TM63RootResidueSixteen

open BB6Coverage
open BB6ChampionArithmetic
open BB6Coverage.Agent42RootAttainable
open BB6Coverage.Agent42RootCountdown
open BB6Coverage.Agent42RootResidueSix
open BB6Coverage.Agent8TM63RootResidueFour
open BB6Coverage.Agent48TM63RootResidueThree
open BB6Coverage.Agent41M2EvenResidueSixteen

private theorem four_dvd_pow_two (n : Nat) (hn : 2 ≤ n) :
    4 ∣ 2^n := by
  have heq : n = (n-2)+2 := by omega
  refine ⟨2^(n-2), ?_⟩
  rw [heq, Nat.pow_add]
  norm_num [Nat.mul_comm]

/-- The middle-15 quotient r is odd, so n=16*r has the form 32*k+16. -/
theorem tm63_root_residue16_r_odd :
    tm63RootResidueSixK % 2 = 1 := by
  have hA : 5 ≤ tm63FirstSection.exponent :=
    tm63FirstSection_exponent_ge_five
  have hpow : 4 ∣ 2^(tm63FirstSection.exponent-3) :=
    four_dvd_pow_two (tm63FirstSection.exponent-3) (by omega)
  obtain ⟨q,hq⟩ := hpow
  have hprod : 4 ∣ 31*2^(tm63FirstSection.exponent-3) := by
    refine ⟨31*q, ?_⟩
    rw [hq]
    ring
  have hmodBase :
      (31*2^(tm63FirstSection.exponent-3)) % 4 = 0 :=
    Nat.mod_eq_zero_of_dvd hprod
  have hmod : tm63RootMiddleK % 4 = 3 := by
    unfold tm63RootMiddleK
    omega
  have hsplit :
      tm63RootMiddleK = 4*(tm63RootMiddleK/4)+3 := by
    have h := Nat.mod_add_div tm63RootMiddleK 4
    rw [hmod] at h
    omega
  have hhalf :
      tm63RootMiddleK/2 = 2*(tm63RootMiddleK/4)+1 := by
    omega
  change (tm63RootMiddleK/2) % 2 = 1
  rw [hhalf]
  omega

private theorem tm63_root_residue16_split :
    tm63RootResidueSixK =
      2*(tm63RootResidueSixK/2)+1 := by
  have hodd := tm63_root_residue16_r_odd
  have h := Nat.mod_add_div tm63RootResidueSixK 2
  rw [hodd] at h
  omega

private theorem tm63_root_length_ge_five : 5 ≤ tm63Length1 := by
  have hA := tm63FirstSection_exponent_ge_five
  have hL :
      tm63Length1 = tm63FirstSection.exponent+5 := by
    dsimp [tm63Length1]
    omega
  omega

private theorem tm63_root_residue16_bound :
    32*(tm63RootResidueSixK/2)+16 < 2^tm63Length1 := by
  have hroot := tm63_index1_lt_pow_length1
  rw [tm63_root_index_eq_16r15] at hroot
  rw [tm63_root_residue16_split] at hroot
  omega

private theorem tm63_middle_after15_a_pos :
    0 < tm63MiddleAfter15A := by
  unfold tm63MiddleAfter15A
  omega

/-- Exact parameters after the m=2, n=16*r counted increment. -/
def tm63MiddleAfter16A : Nat :=
  tm63MiddleAfter15A+tm63MiddleAfter15B+2

def tm63MiddleAfter16B : Nat :=
  2^tm63MiddleAfter15B-1

def tm63MiddleAfter16Head : Int :=
  tm63MiddleAfter15Head+5+3*tm63MiddleAfter15B

def tm63MiddleFirst16Moves : Nat :=
  tm63MiddleFirst15Moves +
    proposedIncrementCost 2 (16*tm63RootResidueSixK)
      tm63MiddleAfter15A tm63MiddleAfter15B

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add,h1]
  simp only [Option.bind_some]
  exact h2

/-- Candidate authentic blank-root source prefix through middle row 16.
The only new transition is the generic m=2, n=32*k+16 counted row
instantiated at k=tm63RootResidueSixK/2. -/
theorem tm63_blank_reaches_after_middle16 :
    run tm2 tm63MiddleFirst16Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-1) 1
        tm63MiddleAfter16A 0 tm63MiddleAfter16B
        tm63MiddleAfter16Head) := by
  have hsplit := tm63_root_residue16_split
  have hinput :
      32*(tm63RootResidueSixK/2)+16 =
        16*tm63RootResidueSixK := by
    rw [hsplit]
    omega
  have htarget :
      32*(tm63RootResidueSixK/2)+15 =
        16*tm63RootResidueSixK-1 := by
    rw [hsplit]
    omega
  have hrow := m2Even_residue16_counted_increment_source
    tm63Length1 (tm63RootResidueSixK/2)
    tm63MiddleAfter15A tm63MiddleAfter15B tm63MiddleAfter15Head
    tm63_root_length_ge_five tm63_root_residue16_bound
    tm63_middle_after15_a_pos
  have hrow' :
      run tm2
        (proposedIncrementCost 2 (16*tm63RootResidueSixK)
          tm63MiddleAfter15A tm63MiddleAfter15B)
        (s1Config tm63Length1 (16*tm63RootResidueSixK) 2
          tm63MiddleAfter15A 0 tm63MiddleAfter15B
          tm63MiddleAfter15Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-1) 1
        (tm63MiddleAfter15A+tm63MiddleAfter15B+2) 0
        (2^tm63MiddleAfter15B-1)
        (tm63MiddleAfter15Head+5+3*tm63MiddleAfter15B)) := by
    simpa [hinput,htarget] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle15 hrow'
  simpa [tm63MiddleFirst16Moves,tm63MiddleAfter16A,
    tm63MiddleAfter16B,tm63MiddleAfter16Head] using hcomp


/-! The next marker-one odd row is also root-compatible: with r=2k+1,
16*r-1 = 8*(4*k+1)+7.  This is the exact input family of
Agent 41's m=1, n=8*q+7 source theorem. -/

def tm63RootResidueSixteenQ : Nat :=
  4*(tm63RootResidueSixK/2)+1

private theorem tm63_root_residue16_m1_bound :
    8*tm63RootResidueSixteenQ+7 < 2^tm63Length1 := by
  have hroot := tm63_index1_lt_pow_length1
  rw [tm63_root_index_eq_16r15] at hroot
  have hsplit := tm63_root_residue16_split
  dsimp [tm63RootResidueSixteenQ]
  rw [hsplit]
  omega

private theorem tm63_middle_after16_a_pos :
    0 < tm63MiddleAfter16A := by
  unfold tm63MiddleAfter16A
  omega

/-- Exact parameters after the m=1, n=16*r-1 counted increment. -/
def tm63MiddleAfter17A : Nat :=
  tm63MiddleAfter16A+tm63MiddleAfter16B+2

def tm63MiddleAfter17B : Nat :=
  2^tm63MiddleAfter16B-1

def tm63MiddleAfter17Head : Int :=
  tm63MiddleAfter16Head+5+3*tm63MiddleAfter16B

def tm63MiddleFirst17Moves : Nat :=
  tm63MiddleFirst16Moves +
    proposedIncrementCost 1 (16*tm63RootResidueSixK-1)
      tm63MiddleAfter16A tm63MiddleAfter16B

/-- Candidate authentic blank-root source prefix through middle row 17.
The m=1,n=8*q+7 row is instantiated at q=4*k+1 after the
m=2,n=32*k+16 row. -/
theorem tm63_blank_reaches_after_middle17 :
    run tm2 tm63MiddleFirst17Moves blank =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-2) 0
        tm63MiddleAfter17A 0 tm63MiddleAfter17B
        tm63MiddleAfter17Head) := by
  have hsplit := tm63_root_residue16_split
  have hinput :
      8*tm63RootResidueSixteenQ+7 =
        16*tm63RootResidueSixK-1 := by
    dsimp [tm63RootResidueSixteenQ]
    rw [hsplit]
    omega
  have htarget :
      8*tm63RootResidueSixteenQ+6 =
        16*tm63RootResidueSixK-2 := by
    dsimp [tm63RootResidueSixteenQ]
    rw [hsplit]
    omega
  have hrow := m1ResidueSeven_counted_increment_source_symbolic
    tm63Length1 tm63RootResidueSixteenQ
    tm63MiddleAfter16A tm63MiddleAfter16B tm63MiddleAfter16Head
    tm63_root_length_ge_five tm63_root_residue16_m1_bound
    tm63_middle_after16_a_pos
  have hrow' :
      run tm2
        (proposedIncrementCost 1 (16*tm63RootResidueSixK-1)
          tm63MiddleAfter16A tm63MiddleAfter16B)
        (s1Config tm63Length1 (16*tm63RootResidueSixK-1) 1
          tm63MiddleAfter16A 0 tm63MiddleAfter16B
          tm63MiddleAfter16Head) =
      some (s1Config tm63Length1
        (16*tm63RootResidueSixK-2) 0
        (tm63MiddleAfter16A+tm63MiddleAfter16B+2) 0
        (2^tm63MiddleAfter16B-1)
        (tm63MiddleAfter16Head+5+3*tm63MiddleAfter16B)) := by
    simpa [hinput,htarget,nextExponent,nextRight] using hrow
  have hcomp := run_compose_local
    tm63_blank_reaches_after_middle16 hrow'
  simpa [tm63MiddleFirst17Moves,tm63MiddleAfter17A,
    tm63MiddleAfter17B,tm63MiddleAfter17Head] using hcomp

#print axioms tm63_root_residue16_r_odd
#print axioms tm63_blank_reaches_after_middle16

end BB6Coverage.Agent49TM63RootResidueSixteen