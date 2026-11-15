import ChampionRootBridge
import S1Encoder
import CountedQ4Prefix
import M1EvenResidueTwoFiniteBridge
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent8M1EvenResidueTwoInputFrameGeneral

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent6Q4Prefix
open BB6Coverage.Agent8M1EvenResidueTwo

/-- The low three complemented binary blocks for the residue-two branch. -/
theorem binDec_residue_two (L k : Nat) (hL : 3 ≤ L)
    (hk : k < 2^(L-3)) :
    binDec L (8*k+2) = d1 ++ d0 ++ d1 ++ binDec (L-3) k := by
  let r := L-3
  have hL' : L = r+3 := by dsimp [r]; omega
  have hk0 : k < 2^r := by simpa [r] using hk
  have hpow1 : 2^(r+2) = 4*2^r := by
    rw [Nat.pow_add]
    simp [show 2^2 = 4 by decide, Nat.mul_comm]
  have hpow2 : 2^(r+1) = 2*2^r := by
    rw [Nat.pow_add]
    simp [show 2^1 = 2 by decide, Nat.mul_comm]
  have hk1 : 4*k+1 < 2^(r+2) := by rw [hpow1]; omega
  have hk2 : 2*k < 2^(r+1) := by rw [hpow2]; omega
  have h1 : binDec (r+3) (8*k+2) = d1 ++ binDec (r+2) (4*k+1) := by
    have hnum : 8*k+2 = 2*(4*k+1) := by omega
    rw [hnum]
    exact binDec_even (r+2) (4*k+1) hk1
  have h2 : binDec (r+2) (4*k+1) = d0 ++ binDec (r+1) (2*k) := by
    have hnum : 4*k+1 = 2*(2*k)+1 := by omega
    rw [hnum]
    exact binDec_odd (r+1) (2*k) hk2
  have h3 : binDec (r+1) (2*k) = d1 ++ binDec r k := by
    exact binDec_even r k hk0
  rw [hL', h1, h2, h3]
  simp [List.append_assoc]

/-- The output low-three-bit word after decrementing the residue-two source. -/
theorem binDec_residue_one (L k : Nat) (hL : 3 ≤ L)
    (hk : k < 2^(L-3)) :
    binDec L (8*k+1) = d0 ++ d1 ++ d1 ++ binDec (L-3) k := by
  let r := L-3
  have hL' : L = r+3 := by dsimp [r]; omega
  have hk0 : k < 2^r := by simpa [r] using hk
  have hpow1 : 2^(r+2) = 4*2^r := by
    rw [Nat.pow_add]
    simp [show 2^2 = 4 by decide, Nat.mul_comm]
  have hpow2 : 2^(r+1) = 2*2^r := by
    rw [Nat.pow_add]
    simp [show 2^1 = 2 by decide, Nat.mul_comm]
  have hk1 : 4*k < 2^(r+2) := by rw [hpow1]; omega
  have hk2 : 2*k < 2^(r+1) := by rw [hpow2]; omega
  have h1 : binDec (r+3) (8*k+1) = d0 ++ binDec (r+2) (4*k) := by
    have hnum : 8*k+1 = 2*(4*k)+1 := by omega
    rw [hnum]
    exact binDec_odd (r+2) (4*k) hk1
  have h2 : binDec (r+2) (4*k) = d1 ++ binDec (r+1) (2*k) := by
    have hnum : 4*k = 2*(2*k) := by omega
    rw [hnum]
    exact binDec_even (r+1) (2*k) hk2
  have h3 : binDec (r+1) (2*k) = d1 ++ binDec r k := by
    exact binDec_even r k hk0
  rw [hL', h1, h2, h3]
  simp [List.append_assoc]

private theorem m1EvenResidueTwoSourceLeftAt (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hk : k < 2^(L-3)) (i : Nat) (hi : i ≤ 11) :
    (s1Config L (8*k+2) 1 a 0 b h).tape
      (h - ((3*a+1+i : Nat) : Int)) =
      sideBit (markerWord 1 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh) (1+i) := by
  rw [s1Config_left_cell L (8*k+2) 1 a 0 b h (3*a+1+i)]
  simp only [s1LeftFacing]
  rw [binDec_zero]
  have hsb := sideBit_d1pow_append a (1+i)
    (markerWord 1 ++ d0 ++ binDec L (8*k+2) ++ lh)
  have hsb' : sideBit (d1pow a ++ markerWord 1 ++ d0 ++ binDec L (8*k+2) ++ lh)
      (3*a+1+i) = sideBit (markerWord 1 ++ d0 ++ binDec L (8*k+2) ++ lh) (1+i) := by
    simpa [List.append_assoc, Nat.add_assoc] using hsb
  rw [hsb']
  have hbin := binDec_residue_two L k hL hk
  rw [hbin]
  let pref := markerWord 1 ++ d0 ++ d1 ++ d0 ++ d1
  have hlt : 1+i < pref.length := by
    dsimp [pref, markerWord, d0, d1]
    omega
  have hleft1 := sideBit_append_left pref (binDec (L-3) k ++ lh) (1+i) hlt
  have hleft2 := sideBit_append_left pref lh (1+i) hlt
  simpa [pref, List.append_assoc] using hleft1.trans hleft2.symm

private theorem m1EvenResidueTwoSweptLeftCell (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hk : k < 2^(L-3)) (i : Nat) (hi : i ≤ 11) :
    sweptLeft (3*a+1) (s1Config L (8*k+2) 1 a 0 b h).tape h
      (h - ((3*a+1+i : Nat) : Int)) =
      sideBit (markerWord 1 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh) (1+i) := by
  have hp := sweptLeft_preserves_left (3*a+1)
    (s1Config L (8*k+2) 1 a 0 b h).tape h
    (h - ((3*a+1+i : Nat) : Int)) (by omega)
  rw [hp]
  exact m1EvenResidueTwoSourceLeftAt L k a b h hL hk i hi

private theorem m1EvenResidueTwoBits (i : Nat) (hi : i ≤ 11) :
    sideBit (markerWord 1 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh) (1+i) =
      decide (-(i : Int) ∈ m1EvenResidueTwoBridgeStart.marked) := by
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨
      i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 := by omega
  rcases hcases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11
  all_goals subst i <;> decide

/-- For every admissible S1 source with m=1 and n=8*k+2, the
`3*a+1)-cell left sweep agrees with the exact finite bridge input on the
whole `[-11,4]` window. -/
theorem m1EvenResidueTwoBridge_input_match (L k a b : Nat) (h : Int)
    (hL : 3 ≤ L) (hk : k < 2^(L-3)) (ha : 0 < a) :
    ∀ y, m1EvenResidueTwoInside y = true →
      sweptLeft (3*a+1) (s1Config L (8*k+2) 1 a 0 b h).tape h
        (h - ((3*a+1 : Nat) : Int) + y) =
        decide (y ∈ m1EvenResidueTwoBridgeStart.marked) := by
  intro y hy
  have hbounds : -11 ≤ y ∧ y ≤ 4 := by
    simpa [m1EvenResidueTwoInside] using hy
  by_cases hy0 : y ≤ 0
  · let i := (-y).toNat
    have hi : i ≤ 11 := by
      have hii : (i : Int) = -y := by
        dsimp [i]
        exact Int.toNat_of_nonneg (by omega)
      have hle : (i : Int) ≤ 11 := by rw [hii]; omega
      exact_mod_cast hle
    have hcoord : h - ((3*a+1 : Nat) : Int) + y =
        h - ((3*a+1+i : Nat) : Int) := by
      have hii : (i : Int) = -y := by
        dsimp [i]
        exact Int.toNat_of_nonneg (by omega)
      omega
    rw [hcoord, m1EvenResidueTwoSweptLeftCell L k a b h hL hk i hi]
    have hbits :
        sideBit (markerWord 1 ++ d0 ++ d1 ++ d0 ++ d1 ++ lh) (1+i) =
          decide (y ∈ m1EvenResidueTwoBridgeStart.marked) := by
      have hyi : y = -(i : Int) := by
        have hii : (i : Int) = -y := by
          dsimp [i]
          exact Int.toNat_of_nonneg (by omega)
        omega
      simpa [hyi] using m1EvenResidueTwoBits i hi
    exact hbits
  · have hypos : 0 < y := by omega
    rcases (show y = 1 ∨ y = 2 ∨ y = 3 ∨ y = 4 by omega) with h1 | h2 | h3 | h4
    · rw [h1]
      have hleft := sweptLeft_leftmost (3*a)
        (s1Config L (8*k+2) 1 a 0 b h).tape h
      have hcoord : h - ((3*a+1 : Nat) : Int) + 1 = h - (3*a : Int) := by omega
      rw [hcoord]
      simpa [m1EvenResidueTwoBridgeStart] using hleft
    · rw [h2]
      let j := 3*a+1-2
      have hj : j+1 < 3*a+1 := by dsimp [j]; omega
      have hblock := sweptLeft_block (3*a+1) j
        (s1Config L (8*k+2) 1 a 0 b h).tape h hj
      have hcoord : h - ((3*a+1 : Nat) : Int) + 2 = h - (j : Int) := by
        dsimp [j]; omega
      rw [hcoord]
      simpa [m1EvenResidueTwoBridgeStart] using hblock
    · rw [h3]
      let j := 3*a+1-3
      have hj : j+1 < 3*a+1 := by dsimp [j]; omega
      have hblock := sweptLeft_block (3*a+1) j
        (s1Config L (8*k+2) 1 a 0 b h).tape h hj
      have hcoord : h - ((3*a+1 : Nat) : Int) + 3 = h - (j : Int) := by
        dsimp [j]; omega
      rw [hcoord]
      simpa [m1EvenResidueTwoBridgeStart] using hblock
    · rw [h4]
      let j := 3*a+1-4
      have hj : j+1 < 3*a+1 := by dsimp [j]; omega
      have hblock := sweptLeft_block (3*a+1) j
        (s1Config L (8*k+2) 1 a 0 b h).tape h hj
      have hcoord : h - ((3*a+1 : Nat) : Int) + 4 = h - (j : Int) := by
        dsimp [j]; omega
      rw [hcoord]
      simpa [m1EvenResidueTwoBridgeStart] using hblock

#print axioms binDec_residue_two
#print axioms binDec_residue_one
#print axioms m1EvenResidueTwoBridge_input_match

end BB6Coverage.Agent8M1EvenResidueTwoInputFrameGeneral
