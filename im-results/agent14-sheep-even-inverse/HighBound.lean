import Std
namespace SheepEvenBound

def Q (D : Nat) (B : Int) (a : Nat) : Int := 2*(D:Int)*(a:Int)+B

/-- A single strict valuation-gap cutoff propagates to every larger valuation. -/
theorem gap_above (D A : Nat) (B : Int) (hDA : 2*D < 2^A)
    (hLo : 1 < Q D B A) (hHi : Q D B A < (2^A : Nat))
    (a : Nat) (ha : A ≤ a) :
    1 < Q D B a ∧ Q D B a < (2^a : Nat) := by
  have hall (n : Nat) :
      1 < Q D B (A+n) ∧ Q D B (A+n) < (2^(A+n) : Nat) := by
    induction n with
    | zero => simpa using And.intro hLo hHi
    | succ n ih =>
      have hpow : 2^A ≤ 2^(A+n) :=
        Nat.pow_le_pow_right (by decide) (by omega)
      have hpow2 : 2*D < 2^(A+n) := by omega
      have hq : Q D B (A+(n+1)) = Q D B (A+n) + 2*(D:Int) := by
        simp [Q, Int.mul_add, Int.natCast_add]
        omega
      have hp : 2^(A+(n+1)) = 2*2^(A+n) := by
        have he : A+(n+1)=(A+n)+1 := by omega
        rw [he, Nat.pow_succ]
        omega
      have hc : (2*D:Int) < (2^(A+n):Nat) := by exact_mod_cast hpow2
      constructor
      · rw [hq]; omega
      · rw [hq, hp]; omega
  have hrep : a = A+(a-A) := by omega
  rw [hrep]
  exact hall (a-A)

/-- For node 0, h=0, no valuation a>=2 lies outside the residue gap. -/
theorem node0_h0_high (a : Nat) (ha : 2 ≤ a) :
    1 < Q 1 (-1) a ∧ Q 1 (-1) a < (2^a : Nat) := by
  exact gap_above 1 2 (-1) (by decide) (by decide) (by decide) a ha

/-- For node 0, h=1, no valuation a>=5 lies outside the residue gap. -/
theorem node0_h1_high (a : Nat) (ha : 5 ≤ a) :
    1 < Q 3 (-5) a ∧ Q 3 (-5) a < (2^a : Nat) := by
  exact gap_above 3 5 (-5) (by decide) (by decide) (by decide) a ha

/-- For node 0, h=2, no valuation a>=7 lies outside the residue gap. -/
theorem node0_h2_high (a : Nat) (ha : 7 ≤ a) :
    1 < Q 9 (-19) a ∧ Q 9 (-19) a < (2^a : Nat) := by
  exact gap_above 9 7 (-19) (by decide) (by decide) (by decide) a ha

/-- For node 1, h=0, no valuation a>=8 lies outside the residue gap. -/
theorem node1_h0_high (a : Nat) (ha : 8 ≤ a) :
    1 < Q 15 (-11) a ∧ Q 15 (-11) a < (2^a : Nat) := by
  exact gap_above 15 8 (-11) (by decide) (by decide) (by decide) a ha

/-- For node 1, h=1, no valuation a>=10 lies outside the residue gap. -/
theorem node1_h1_high (a : Nat) (ha : 10 ≤ a) :
    1 < Q 45 (-67) a ∧ Q 45 (-67) a < (2^a : Nat) := by
  exact gap_above 45 10 (-67) (by decide) (by decide) (by decide) a ha

/-- For node 1, h=2, no valuation a>=12 lies outside the residue gap. -/
theorem node1_h2_high (a : Nat) (ha : 12 ≤ a) :
    1 < Q 135 (-269) a ∧ Q 135 (-269) a < (2^a : Nat) := by
  exact gap_above 135 12 (-269) (by decide) (by decide) (by decide) a ha

/-- For node 1, h=3, no valuation a>=14 lies outside the residue gap. -/
theorem node1_h3_high (a : Nat) (ha : 14 ≤ a) :
    1 < Q 405 (-943) a ∧ Q 405 (-943) a < (2^a : Nat) := by
  exact gap_above 405 14 (-943) (by decide) (by decide) (by decide) a ha

/-- For node 2, h=0, no valuation a>=11 lies outside the residue gap. -/
theorem node2_h0_high (a : Nat) (ha : 11 ≤ a) :
    1 < Q 81 (55) a ∧ Q 81 (55) a < (2^a : Nat) := by
  exact gap_above 81 11 (55) (by decide) (by decide) (by decide) a ha

/-- For node 2, h=1, no valuation a>=13 lies outside the residue gap. -/
theorem node2_h1_high (a : Nat) (ha : 13 ≤ a) :
    1 < Q 243 (-133) a ∧ Q 243 (-133) a < (2^a : Nat) := by
  exact gap_above 243 13 (-133) (by decide) (by decide) (by decide) a ha

#print axioms node0_h0_high
#print axioms node0_h1_high
#print axioms node0_h2_high
#print axioms node1_h0_high
#print axioms node1_h1_high
#print axioms node1_h2_high
#print axioms node1_h3_high
#print axioms node2_h0_high
#print axioms node2_h1_high
#print axioms gap_above
end SheepEvenBound
