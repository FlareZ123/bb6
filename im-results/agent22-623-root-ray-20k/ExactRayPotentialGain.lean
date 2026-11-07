import Agent22ExactDrainCocycleSource

/-!
# Exact monotone weighted potential for the four #623 canonical rays

The original-source weighted B-drain identity gives a strictly increasing
potential P(a,d)=2*a+d along every canonical ray transition. The increment
is stated exactly in terms of the number of outer B-drain iterations.
-/

namespace BB6.Agent22ExactRayPotentialGain

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent22ExactDrainCocycleSource

/-- Left-odd ray: P increases by exactly 2r+4. -/
theorem left_odd_gain (k d t B E : Nat)
    (hbudget : d + 3 ≤ ternaryOnes k)
    (hbase : drainB k (d + 3) 5 = some (.D B E)) :
    ∃ r : Nat,
      2 * (B + t) + E =
        (2 * (d + 5 + k + t) + d) + 2*r + 4 := by
  obtain ⟨r, hr⟩ := drainB_weighted_exact (d + 3) k 5 B E hbudget hbase
  refine ⟨r, ?_⟩
  omega

/-- Left-even ray: P increases by exactly 2r+4. -/
theorem left_even_gain (k d t B E : Nat)
    (hbudget : d + 2 ≤ ternaryOnes k)
    (hbase : drainB k (d + 2) 2 = some (.D B E)) :
    ∃ r : Nat,
      2 * (B + t) + E =
        (2 * (d + 2 + k + t) + d) + 2*r + 4 := by
  obtain ⟨r, hr⟩ := drainB_weighted_exact (d + 2) k 2 B E hbudget hbase
  refine ⟨r, ?_⟩
  omega

/-- Right-odd ray: P increases by exactly (d-a)+2r+8. -/
theorem right_odd_gain (k a t B E : Nat)
    (ha : 1 ≤ a)
    (hbudget : a - 1 ≤ ternaryOnes (2*k + 5))
    (hbase : drainB (2*k + 5) (a - 1) 3 = some (.D B E)) :
    ∃ r : Nat,
      2 * (B + 2*t) + E =
        (2*a + (a + 1 + 2*k + 2*t)) +
          ((a + 1 + 2*k + 2*t) - a) + 2*r + 8 := by
  obtain ⟨r, hr⟩ := drainB_weighted_exact (a - 1) (2*k + 5) 3 B E hbudget hbase
  refine ⟨r, ?_⟩
  omega

/-- Right-even ray: P increases by exactly (d-a)+2r+7. -/
theorem right_even_gain (k a t a1 b1 d1 B E : Nat)
    (hbudget : a < ternaryOnes (2*k + 3))
    (heval : evalA (2*k + 3) a (2*a + 5) = some (a1, b1, d1))
    (hbudget1 : b1 ≤ ternaryOnes a1)
    (hbase : drainB a1 b1 d1 = some (.D B E)) :
    ∃ r : Nat,
      2 * (B + 2*t) + E =
        (2*a + (a + 2 + 2*k + 2*t)) +
          ((a + 2 + 2*k + 2*t) - a) + 2*r + 7 := by
  obtain ⟨r, hr⟩ := drainB_weighted_exact b1 a1 d1 B E hbudget1 hbase
  have he := evalA_weighted_exact (2*k + 3) a (2*a + 5) a1 b1 d1 hbudget heval
  refine ⟨r, ?_⟩
  omega

#print axioms left_odd_gain
#print axioms left_even_gain
#print axioms right_odd_gain
#print axioms right_even_gain

end BB6.Agent22ExactRayPotentialGain
