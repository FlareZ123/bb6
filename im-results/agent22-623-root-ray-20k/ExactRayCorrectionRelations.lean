import Agent22ExactDrainCocycleSource

/-!
# Source-exact correction relations for the four canonical #623 rays

These lemmas instantiate the weighted B-drain cocycle in each canonical
ray sector. They reduce the two correction variables beta and delta to
one integer r (the number of outer drain iterations).
-/

namespace BB6.Agent22ExactRayCorrectionRelations

open BusyBeaver.M_1RB0LE_0RC1RC_0RD1LA_1LD0LA_1LF1LC_HHH0LA
open BB6.Agent49ParitySource
open BB6.Agent22ExactDrainCocycleSource

def beta (B c v : Nat) : Int := (B : Int) - (c : Int) - (v : Int)

def delta (E m : Nat) : Int := (E : Int) - 3 * (m : Int)

/-- Left-odd canonical base: delta + 2 beta = 2r + 4. -/
theorem left_odd_correction (k d B E : Nat)
    (hbudget : d + 3 ≤ ternaryOnes k)
    (hbase : drainB k (d + 3) 5 = some (.D B E)) :
    ∃ r : Nat, delta E d + 2 * beta B 5 k = (2*r + 4 : Int) := by
  obtain ⟨r, hr⟩ := drainB_weighted_exact (d + 3) k 5 B E hbudget hbase
  refine ⟨r, ?_⟩
  simp [beta, delta]
  omega

/-- Left-even canonical base: delta + 2 beta = 2r + 4. -/
theorem left_even_correction (k d B E : Nat)
    (hbudget : d + 2 ≤ ternaryOnes k)
    (hbase : drainB k (d + 2) 2 = some (.D B E)) :
    ∃ r : Nat, delta E d + 2 * beta B 2 k = (2*r + 4 : Int) := by
  obtain ⟨r, hr⟩ := drainB_weighted_exact (d + 2) k 2 B E hbudget hbase
  refine ⟨r, ?_⟩
  simp [beta, delta]
  omega

/-- Right-odd canonical base: delta + 2 beta = 2r + 8. -/
theorem right_odd_correction (k a B E : Nat)
    (hbudget : a - 1 ≤ ternaryOnes (2*k + 5))
    (hbase : drainB (2*k + 5) (a - 1) 3 = some (.D B E)) :
    ∃ r : Nat, delta E a + 2 * beta B 1 (2*k) = (2*r + 8 : Int) := by
  obtain ⟨r, hr⟩ := drainB_weighted_exact (a - 1) (2*k + 5) 3 B E hbudget hbase
  refine ⟨r, ?_⟩
  simp [beta, delta]
  omega

/-- Right-even canonical base: the initial evaluator contributes the
    fixed offset 7, while the subsequent B-drain contributes 2r. -/
theorem right_even_correction (k a a1 b1 d1 B E : Nat)
    (hbudget : a < ternaryOnes (2*k + 3))
    (heval : evalA (2*k + 3) a (2*a + 5) = some (a1, b1, d1))
    (hbudget1 : b1 ≤ ternaryOnes a1)
    (hbase : drainB a1 b1 d1 = some (.D B E)) :
    ∃ r : Nat, delta E a + 2 * beta B 2 (2*k) = (2*r + 7 : Int) := by
  obtain ⟨r, hr⟩ := drainB_weighted_exact b1 a1 d1 B E hbudget1 hbase
  have he := evalA_weighted_exact (2*k + 3) a (2*a + 5) a1 b1 d1 hbudget heval
  refine ⟨r, ?_⟩
  simp [beta, delta]
  omega

#print axioms left_odd_correction
#print axioms left_even_correction
#print axioms right_odd_correction
#print axioms right_even_correction

end BB6.Agent22ExactRayCorrectionRelations
