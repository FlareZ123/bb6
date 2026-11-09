import Lean
import Lean.Elab.Tactic.Omega

namespace S4Mass

/-- Weight and mass of the unary-block digit stack, matching S4Power.W and
S4PrefixEighthMass.stackMass respectively. -/
def W : List Nat → Nat
  | [] => 0
  | a :: xs => a + 1 + 2 * W xs

def mass (xs : List Nat) : Nat := xs.sum + xs.length

/-- Every integer weight in [m,3m), for m ≥ 10, is attainable by
a stack of total unary-block mass m using at most three digits.
This is a constructive finite-length statement. -/
theorem realize_weight_with_mass (m w : Nat)
    (hm : 10 ≤ m) (hlo : m ≤ w) (hhi : w < 3 * m) :
    ∃ xs : List Nat, mass xs = m ∧ W xs = w ∧ xs.length ≤ 3 := by
  by_cases h0 : w = m
  · refine ⟨[m - 1], ?_, ?_, by simp⟩
    · simp [mass]; omega
    · simp [W]; omega
  by_cases h2 : w < 2 * m
  · let a := 2 * m - w
    let b := w - m
    have ha : 1 ≤ a := by dsimp [a]; omega
    have hb : 1 ≤ b := by dsimp [b]; omega
    refine ⟨[a - 1, b - 1], ?_, ?_, by simp⟩
    · simp [mass]; dsimp [a, b]; omega
    · simp [W]; dsimp [a, b]; omega
  · let d := w - m
    let q := (d - 1) / 3
    let r := d - 3 * q
    let a := m - q - r
    have hdlo : m ≤ d := by dsimp [d]; omega
    have hdhi : d < 2 * m := by dsimp [d]; omega
    have hq : 1 ≤ q := by dsimp [q]; omega
    have hr : 1 ≤ r ∧ r ≤ 3 := by dsimp [r, q]; omega
    have ha : 1 ≤ a := by dsimp [a]; omega
    refine ⟨[a - 1, r - 1, q - 1], ?_, ?_, by simp⟩
    · simp [mass]; dsimp [a, r, q, d]; omega
    · simp [W]; dsimp [a, r, q, d]; omega

/-- An exact-mass suffix can hit any dyadic gate whose exponent lies
in the natural dyadic bracket [m+k,2(m+k)). -/
theorem realize_power_target (m k p : Nat)
    (hm : 10 ≤ m) (hk : k ≤ m)
    (hlo : m + k ≤ p) (hhi : p < 2 * (m + k)) :
    ∃ xs : List Nat, mass xs = m ∧ W xs + k = p ∧ xs.length ≤ 3 := by
  have hwlo : m ≤ p - k := by omega
  have hwhi : p - k < 3 * m := by omega
  obtain ⟨xs, hm', hw', hlen⟩ :=
    realize_weight_with_mass m (p-k) hm hwlo hwhi
  exact ⟨xs, hm', by omega, hlen⟩

#print axioms realize_weight_with_mass
#print axioms realize_power_target

end S4Mass
