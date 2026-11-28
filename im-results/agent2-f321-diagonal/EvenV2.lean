import F321BackwardBarrier
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321EvenV2
open BB6.Agent31F321Density

/-- Positive n has even 2-adic valuation exactly when it is a power of four
    times an odd integer.  We use this representation instead of a valuation
    function so the invariant stays elementary and source-local. -/
def EvenV2Form (n : Nat) : Prop :=
  ∃ t u : Nat, n = 4^t * u ∧ u % 2 = 1

/-- Root-specific all-depth 2-adic invariant.  Every reached state below the
    diagonal with even gap has even 2-adic valuation of a+2. -/
theorem reached_below_even_evenV2 {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (hbelow : a < d) (heven : (d-a)%2 = 0) :
    EvenV2Form (a+2) := by
  induction hr with
  | nil => omega
  | @step n a d A D hr hm ih =>
    cases hm with
    | high d hg =>
        unfold EvenV2Form
        have hodd : (a-d) % 2 = 1 := by omega
        exact ⟨0, a-d, by omega, hodd⟩
    | equal => omega
    | far d h1 h2 =>
        have hp : (d-a)%2 = 0 := by omega
        rcases ih h1 hp with ⟨t,u,htu,hu⟩
        unfold EvenV2Form
        refine ⟨t+1,u,?_,hu⟩
        rw [Nat.pow_succ]
        calc
          4 * a + 6 + 2 = 4 * (a+2) := by omega
          _ = 4 * (4^t * u) := by rw [htu]
          _ = (4^t * 4) * u := by ac_rfl
    | middleEven d h1 h2 hp => omega
    | middleOdd d h1 h2 hp => omega

/-- In particular every root-reachable middle-even predecessor has
    a+2 = 4^t*u with u odd. -/
theorem reachable_middleEven_evenV2 {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (h1 : a < d) (hp : (d-a)%2 = 0) :
    EvenV2Form (a+2) :=
  reached_below_even_evenV2 hr h1 hp

#print axioms reached_below_even_evenV2
#print axioms reachable_middleEven_evenV2
end BB6.Agent2F321EvenV2
