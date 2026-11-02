import Lean.Elab.Tactic.Omega
import CodeImplicitNil
import TokenCostNormal

set_option maxHeartbeats 5000000

namespace BB6.Agent32Permutation

open BB6.Parikh

def start (k : Nat) (w : List Bool) : CryptidBoundary.Cfg :=
  CryptidBoundary.init
    (List.replicate (3*k+1) true ++ false :: CryptidA.wordCode w)

def cost (k : Nat) (w : List Bool) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) w +
      (2*((4*k+3)+CryptidA.wordInc w)+6))

def before (u v : List Bool) : List Bool := u ++ false :: true :: v
def after (u v : List Bool) : List Bool := u ++ true :: false :: v

theorem swap_inc (u v : List Bool) :
    CryptidA.wordInc (before u v) = CryptidA.wordInc (after u v) := by
  simp [before, after, BB6.Parikh.wordInc_append, CryptidA.wordInc]
  omega

theorem swap_times (k : Nat) (u v : List Bool) :
    cost k (before u v) = cost k (after u v) + 6 := by
  unfold cost
  rw [swap_inc]
  have h := BB6.Parikh.swap_cost_context (4*k+3) u v
  change CryptidA.wordCost (4*k+3) (before u v) =
    CryptidA.wordCost (4*k+3) (after u v) + 6 at h
  omega

/-- Original raw-machine trajectories for adjacent packet permutations
    reunite at EXACTLY the same finite configuration, six steps apart. -/
theorem swap_confluence (k : Nat) (u v : List Bool) :
    CryptidBoundary.run (cost k (before u v)) (start k (before u v)) =
    CryptidBoundary.run (cost k (after u v)) (start k (after u v)) := by
  unfold cost start
  rw [BB6.Agent32Code.full_A_code_implicit_nil,
      BB6.Agent32Code.full_A_code_implicit_nil]
  rw [swap_inc]

/-- The entire source-verified A-code return factors through counts of
    the two token types, independent of order and inversion count. -/
theorem same_counts_confluence (k : Nat) (u v : List Bool)
    (hp : pairsN u = pairsN v)
    (ht : triplesN u = triplesN v) :
    CryptidBoundary.run (cost k u) (start k u) =
    CryptidBoundary.run (cost k v) (start k v) := by
  unfold cost start
  rw [BB6.Agent32Code.full_A_code_implicit_nil,
      BB6.Agent32Code.full_A_code_implicit_nil]
  have hi : CryptidA.wordInc u = CryptidA.wordInc v := by
    rw [wordInc_formula, wordInc_formula, hp, ht]
  rw [hi]

#print axioms swap_times
#print axioms swap_confluence
#print axioms same_counts_confluence
end BB6.Agent32Permutation
