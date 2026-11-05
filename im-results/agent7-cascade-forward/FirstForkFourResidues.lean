import FirstForkFourDistinct
import FirstForkRootFour
set_option maxHeartbeats 0
set_option maxRecDepth 16384
set_option exponentiation.threshold 14000

namespace CascadeFirstFork
open CascadeResetInverse CascadeUniformFatal CascadeManyShield CascadeSweep

private theorem pow_period_thirteen_thousand (n : Nat) :
    2^(n+13122)%6561=2^n%6561 := by
  rw [Nat.pow_add]
  have hp:2^13122%6561=1:=by decide
  rw [Nat.mul_mod,hp]
  omega

private theorem pow_mod_thirteen_thousand (n:Nat) :
    2^n%6561=2^(n%13122)%6561:=by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    by_cases hn:n<13122
    · simp [Nat.mod_eq_of_lt hn]
    · have hm:n-13122<n:=by omega
      have he:n=(n-13122)+13122:=by omega
      rw [he,pow_period_thirteen_thousand]
      rw [ih (n-13122) hm]
      have hemod:((n-13122)+13122)%13122=(n-13122)%13122:=by omega
      rw [hemod]

/-- Four quantified fatal index classes have exactly the valuation-seven
    parent numerators required by the source-level four-parent theorem. -/
theorem fatal_exact_seven_indices (n:Nat) (hn:10≤n)
    (hres:n%13122=4865 ∨ n%13122=9239 ∨
      n%13122=3208 ∨ n%13122=11956) :
    (2*fatal n+5)%2187=0 ∧ (2*fatal n+5)%6561≠0 := by
  have h4374:n%4374=491 ∨ n%4374=3208:=by omega
  constructor
  · exact fatal_div2187_special n hn h4374
  · have hpow:=pow_mod_thirteen_thousand n
    have hclose:=fatal_close n (by omega)
    have hz:2*fatal n+5+2*n+3=8*2^n:=by omega
    rcases hres with h|h|h|h
    · have hh:2^n%6561=5864:=by rw [hpow,h]
      omega
    · have hh:2^n%6561=5864:=by rw [hpow,h]
      omega
    · have hh:2^n%6561=2716:=by rw [hpow,h]
      omega
    · have hh:2^n%6561=2716:=by rw [hpow,h]
      omega

/-- Four more quantified index classes have exactly seven factors of three
    in the second forced-even ancestor's odd inverse numerator. -/
theorem second_exact_seven_indices (n:Nat) (hn:10≤n)
    (hres:n%13122=83 ∨ n%13122=8831 ∨
      n%13122=6280 ∨ n%13122=10654) :
    (2*secondPred n+5)%2187=0 ∧
    (2*secondPred n+5)%6561≠0 := by
  have h4374:n%4374=83 ∨ n%4374=1906:=by omega
  constructor
  · exact second_div2187_special n hn h4374
  · have hpow:=pow_mod_thirteen_thousand n
    have hclose:=second_close n hn
    have hz:2*secondPred n+5+14*n+21=8*2^n:=by omega
    rcases hres with h|h|h|h
    · have hh:2^n%6561=5342:=by rw [hpow,h]
      omega
    · have hh:2^n%6561=5342:=by rw [hpow,h]
      omega
    · have hh:2^n%6561=2518:=by rw [hpow,h]
      omega
    · have hh:2^n%6561=2518:=by rw [hpow,h]
      omega

/-- An unconditional complete four-branch genuine blank-reset-root
    reachability equivalence on four infinite fatal index cylinders.
    This does not decide reachability of any of the four branches. -/
theorem rooted_fatal_four_unconditional (n:Nat) (hn:10≤n)
    (hres:n%13122=4865 ∨ n%13122=9239 ∨
      n%13122=3208 ∨ n%13122=11956) :
    ReachC (2,0) (fatal n,0) ↔
      ReachC (2,0) (oddPre6 n (fatal n),0) ∨
      ReachC (2,0) (oddPre3 n (fatal n),0) ∨
      ReachC (2,0) (oddPre n (fatal n),0) ∨
      ReachC (2,0) (evenPre n (n+4),0) := by
  have h4374:n%4374=491 ∨ n%4374=3208:=by omega
  exact rooted_fatal_four n hn h4374 (fatal_exact_seven_indices n hn hres).2

/-- An unconditional complete four-branch genuine blank-root equivalent
    on four infinite second-ancestor index cylinders. -/
theorem rooted_second_four_unconditional (n:Nat) (hn:10≤n)
    (hres:n%13122=83 ∨ n%13122=8831 ∨
      n%13122=6280 ∨ n%13122=10654) :
    ReachC (2,0) (fatal n,0) ↔
      ReachC (2,0) (oddPre6 n (secondPred n),0) ∨
      ReachC (2,0) (oddPre3 n (secondPred n),0) ∨
      ReachC (2,0) (oddPre n (secondPred n),0) ∨
      ReachC (2,0) (evenPre n (7*n+13),0) := by
  have h4374:n%4374=83 ∨ n%4374=1906:=by omega
  exact rooted_second_four n hn h4374 (second_exact_seven_indices n hn hres).2

#print axioms fatal_exact_seven_indices
#print axioms second_exact_seven_indices
#print axioms rooted_fatal_four_unconditional
#print axioms rooted_second_four_unconditional
end CascadeFirstFork
