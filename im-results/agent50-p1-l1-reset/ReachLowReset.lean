import ResetCount
import DichotomyOriginal

namespace BB6.Agent50ReachReset
open BB6.Agent47P1
open BB6.Agent1Quarter
open BB6.Agent45TwoRoot
open BB6.Agent50ResetCount

/-- Genuine blank-orbit-reachable positive even exits from the two authentic
    critical feeders, at inverse cost below 8*2^(16q), require at least two
    positive-depth inverse edges in their exact source odd inverse history. -/
theorem authentic_lowcost_reachable_even_requires_two_resets
    (q b d m t k c : Nat) (root : Bool)
    (hq : 1≤q)
    (hcone : OddCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m)
    (hb : 8≤b) (hb4 : b%4=0) (hdodd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hceven : c%2=0) (hk : 2≤k)
    (hreach : BB6.Agent1.Reach (2*k-4) (c+4))
    (hlow : m < 8*2^(16*q)) :
    ∃ z, CountCone
      (if root then 4*u2 q-4 else 6*u2 q-2)
      (if root then 4*u2 q+9 else 2*u2 q+5) b d m z ∧ 2≤z := by
  obtain ⟨z,hcount⟩ := odd_cone_has_count _ _ b d m hcone
  have hdich := BB6.Agent9Dichotomy.authentic_reachable_even_exponential_or_wall
    q b d m t k c root hq hcone hb hb4 hdodd hi hceven hk hreach
  rcases hdich with hbig | ⟨ht,hwall⟩
  · omega
  · have hwall' : b = 4*m+64*q+(if root then 12 else 16) := by
      cases root <;> simpa using hwall
    exact ⟨z,hcount, wall_requires_two_resets q b d m z root hq hcount hwall'⟩

#print axioms authentic_lowcost_reachable_even_requires_two_resets
end BB6.Agent50ReachReset
