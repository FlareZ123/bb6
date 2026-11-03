import P1BudgetTwoSector
import P1TwoSector

namespace BB6.Agent27Budget
open BB6.Agent47P1
open BB6.Agent1Quarter

/-- The exact source's two-feeder parameter is definitionally identical to
our arithmetic presentation, with no numerical approximation or assumption. -/
theorem u27_eq_published_u2 (q : Nat) :
    u27 q=BB6.Agent45TwoRoot.u2 q := rfl

/-- Audit the exact original Agent45 source feeder names and the full
BB6.Agent1 blank-entry Reach and OddCone definitions in one theorem. -/
theorem published_two_feeder_precise_cost_or_wall
    (q b d m t k c : Nat) (root : Bool)
    (hq : 1≤q)
    (hcone : OddCone
      (if root then 4*BB6.Agent45TwoRoot.u2 q-4 else
        6*BB6.Agent45TwoRoot.u2 q-2)
      (if root then 4*BB6.Agent45TwoRoot.u2 q+9 else
        2*BB6.Agent45TwoRoot.u2 q+5) b d m)
    (hb : 8≤b) (hb4 : b%4=0) (hd : d%2=1)
    (hi : inverseAt b d t = some (k,c))
    (hc : 2≤c) (hce : c%2=0) (hk : 2≤k)
    (hr : BB6.Agent1.Reach (2*k-4) (c+4)) :
    (t=1 ∧ b=4*m+64*q+(if root then 12 else 16)) ∨
      28*2^(16*q) ≤ 3*m+48*q+(if root then 16 else 19) := by
  exact authentic_two_feeder_precise_cost_or_wall
    q b d m t k c root hq hcone hb hb4 hd hi hc hce hk hr

#print axioms u27_eq_published_u2
#print axioms published_two_feeder_precise_cost_or_wall
end BB6.Agent27Budget
