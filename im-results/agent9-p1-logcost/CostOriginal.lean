import UniversalSmallLeft
import CostBarrier

namespace BB6.Agent9Cost

open BB6.Agent47P1
open BB6.Agent1Quarter
open BB6.Agent45TwoRoot
open BB6.Agent1ShortCone

/-- Source-connected logarithmic-depth obstruction for a genuinely
blank-reachable even-right inverse branch of either real P1 two-sector
feeder. The inverse cost m must be within O(log q) of 16q. -/
theorem reachable_even_terminal_near_full_cost
    (q b d m t k c r : Nat) (root : Bool)
    (hq : 1 ≤ q) (hqr : q ≤ 2 ^ r)
    (hcone : OddCone
      (if root then 4 * u2 q - 4 else 6 * u2 q - 2)
      (if root then 4 * u2 q + 9 else 2 * u2 q + 5) b d m)
    (hb : 8 ≤ b) (hb4 : b % 4 = 0) (hd : d % 2 = 1)
    (hi : inverseAt b d t = some (k,c))
    (hc : c % 2 = 0) (hk : 2 ≤ k)
    (hr : BB6.Agent1.Reach (2 * k - 4) (c + 4)) :
    16 * q ≤ m + r + 4 := by
  let u := u2 q
  have hdom := pow16_dom q hq
  have hu : u + 4*q + 3 = 7 * 2^(16*q) := by
    dsimp [u,u2]
    omega
  have hscale : 27 * 2^(16*q) ≤ 4*u + 8 :=
    scale15 q u hq hu
  have hleft : 4*u+8 ≤ 2^m * (b+12) := by
    cases root with
    | false =>
      have hh := odd_cone_left_bound (6*u-2) (2*u+5) b d m
        (by simpa [u] using hcone)
      have hfirst : 4*u+8 ≤ 6*u-2+12 := by omega
      exact Nat.le_trans hfirst hh
    | true =>
      have hh := odd_cone_left_bound (4*u-4) (4*u+9) b d m
        (by simpa [u] using hcone)
      have hfirst : 4*u+8 = 4*u-4+12 := by omega
      exact hfirst ▸ hh
  have hdyadic : 27 * 2^(16*q) ≤ 2^m * (b+12) :=
    Nat.le_trans hscale hleft
  have hnarrow := BB6.Agent1Bottleneck.reachable_even_terminal_small_left
    q b d m t k c root hq hcone hb hb4 hd hi hc hk hr
  exact logarithmic_cost_lower q m r b hq hqr hdyadic hnarrow

#print axioms reachable_even_terminal_near_full_cost
end BB6.Agent9Cost
