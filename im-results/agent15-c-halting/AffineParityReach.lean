import AffineParityDepth
import SectionDyadic
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15

/-- Authentic blank-origin reachability forces the terminal right counter
of a left-3-mod-4 / even-right section to be divisible by four. The excluded
terminal value two is ruled out by the source-certified section theorem. -/
theorem reachable_three_normalized_right_mod4 (a k : Nat)
    (ha : a%4=3) (he : k%2=0) (hk : 2≤k)
    (hreach : CReach a k) :
    (affineNormalize a k).2%4=0 := by
  have hpair := normalize_three_even_ge_two a k ha he hk
  have hterm := (normalize_three_depth_invariants a k ha).2.2
  have hrnorm := (reach_iff_normalize a k).mp hreach
  have htwo : (affineNormalize a k).2 ≠ 2 := by
    intro htwo
    rcases hrnorm with ⟨time, ht⟩
    cases hp : affineNormalize a k with
    | mk x y =>
      simp only [hp, Prod.snd] at htwo
      rw [hp] at ht
      exact blank_no_right_two time x (by simpa [htwo] using ht)
  rcases hpair with ⟨heven,hbound⟩
  omega

/-- The 2-adic valuation of the shifted right counter equals the exact
forced-inversion depth plus one on every authentic reachable section in
this sector, represented without a separate valuation library. -/
theorem reachable_three_valuation (a k : Nat)
    (ha : a%4=3) (he : k%2=0) (hk : 2≤k)
    (hreach : CReach a k) :
    ∃ q : Nat, k+2=2^(oddDepth k+1)*(2*q+1) := by
  let p := affineNormalize a k
  have hmod : p.2%4=0 := reachable_three_normalized_right_mod4 a k ha he hk hreach
  have hlin : 2^(oddDepth k)*(p.2+2)=k+2 := (normalize_three_depth_invariants a k ha).2.1
  have hh : p.2=4*(p.2/4) := by omega
  have hy : p.2+2=2*(2*(p.2/4)+1) := by omega
  refine ⟨p.2/4,?_⟩
  calc
    k+2 = 2^(oddDepth k)*(p.2+2) := hlin.symm
    _ = 2^(oddDepth k)*(2*(2*(p.2/4)+1)) := by rw [hy]
    _ = 2^(oddDepth k+1)*(2*(p.2/4)+1) := by
      rw [Nat.pow_succ]
      ac_rfl

#print axioms reachable_three_normalized_right_mod4
#print axioms reachable_three_valuation
end BB6.Agent15
