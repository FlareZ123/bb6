import UniformReachBounds
import GenericCriticalReach41K
import Q33Finite

namespace BB6.Agent9Q33Uniform
open BB6.Precision BB6.Agent9Q33

/-- Uniform abstract shadow bounds for the first genuine P1 feeder,
    obtained from the fixed q=33 graph without constructing any
    parameter-dependent finite nodes. -/
theorem bounds0 (r m z : Nat)
    (hpath : ShadowReach (16*(33+2^(10+41)*r)+8)
        (12*(33+2^(10+41)*r)+4) m z) :
    m≤41 ∧ ¬1024∣z := by
  have hL : 16*(33+2^(10+41)*r)+8 = 536+16*2^(10+41)*r := by
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega
  have hR : 12*(33+2^(10+41)*r)+4 =
      400+2^(10+41)*(12*r) := by
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega
  have hpath' : ShadowReach (536+16*2^(10+41)*r)
      (400+2^(10+41)*(12*r)) m z := by
    simpa only [hL,hR] using hpath
  have h := uniform_reach_bounds 10 41 536 400 r 12
      (fun m z => (m,z)∈q33L0Nodes) q33L0_root
      q33L0_small q33L0_no1024 q33L0_closed m z hpath'
  simpa only [show (2:Nat)^10=1024 by decide] using h

/-- The analogous uniform bound for the second genuine P1 feeder. -/
theorem bounds1 (r m z : Nat)
    (hpath : ShadowReach (16*(33+2^(10+41)*r)+9)
        (10*(33+2^(10+41)*r)+4) m z) :
    m≤41 ∧ ¬1024∣z := by
  have hL : 16*(33+2^(10+41)*r)+9 = 537+16*2^(10+41)*r := by
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega
  have hR : 10*(33+2^(10+41)*r)+4 =
      334+2^(10+41)*(10*r) := by
    simp only [Nat.mul_add, Nat.mul_assoc]
    omega
  have hpath' : ShadowReach (537+16*2^(10+41)*r)
      (334+2^(10+41)*(10*r)) m z := by
    simpa only [hL,hR] using hpath
  have h := uniform_reach_bounds 10 41 537 334 r 10
      (fun m z => (m,z)∈q33L1Nodes) q33L1_root
      q33L1_small q33L1_no1024 q33L1_closed m z hpath'
  simpa only [show (2:Nat)^10=1024 by decide] using h

/-- A full original-source blank-root critical-gateway exclusion derived
    automatically from a single fixed finite shadow graph and the uniform
    precision path theorem. The stronger dedicated 2^40 cylinder is known. -/
theorem blank_no_critical_uniform_2pow51 (r : Nat) :
    ¬ BB6.Agent1.Reach 2
      (14*2^(16*(33+2^(10+41)*r)+2)-2*(16*(33+2^(10+41)*r)+2)-10) := by
  let q := 33+2^(10+41)*r
  have hq : 29≤q := by dsimp [q]; omega
  have hs0 : ∀ m z, ShadowReach (16*q+8) (12*q+4) m z → m≤41 := by
    intro m z hp
    exact (bounds0 r m z hp).1
  have hs1 : ∀ m z, ShadowReach (16*q+9) (10*q+4) m z → m≤41 := by
    intro m z hp
    exact (bounds1 r m z hp).1
  have hn0 : ∀ m z, ShadowReach (16*q+8) (12*q+4) m z → ¬1024∣z := by
    intro m z hp
    exact (bounds0 r m z hp).2
  have hn1 : ∀ m z, ShadowReach (16*q+9) (10*q+4) m z → ¬1024∣z := by
    intro m z hp
    exact (bounds1 r m z hp).2
  exact BB6.Agent9Generic41Reach.critical_unreachable_of_reach41K
    q hq hs0 hs1 hn0 hn1

#print axioms bounds0
#print axioms bounds1
#print axioms blank_no_critical_uniform_2pow51
end BB6.Agent9Q33Uniform
