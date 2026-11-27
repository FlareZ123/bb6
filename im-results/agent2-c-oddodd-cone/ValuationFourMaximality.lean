import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 0

namespace BB6.Agent2Val4Maximality

/-- Complete arithmetic classification of the simultaneous one-step
    odd-image obstructions at the two admissible even depths n=0,2
    of an odd-source high bounce.

    The equations are exactly the original Machine C section
    sum/power and affine-cost equations at those two depths:
      Q = A+K+1 = 2*(b0+3) = 8*(b2+3);
      A+2K = 2*l0+b0+7 = 2*l2+b2+13.
    For a target with even A and odd K, the two source branches
    both have forbidden-odd-image outputs iff the target lies in the
    single residue pattern A=0 mod8 and Q=48 mod64.

    This theorem is a genuine equivalence without a search range,
    branch-depth cutoff, or any assumption about the magnitude
    of either target coordinate. Source guard fulfillment is a
    separate condition checked by the exact section inverse. -/
theorem two_depth_forbidden_iff (A K b0 l0 b2 l2 : Nat)
    (hA : A%2=0) (hK : K%2=1)
    (hQ0 : A+K+1=2*(b0+3))
    (hC0 : A+2*K=2*l0+b0+7)
    (hQ2 : A+K+1=8*(b2+3))
    (hC2 : A+2*K=2*l2+b2+13) :
    ((l0%2=1 ∧ ((b0+l0)%4=1 ∨ (b0+l0)%4=2)) ∧
     (l2%2=1 ∧ ((b2+l2)%4=1 ∨ (b2+l2)%4=2))) ↔
      A%8=0 ∧ (A+K+1)%64=48 := by
  omega

/-- In particular, no valuation-four target with Q = 16 mod64 can
    force both of its admissible predecessor branches into the
    one-step odd-image obstruction by this mechanism. -/
theorem val4_sixteen_not_two_depth_forbidden (A K b0 l0 b2 l2 : Nat)
    (hA : A%2=0) (hK : K%2=1)
    (h16 : (A+K+1)%64=16)
    (hQ0 : A+K+1=2*(b0+3))
    (hC0 : A+2*K=2*l0+b0+7)
    (hQ2 : A+K+1=8*(b2+3))
    (hC2 : A+2*K=2*l2+b2+13) :
    ¬ ((l0%2=1 ∧ ((b0+l0)%4=1 ∨ (b0+l0)%4=2)) ∧
       (l2%2=1 ∧ ((b2+l2)%4=1 ∨ (b2+l2)%4=2))) := by
  intro h
  obtain ⟨_,h48⟩ :=
    (two_depth_forbidden_iff A K b0 l0 b2 l2
      hA hK hQ0 hC0 hQ2 hC2).mp h
  omega

#print axioms two_depth_forbidden_iff
#print axioms val4_sixteen_not_two_depth_forbidden

end BB6.Agent2Val4Maximality
