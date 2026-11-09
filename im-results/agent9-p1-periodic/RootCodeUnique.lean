import DistinctParameterSource
import ZeroOffset

/-!
# Injectivity of inverse-depth coding across all source-margin root parameters

Any two original scalar shadow inverse rays with equal starting cost and the
same full depth stream must have identical source L and initial z. This is a
uniform source theorem, with neither L-parity nor feeder-family restrictions.
-/

namespace BB6.Agent9CrossFeeder
open BB6.Precision

/-- A single inverse-depth stream determines its initial (L,z) pair among
all positive four-unit-margin source shadow rays of equal starting cost. -/
theorem infinite_shadow_root_code_injective
    (L0 L1 root0 root1 : Nat)
    (p0 : InfiniteShadowPath L0 root0)
    (p1 : InfiniteShadowPath L1 root1)
    (hL : 8≤L0) (hrootpos : 0<root0) (hrootmargin : root0+4≤L0)
    (hm0 : p0.m 0=p1.m 0)
    (hz0 : p0.z 0=root0) (hz1 : p1.z 0=root1)
    (hsame : ∀ n, p0.depth n=p1.depth n) :
    L0=L1 ∧ root0=root1 := by
  by_cases heqL : L0=L1
  · have heqm : ∀ n, p0.m n=p1.m n := by
      intro n
      induction n with
      | zero => exact hm0
      | succ n ih => rw [p0.hm n,p1.hm n,←hsame n,ih]
    let D : Nat → Int := fun n => (p1.z n:Int)-(p0.z n:Int)
    have hstep : ∀ n, D n=(2:Int)^(p0.depth n)*(2*D (n+1)) := by
      intro n
      let t := p0.depth n
      have hdiv0 := p0.hdiv n
      have hdiv1 := p1.hdiv n
      have hs : p1.depth n=t := by simp [t,←hsame n]
      rw [hs] at hdiv1
      have hdiv0I : (p0.z n:Int)=(2:Int)^t*(p0.quotient n:Int) := by
        exact_mod_cast hdiv0
      have hdiv1I : (p1.z n:Int)=(2:Int)^t*(p1.quotient n:Int) := by
        exact_mod_cast hdiv1
      have hn0 := congrArg (fun x:Nat => (x:Int)) (p0.hnext n)
      have hn1 := congrArg (fun x:Nat => (x:Int)) (p1.hnext n)
      have hnext : 2*D (n+1) = (p1.quotient n:Int)-(p0.quotient n:Int) := by
        dsimp [D]
        simp only [Int.natCast_add, Int.natCast_mul] at hn0 hn1 ⊢
        have hm := heqm n
        have ht := hsame n
        omega
      dsimp [D]
      rw [hnext]
      rw [hdiv0I,hdiv1I]
      simp only [Int.mul_sub]
      rfl
    have hz : D 0=0 := zero_offset_difference_vanishes D p0.depth hstep 0
    dsimp [D] at hz
    constructor
    · exact heqL
    · omega
  · exact False.elim (distinct_L_no_common_depth_stream L0 L1 root0 root1
      p0 p1 hL hrootpos hrootmargin heqL hm0 hsame)

#print axioms infinite_shadow_root_code_injective
end BB6.Agent9CrossFeeder
