import Factor2
import OddRescale
import ZeroOffset
import SourcePeriodAllPeriods

/-!
# Initial effective-source parameter rigidity for arbitrary inverse-shadow histories

For two infinite genuine source-shadow histories with identical dyadic depths,
the complete depth word determines both the initial shadow coordinate z and
the effective source parameter L+m. Initial costs need not agree.
-/

namespace BB6.Agent9CrossFeeder
open BB6.Precision

/-- A complete common inverse-depth stream determines the initial effective
parameter L + m and initial shadow coordinate z among all source-margin paths. -/
theorem infinite_shadow_effective_code_injective
    (L0 L1 root0 root1 : Nat)
    (p0 : InfiniteShadowPath L0 root0)
    (p1 : InfiniteShadowPath L1 root1)
    (hL : 8≤L0) (hrootpos : 0<root0) (hrootmargin : root0+4≤L0)
    (hsame : ∀ n, p0.depth n=p1.depth n) :
    (L0:Int)+(p0.m 0:Int) = (L1:Int)+(p1.m 0:Int) ∧
    p0.z 0=p1.z 0 := by
  let C : Int := ((L1:Int)+(p1.m 0:Int))-((L0:Int)+(p0.m 0:Int))
  let D : Nat → Int := fun n => (p1.z n:Int)-(p0.z n:Int)
  have hdiffM : ∀ n, (p1.m n:Int)-(p0.m n:Int) =
      (p1.m 0:Int)-(p0.m 0:Int) := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih =>
        have h0 := p0.hm n
        have h1 := p1.hm n
        have hs := hsame n
        rw [h0,h1]
        simp only [Int.natCast_add]
        omega
  have hstep : ∀ n, D n = (2:Int)^(p0.depth n)*(2*D (n+1)-C) := by
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
    have hnext : 2*D (n+1)-C = (p1.quotient n:Int)-(p0.quotient n:Int) := by
      dsimp [D,C]
      simp only [Int.natCast_add, Int.natCast_mul] at hn0 hn1 ⊢
      have hm := hdiffM n
      have ht := hsame n
      omega
    dsimp [D]
    rw [hnext]
    rw [hdiv0I,hdiv1I]
    simp only [Int.mul_sub]
    rfl
  have hCzero : C=0 := by
    by_cases hC : C=0
    · exact hC
    · exfalso
      obtain ⟨e,B,hodd,hfactor⟩ := integer_odd_factor C hC
      have hfactored : ∀ n, D n=(2:Int)^(p0.depth n)*
          (2*D (n+1)-(2:Int)^e*B) := by
        intro n
        simpa [hfactor] using hstep n
      obtain ⟨N,d,w,hd,hwlen,hperiod⟩ :=
        rescaled_odd_difference_has_period e B D p0.depth hodd hfactored
      have hperiod' : ∀ n k (hk : k<d),
          p0.depth (N+n*d+k)=w.get ⟨k,by simpa [hwlen] using hk⟩ := by
        intro n k hk
        exact hperiod n k (by simpa [hwlen] using hk)
      exact p0.no_eventually_periodic_shadow_path hL hrootpos hrootmargin
        N d hd w hwlen hperiod'
  have hzero : ∀ n, D n=(2:Int)^(p0.depth n)*(2*D (n+1)) := by
    intro n
    simpa [hCzero] using hstep n
  have hz : D 0 = 0 := zero_offset_difference_vanishes D p0.depth hzero 0
  constructor
  · dsimp [C] at hCzero
    omega
  · dsimp [D] at hz
    omega

#print axioms infinite_shadow_effective_code_injective
end BB6.Agent9CrossFeeder
