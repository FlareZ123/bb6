import SourcePeriodAllPeriods
import OddRescale

/-!
# Uniform non-synchronization for all nonzero dyadic source-offset differences

If two source L parameters differ by 2^e times an odd integer, synchronized
infinite inverse-depth histories with equal initial cost are impossible when
one root has the inherited four-unit source margin. The theorem works for
arbitrarily large e and both signs of the odd factor.
-/

namespace BB6.Agent9CrossFeeder
open BB6.Precision

/-- Source obstruction after removing the full dyadic factor in L₁-L₀. -/
theorem scaled_odd_parameter_no_shared_depth_stream
    (L0 L1 root0 root1 : Nat) (e : Nat) (B : Int)
    (p0 : InfiniteShadowPath L0 root0)
    (p1 : InfiniteShadowPath L1 root1)
    (hL : 8≤L0) (hrootpos : 0<root0) (hrootmargin : root0+4≤L0)
    (hodd : B%2=1)
    (hC : ((L1:Int)-(L0:Int))=(2:Int)^e*B)
    (hm0 : p0.m 0=p1.m 0)
    (hsame : ∀ n, p0.depth n=p1.depth n) : False := by
  let D : Nat → Int := fun n => (p1.z n:Int)-(p0.z n:Int)
  have heqm : ∀ n, p0.m n=p1.m n := by
    intro n
    induction n with
    | zero => exact hm0
    | succ n ih =>
        rw [p0.hm n,p1.hm n,←hsame n,ih]
  have hstep : ∀ n, D n=(2:Int)^(p0.depth n)*(2*D (n+1)-(2:Int)^e*B) := by
    intro n
    let t := p0.depth n
    have heq0 := p0.hdiv n
    have heq1 := p1.hdiv n
    have hs : p1.depth n=t := by simp [t,←hsame n]
    rw [hs] at heq1
    have heq0I : (p0.z n:Int)=(2:Int)^t*(p0.quotient n:Int) := by
      exact_mod_cast heq0
    have heq1I : (p1.z n:Int)=(2:Int)^t*(p1.quotient n:Int) := by
      exact_mod_cast heq1
    have hn0 := congrArg (fun x:Nat => (x:Int)) (p0.hnext n)
    have hn1 := congrArg (fun x:Nat => (x:Int)) (p1.hnext n)
    have hnext0 : 2*D (n+1)-((L1:Int)-(L0:Int)) =
        (p1.quotient n:Int)-(p0.quotient n:Int) := by
      dsimp [D]
      simp only [Int.natCast_add, Int.natCast_mul] at hn0 hn1 ⊢
      have hm := heqm n
      have ht := hsame n
      omega
    have hnext : 2*D (n+1)-(2:Int)^e*B =
        (p1.quotient n:Int)-(p0.quotient n:Int) := by
      simpa [hC] using hnext0
    dsimp [D]
    rw [hnext]
    rw [heq0I,heq1I]
    simp only [Int.mul_sub]
    rfl
  obtain ⟨N,d,w,hd,hwlen,hperiod⟩ :=
    rescaled_odd_difference_has_period e B D p0.depth hodd hstep
  have hperiod' : ∀ n k (hk : k<d),
      p0.depth (N+n*d+k)=w.get ⟨k,by simpa [hwlen] using hk⟩ := by
    intro n k hk
    exact hperiod n k (by simpa [hwlen] using hk)
  exact p0.no_eventually_periodic_shadow_path hL hrootpos hrootmargin N d hd w hwlen hperiod'

#print axioms scaled_odd_parameter_no_shared_depth_stream
end BB6.Agent9CrossFeeder
