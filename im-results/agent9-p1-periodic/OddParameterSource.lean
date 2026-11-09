import SourcePeriodAllPeriods
import OddDifference

/-!
# Odd-offset scalar source inverse codes have disjoint infinite languages

Any two infinite source inverse-shadow histories with the same initial cost,
shared depths, and an odd difference in source L parameters would force an
eventually periodic depth tail. A single preserved source margin excludes this.
The other root may be arbitrary and need not satisfy a margin hypothesis.
-/

namespace BB6.Agent9CrossFeeder
open BB6.Precision

/-- A universal odd-L parity obstruction for synchronized infinite paths. -/
theorem odd_parameter_no_shared_depth_stream
    (L0 L1 root0 root1 : Nat)
    (p0 : InfiniteShadowPath L0 root0)
    (p1 : InfiniteShadowPath L1 root1)
    (hL : 8≤L0) (hrootpos : 0<root0) (hrootmargin : root0+4≤L0)
    (hodd : ((L1:Int)-(L0:Int))%2=1)
    (hm0 : p0.m 0=p1.m 0)
    (hsame : ∀ n, p0.depth n=p1.depth n) : False := by
  let B : Int := (L1:Int)-(L0:Int)
  let D : Nat → Int := fun n => (p1.z n:Int)-(p0.z n:Int)
  have heqm : ∀ n, p0.m n=p1.m n := by
    intro n
    induction n with
    | zero => exact hm0
    | succ n ih =>
        rw [p0.hm n,p1.hm n,←hsame n,ih]
  have hstep : ∀ n, D n=(2:Int)^(p0.depth n)*(2*D (n+1)-B) := by
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
    have hnext : 2*D (n+1)-B = (p1.quotient n:Int)-(p0.quotient n:Int) := by
      dsimp [D,B]
      simp only [Int.natCast_add, Int.natCast_mul] at hn0 hn1 ⊢
      have hm := heqm n
      have ht := hsame n
      omega
    dsimp [D]
    rw [hnext]
    rw [heq0I,heq1I]
    simp only [Int.mul_sub]
    rfl
  let M : Nat := (D 0).natAbs + B.natAbs
  have hboundD0 : -(M:Int) ≤ D 0 ∧ D 0 ≤ (M:Int) := by
    have hu := Int.le_natAbs (a := D 0)
    have hl := Int.le_natAbs (a := -D 0)
    rw [Int.natAbs_neg] at hl
    dsimp [M]
    omega
  have hboundB : -(M:Int) ≤ B ∧ B ≤ (M:Int) := by
    have hu := Int.le_natAbs (a := B)
    have hl := Int.le_natAbs (a := -B)
    rw [Int.natAbs_neg] at hl
    dsimp [M]
    omega
  obtain ⟨N,d,w,hd,hwlen,hperiod⟩ :=
    odd_difference_has_period M B D p0.depth hodd hboundB hboundD0 hstep
  have hperiod' : ∀ n k (hk : k<d),
      p0.depth (N+n*d+k)=w.get ⟨k,by simpa [hwlen] using hk⟩ := by
    intro n k hk
    exact hperiod n k (by simpa [hwlen] using hk)
  exact p0.no_eventually_periodic_shadow_path hL hrootpos hrootmargin N d hd w hwlen hperiod'

#print axioms odd_parameter_no_shared_depth_stream
end BB6.Agent9CrossFeeder
