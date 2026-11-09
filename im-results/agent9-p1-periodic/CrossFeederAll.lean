import SourcePeriodAllPeriods
import OddDifference

/-!
# Opposite P1 feeder roots have disjoint infinite inverse-depth languages

A shared infinite depth stream across roots (16q₀+8, 12q₀+4) and
(16q₁+9, 10q₁+4) forces an eventually periodic depth tail by a bounded
integer difference dynamical system, contradicting the original-source
all-period theorem. The parameters q₀ and q₁ need not coincide.
-/

namespace BB6.Agent9CrossFeeder

open BB6.Precision

/-- Opposite original P1 shadow feeder families, with any independent
natural parameters, cannot admit a common infinite inverse-depth sequence. -/
theorem no_common_cross_feeder_depth_stream (q0 q1 : Nat)
    (p0 : InfiniteShadowPath (16*q0+8) (12*q0+4))
    (p1 : InfiniteShadowPath (16*q1+9) (10*q1+4))
    (hm0 : p0.m 0=0) (hm1 : p1.m 0=0)
    (hsame : ∀ n, p0.depth n=p1.depth n) : False := by
  let B : Int := (16*q1+9:Nat)-(16*q0+8:Nat)
  let D : Nat → Int := fun n => (p1.z n:Int)-(p0.z n:Int)
  have hodd : B%2=1 := by
    have hB : B=(16:Int)*((q1:Int)-(q0:Int))+1 := by
      dsimp [B]
      omega
    rw [hB]
    omega
  have heqm : ∀ n, p0.m n=p1.m n := by
    intro n
    induction n with
    | zero => omega
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
  have hL : 8≤16*q0+8 := by omega
  have hrootpos : 0<12*q0+4 := by omega
  have hrootmargin : 12*q0+4+4≤16*q0+8 := by omega
  exact p0.no_eventually_periodic_shadow_path hL hrootpos hrootmargin N d hd w hwlen hperiod'

#print axioms no_common_cross_feeder_depth_stream

end BB6.Agent9CrossFeeder
