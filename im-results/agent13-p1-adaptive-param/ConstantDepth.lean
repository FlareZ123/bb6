import Lean
namespace BB6.Agent13ConstantDepth

/-- Exact integer obstruction associated with repeated t=1 inverse shadows. -/
def potential (L m z : Nat) : Int :=
  9*(z:Int)+16-6*((L:Int)+(m:Int))

/-- One exact P1 scalar inverse edge at depth t=1 scales the obstruction by 4. -/
theorem potential_step (L m z v zp : Nat)
    (hdiv : z=2*v)
    (hnext : 2*zp+1=L+m+1+v) :
    4*potential L (m+2) zp = potential L m z := by
  unfold potential
  omega

/-- The obstruction never vanishes for integral inverse coordinates. -/
theorem potential_ne_zero (L m z : Nat) : potential L m z ≠ 0 := by
  unfold potential
  omega

inductive Run1 (L : Nat) : Nat → Nat → Nat → Prop where
| zero (m z : Nat) : Run1 L 0 m z
| more {N m z v zp : Nat} : Run1 L N (m+2) zp →
    z=2*v → 2*zp+1=L+m+1+v → Run1 L (N+1) m z

/-- Any run of N consecutive depth-one inverse steps forces 4^N to
    divide a nonzero starting integer, so such runs are always finite. -/
theorem power_dvd_potential (L N m z : Nat) (h : Run1 L N m z) :
    (4:Int)^N ∣ potential L m z := by
  induction h with
  | zero m z =>
      simp
  | @more N m z v zp hprev hdiv hnext ih =>
      rcases ih with ⟨u,hu⟩
      refine ⟨u, ?_⟩
      calc
        potential L m z = 4*potential L (m+2) zp := (potential_step L m z v zp hdiv hnext).symm
        _ = 4*((4:Int)^N*u) := by rw [hu]
        _ = (4:Int)^(N+1)*u := by rw [Int.pow_succ']; ac_rfl

/-- A sharp exponential certificate bounds every homogeneous t=1 inverse run. -/
theorem run_length_power_bound (L N m z : Nat) (h : Run1 L N m z) :
    (4:Nat)^N ≤ (potential L m z).natAbs := by
  have hd : (4:Int)^N ∣ potential L m z := power_dvd_potential L N m z h
  have hnat : (4:Nat)^N ∣ (potential L m z).natAbs := by
    have hh := (Int.natAbs_dvd_natAbs).mpr hd
    simpa [Int.natAbs_pow, Int.natAbs_natCast] using hh
  have hpos : 0 < (potential L m z).natAbs :=
    Int.natAbs_pos.mpr (potential_ne_zero L m z)
  exact Nat.le_of_dvd hpos hnat

private theorem growth_four (n : Nat) : n < (4:Nat)^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

/-- Every fixed starting scalar node admits only finitely many consecutive
    exact depth-one inverse steps, with an explicit source arithmetic bound. -/
theorem no_unbounded_run1 (L m z : Nat)
    (hall : ∀ N : Nat, Run1 L N m z) : False := by
  let N := (potential L m z).natAbs
  have hp := run_length_power_bound L (N+1) m z (hall (N+1))
  have hg := growth_four (N+1)
  omega

#print axioms run_length_power_bound
#print axioms no_unbounded_run1
#print axioms potential_step
#print axioms potential_ne_zero
#print axioms power_dvd_potential
end BB6.Agent13ConstantDepth
