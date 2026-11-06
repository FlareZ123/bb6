import Lean.Elab.Tactic.Omega
set_option maxRecDepth 4096
set_option maxHeartbeats 0

namespace BB6.Agent48.SpaceNeedleFive

/-- Infinite common progression for five legal, distinct terminal feeder valuations. -/
def exponent (t : Nat) : Nat :=
  115559872543250362436240044170777864346536 +
  136996046966732361806630100489564981018852 * t

private theorem periodic_mod (d K T b : Nat)
    (hbase : (2:Nat)^K % d = b % d)
    (hperiod : (2:Nat)^T % d = 1) (t : Nat) :
    (2:Nat)^(K+T*t) % d = b % d := by
  induction t with
  | zero => simpa using hbase
  | succ t ih =>
    have he : K+T*(t+1) = (K+T*t)+T := by
      simp [Nat.mul_add, Nat.add_left_comm, Nat.add_comm]
    rw [he, Nat.pow_add, Nat.mul_mod]
    rw [ih, hperiod]
    simp

private theorem period_from_powMod (d b : Nat) (hb : b<d)
    (hbase : Nat.powMod 2 115559872543250362436240044170777864346536 d=b)
    (hperiod : Nat.powMod 2 136996046966732361806630100489564981018852 d=1)
    (t : Nat) :
    (2:Nat)^(exponent t) % d = b := by
  have ha : (2:Nat)^115559872543250362436240044170777864346536 % d = b % d := by
    rw [← Nat.powMod_def, hbase]
    exact (Nat.mod_eq_of_lt hb).symm
  have hp : (2:Nat)^136996046966732361806630100489564981018852 % d = 1 := by
    rw [← Nat.powMod_def, hperiod]
  have hh := periodic_mod d _ _ b ha hp t
  simpa only [exponent, Nat.mod_eq_of_lt hb] using hh

/-- A kernel-checked symbolic, all-t modular five-way certificate. -/
theorem five_moduli (t : Nat) :
    (2:Nat)^(exponent t) % 5 = 1 ∧
    (2:Nat)^(exponent t) % 19 = 11 ∧
    (2:Nat)^(exponent t) % 2097155 = 1048596 ∧
    (2:Nat)^(exponent t) % 549755813891 = 274877906982 ∧
    (2:Nat)^(exponent t) % 19342813113834066795298819 =
      9671406556917033397649491 := by
  have h0 : Nat.powMod 2 115559872543250362436240044170777864346536 5 = 1 := by decide
  have p0 : Nat.powMod 2 136996046966732361806630100489564981018852 5 = 1 := by decide
  have h3 : Nat.powMod 2 115559872543250362436240044170777864346536 19 = 11 := by decide
  have p3 : Nat.powMod 2 136996046966732361806630100489564981018852 19 = 1 := by decide
  have h20 : Nat.powMod 2 115559872543250362436240044170777864346536 2097155 = 1048596 := by decide
  have p20 : Nat.powMod 2 136996046966732361806630100489564981018852 2097155 = 1 := by decide
  have h38 : Nat.powMod 2 115559872543250362436240044170777864346536 549755813891 = 274877906982 := by decide
  have p38 : Nat.powMod 2 136996046966732361806630100489564981018852 549755813891 = 1 := by decide
  have h83 : Nat.powMod 2 115559872543250362436240044170777864346536 19342813113834066795298819 =
      9671406556917033397649491 := by decide
  have p83 : Nat.powMod 2 136996046966732361806630100489564981018852 19342813113834066795298819 = 1 := by decide
  exact ⟨period_from_powMod _ _ (by decide) h0 p0 t,
    period_from_powMod _ _ (by decide) h3 p3 t,
    period_from_powMod _ _ (by decide) h20 p20 t,
    period_from_powMod _ _ (by decide) h38 p38 t,
    period_from_powMod _ _ (by decide) h83 p83 t⟩

private theorem affine_parent (d r x : Nat)
    (hd : 0<d) (hx : d+r ≤ x) (hmod : x%d=r) :
    ∃ q : Nat, d*q+(d+r)=x := by
  have hQ : 1 ≤ x/d := by
    by_cases hzero : x/d=0
    · have hdiv := Nat.mod_add_div x d
      simp [hzero,hmod] at hdiv
      omega
    · exact Nat.one_le_iff_ne_zero.mpr hzero
  refine ⟨x/d-1, ?_⟩
  have hsub : x/d-1+1=x/d := Nat.sub_add_cancel hQ
  have hadd : d*(x/d-1)+d=d*(x/d) := by
    calc
      d*(x/d-1)+d = d*((x/d-1)+1) := by rw [Nat.mul_add]; omega
      _ = d*(x/d) := by rw [hsub]
  have hdiv := Nat.mod_add_div x d
  omega

/-- The five valuations each give a legitimate nonnegative quotient. -/
theorem five_equations (t : Nat) :
    ∃ q0 q3 q20 q38 q83 : Nat,
      5*q0+6=(2:Nat)^(exponent t) ∧
      19*q3+30=(2:Nat)^(exponent t) ∧
      2097155*q20+3145751=(2:Nat)^(exponent t) ∧
      549755813891*q38+824633720873=(2:Nat)^(exponent t) ∧
      19342813113834066795298819*q83+29014219670751100192948310=
          (2:Nat)^(exponent t) := by
  have he : 85 ≤ exponent t := by unfold exponent; omega
  have hpow := Nat.pow_le_pow_right (by decide : 0<(2:Nat)) he
  have h85 : (2:Nat)^85=38685626227668133590597632 := by decide
  have hlarge : 29014219670751100192948310 ≤ (2:Nat)^(exponent t) := by omega
  obtain ⟨h0,h3,h20,h38,h83⟩ := five_moduli t
  obtain ⟨q0,hq0⟩ := affine_parent 5 1 _ (by decide) (Nat.le_trans (by decide) hlarge) h0
  obtain ⟨q3,hq3⟩ := affine_parent 19 11 _ (by decide) (Nat.le_trans (by decide) hlarge) h3
  obtain ⟨q20,hq20⟩ := affine_parent 2097155 1048596 _ (by decide) (Nat.le_trans (by decide) hlarge) h20
  obtain ⟨q38,hq38⟩ := affine_parent 549755813891 274877906982 _ (by decide) (Nat.le_trans (by decide) hlarge) h38
  obtain ⟨q83,hq83⟩ := affine_parent 19342813113834066795298819 9671406556917033397649491 _
    (by decide) (Nat.le_trans (by decide) hlarge) h83
  exact ⟨q0,q3,q20,q38,q83,hq0,hq3,hq20,hq38,hq83⟩

/-- Valuation levels force genuine distinction among the five synthetic sources. -/
theorem five_distinct (q0 q3 q20 q38 q83 : Nat) :
    let d0 := 2*q0+1
    let d3 := 16*q3+22
    let d20 := 2097152*q20+3145726
    let d38 := 549755813888*q38+824633720830
    let d83 := 19342813113834066795298816*q83+29014219670751100192948222
    d0≠d3 ∧ d0≠d20 ∧ d0≠d38 ∧ d0≠d83 ∧
    d3≠d20 ∧ d3≠d38 ∧ d3≠d83 ∧
    d20≠d38 ∧ d20≠d83 ∧ d38≠d83 := by
  dsimp
  omega

#print axioms five_moduli
#print axioms five_equations
#print axioms five_distinct
end BB6.Agent48.SpaceNeedleFive
