import SectionRank
import MachineCLinearRankRigidity
import Lean.Elab.Tactic.Omega

namespace BB6.LinearRankRigidity
open BB6.Agent46

/-- Direct-section family; it forces v ≥ 2u for globally monotone ranks. -/
theorem machine_c_direct_family (k : Nat) (hk : 1≤k) :
    secNext (2*k,k)=some (0,2*k+2) := by
  have ha0 : 2*k≠0 := by omega
  have ha1 : 2*k≠1 := by omega
  have hk0 : k≠0 := by omega
  have hdom : 2*k≤2*k := Nat.le_refl _
  simp [secNext,exactSection,ha0,ha1,hk0,hdom]

/-- The first (c=4) even-bounce exit; it forces v ≤ 2u. -/
theorem machine_c_short_bounce_family (k : Nat) (hk : 1≤k) :
    secNext (2*k+1,k+1)=some (4*k+2,3) := by
  have ha0 : 2*k+1≠0 := by omega
  have ha1 : 2*k+1≠1 := by omega
  have h2k : 2*k≠0 := by omega
  have hk0 : k+1≠0 := by omega
  have hnotdom : ¬(2*(k+1)≤2*k+1) := by omega
  have ha : 2*k+1-1=2*k := by omega
  have hc : 2*(k+1)-(2*k+1)+3=4 := by omega
  have he : (2*k)%2≠1 := by omega
  have hb : (bounce (2*k) 4).2=some (4*k+2,3) := by
    rw [bounce]
    simp only [show ¬(4:Nat)<4 by decide, if_false, he,
      show (4:Nat)=4 by rfl, if_true]
    have heq : 2*(2*k)+2=4*k+2 := by omega
    simp [heq]
  simp [secNext,exactSection,ha0,ha1,h2k,hk0,hnotdom,ha,hc,hb]

/-- Full original-source classification of all globally nondecreasing
nonnegative integral linear section potentials. -/
theorem machine_c_linear_unique (u v:Nat) :
    (∀ a k x y, secNext (a,k)=some (x,y) → weight u v a k≤weight u v x y)
     ↔ v=2*u :=
  unique_linear_nondecrease secNext BB6.Agent3.section_rank_strict
    machine_c_direct_family machine_c_short_bounce_family u v

/-- Full original-source classification of strictly increasing linear
potentials: exactly the positive multiples of a+2k. -/
theorem machine_c_linear_strict (u v:Nat) :
    (∀ a k x y, secNext (a,k)=some (x,y) → weight u v a k < weight u v x y)
     ↔ 0<u ∧ v=2*u :=
  unique_linear_strict secNext BB6.Agent3.section_rank_strict
    machine_c_direct_family machine_c_short_bounce_family u v

#print axioms machine_c_direct_family
#print axioms machine_c_short_bounce_family
#print axioms machine_c_linear_unique
#print axioms machine_c_linear_strict
end BB6.LinearRankRigidity
