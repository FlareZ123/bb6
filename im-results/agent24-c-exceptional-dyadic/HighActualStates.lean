import HighExplicitFamily
import HighOtherExplicit
import BlankParam
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

private theorem high_bound_B (m : Nat) :
    3*m+33 ≤ 31*2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2=(2*m+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- The second, complementary branch has a concrete natural immediate
    stopping counter for every increasing index in its source tower. -/
def highExplicitCounterB (n:Nat) : Nat :=
    31*2^(2*exceptionalIndexB n+2)-(3*exceptionalIndexB n+33)

/-- Every state in this infinite second family really is an immediate
    stopping input of the original Machine C section, and none is ever
    reachable from its authentic blank-root section. -/
theorem high_explicit_counter_B_unreachable (n:Nat) :
    secNext (59,highExplicitCounterB n)=none ∧
      ¬ BB6.Agent3.CReach 59 (highExplicitCounterB n) := by
  let m := exceptionalIndexB n
  have hb := high_bound_B m
  have hstop : highExplicitCounterB n+28+3*m+5 = 2^(2*m+2)*(28+3) := by
    change (31*2^(2*m+2)-(3*m+33))+28+3*m+5=2^(2*m+2)*(28+3)
    have hsub := Nat.sub_add_cancel hb
    omega
  have hhalt : secNext (59,highExplicitCounterB n)=none := by
    apply (BB6.Agent15.section_halts_iff_parametric 59 (highExplicitCounterB n)).mpr
    exact Or.inr (Or.inr ⟨28,m,by decide,by simpa [m] using hstop⟩)
  exact ⟨hhalt,explicit_high_other_unreachable n (highExplicitCounterB n) (by simpa [m] using hstop)⟩

private theorem high_bound_A (m : Nat) :
    3*m+5 ≤ 3*2^(2*m+2) := by
  induction m with
  | zero => decide
  | succ m ih =>
      have he : 2*(m+1)+2=(2*m+2)+2 := by omega
      rw [he,Nat.pow_add]
      simp only [show (2:Nat)^2=4 by decide]
      omega

/-- First branch likewise consists of actual, immediate stopping
    section inputs at each of infinitely many distinct dyadic depths. -/
theorem high_explicit_counter_A_unreachable (r:Nat)
    (hr:8≤r) (hr0:r%8=0) :
    secNext (3,highExplicitCounter r)=none ∧
      ¬ BB6.Agent3.CReach 3 (highExplicitCounter r) := by
  let m := exceptionalIndex r
  have hb := high_bound_A m
  have hstop : highExplicitCounter r+0+3*m+5 = 2^(2*m+2)*(0+3) := by
    change (3*2^(2*m+2)-(3*m+5))+0+3*m+5=2^(2*m+2)*(0+3)
    have hsub := Nat.sub_add_cancel hb
    omega
  have hhalt : secNext (3,highExplicitCounter r)=none := by
    apply (BB6.Agent15.section_halts_iff_parametric 3 (highExplicitCounter r)).mpr
    exact Or.inr (Or.inr ⟨0,m,by decide,by simpa [m] using hstop⟩)
  exact ⟨hhalt,high_explicit_counter_unreachable r hr hr0⟩

#print axioms high_explicit_counter_A_unreachable
#print axioms high_explicit_counter_B_unreachable
end BB6.Agent46
