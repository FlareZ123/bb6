import EvenEvenInverse
import Agent3COrbitIff
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent46

/-- For all even-even outputs whose sum has 2-adic valuation at most
    two, and right output at least six, the direct affine source is
    the unique original-section predecessor. This covers every
    nonzero even residue modulo eight. -/
theorem section_eveneven_nonzero_mod8_inverse (a k x y : Nat)
    (hy : 6≤y) (hx : x%2=0) (he : y%2=0)
    (hs : (x+y)%8≠0)
    (h : secNext (a,k)=some (x,y)) :
    a=x+y-2 ∧ k=(y-2)/2 := by
  have hcases : (x+y)%8=2 ∨ (x+y)%8=4 ∨ (x+y)%8=6 := by omega
  rcases hcases with h2 | h4 | h6
  · exact section_even_sum_two_mod4_inverse a k x y hy he (by omega) h
  · exact section_eveneven_sum_four_mod8_inverse a k x y hy hx he h4 h
  · exact section_even_sum_two_mod4_inverse a k x y hy he (by omega) h

private theorem direct_even_section (x y : Nat)
    (hy : 6≤y) (he : y%2=0) :
    secNext (x+y-2,(y-2)/2)=some (x,y) := by
  have ha0 : x+y-2≠0 := by omega
  have ha1 : x+y-2≠1 := by omega
  have hk0 : (y-2)/2≠0 := by omega
  have hreg : 2*((y-2)/2)≤x+y-2 := by omega
  simp [secNext,exactSection,ha0,ha1,hk0,hreg]
  omega

theorem section_eveneven_nonzero_mod8_iff (a k x y : Nat)
    (hy : 6≤y) (hx : x%2=0) (he : y%2=0)
    (hs : (x+y)%8≠0) :
    secNext (a,k)=some (x,y) ↔ a=x+y-2 ∧ k=(y-2)/2 := by
  constructor
  · exact section_eveneven_nonzero_mod8_inverse a k x y hy hx he hs
  · rintro ⟨rfl,rfl⟩
    exact direct_even_section x y hy he

/-- Full blank-orbit equivalence for the entire even-even nonzero
    sum sector, with no recursion-depth or simulation cutoff. -/
theorem eveneven_nonzero_blank_reach_iff (x y : Nat)
    (hy : 6≤y) (hx : x%2=0) (he : y%2=0)
    (hs : (x+y)%8≠0) :
    BB6.Agent3.CReach x y ↔ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
  constructor
  · rintro ⟨time,hr⟩
    cases time with
    | zero =>
        simp [BB6.Agent8Section.run] at hr
        omega
    | succ n =>
        cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
        | none => simp [BB6.Agent8Section.run,hp] at hr
        | some p =>
            rcases p with ⟨a,k⟩
            have hed : secNext (a,k)=some (x,y) := by
              simpa [BB6.Agent8Section.run,hp] using hr
            obtain ⟨ha,hk⟩ :=
              (section_eveneven_nonzero_mod8_iff a k x y hy hx he hs).mp hed
            refine ⟨n,?_⟩
            simpa only [ha,hk] using hp
  · rintro ⟨n,hr⟩
    have hedge := direct_even_section x y hy he
    refine ⟨n+1,?_⟩
    simpa [BB6.Agent8Section.run,hr,hedge]

/-- Executable all-depth forced parent normalizer. -/
def evenEvenGate (x y : Nat) : Prop :=
  6≤y ∧ x%2=0 ∧ y%2=0 ∧ (x+y)%8≠0

instance evenEvenGate_decidable (x y : Nat) : Decidable (evenEvenGate x y) := by
  unfold evenEvenGate
  infer_instance

def evenEvenNormalize (x y : Nat) : Nat × Nat :=
  if hg : evenEvenGate x y then
    evenEvenNormalize (x+y-2) ((y-2)/2)
  else (x,y)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [evenEvenGate] at *
    omega

theorem blank_reach_iff_evenEvenNormalize (x y : Nat) :
    BB6.Agent3.CReach x y ↔
    BB6.Agent3.CReach (evenEvenNormalize x y).1 (evenEvenNormalize x y).2 := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y with
  | ind z ih =>
      unfold evenEvenNormalize
      by_cases hg : evenEvenGate x y
      · rw [dif_pos hg]
        rcases hg with ⟨hy,hx,he,hs⟩
        have hh := eveneven_nonzero_blank_reach_iff x y hy hx he hs
        have hlt : (x+y-2)+2*((y-2)/2)<z := by omega
        have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
        exact hh.trans hrec
      · rw [dif_neg hg]

#print axioms section_eveneven_nonzero_mod8_inverse
#print axioms section_eveneven_nonzero_mod8_iff
#print axioms eveneven_nonzero_blank_reach_iff
#print axioms blank_reach_iff_evenEvenNormalize

end BB6.Agent46
