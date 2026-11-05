import OddEvenInverse
import ExtraEvenOrbit
import SectionAffineInverse
import Agent3CImage
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192
namespace BB6.Agent46

/-- Maximal low-residue uniqueness rule for original Machine C even-right
    returns: every sum class except 0 and 7 mod8 is direct-affine-only. -/
theorem section_even_right_six_inverse (a k x y : Nat)
    (hy : 6≤y) (he : y%2=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7)
    (h : secNext (a,k)=some (x,y)) :
    a=x+y-2 ∧ k=(y-2)/2 := by
  by_cases hx : x%2=0
  · exact section_eveneven_nonzero_mod8_inverse a k x y hy hx he h0 h
  · have hc : (x+y)%8=1 ∨ (x+y)%8=3 ∨ (x+y)%8=5 := by omega
    rcases hc with h1 | h3 | h5
    · exact (BB6.Agent15.section_sum_one_even_iff_affine
        a k x y (by omega) he (by omega)).mp h
    · exact section_oddeven_sum3_mod8_inverse
        a k x y hy (by omega) he h3 h
    · exact (BB6.Agent15.section_sum_one_even_iff_affine
        a k x y (by omega) he (by omega)).mp h

theorem section_even_right_six_iff (a k x y : Nat)
    (hy : 6≤y) (he : y%2=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7) :
    secNext (a,k)=some (x,y) ↔ a=x+y-2 ∧ k=(y-2)/2 := by
  constructor
  · exact section_even_right_six_inverse a k x y hy he h0 h7
  · rintro ⟨rfl,rfl⟩
    exact direct_even_section x y hy he

theorem six_even_right_blank_reach_iff (x y : Nat)
    (hy : 6≤y) (he : y%2=0)
    (h0 : (x+y)%8≠0) (h7 : (x+y)%8≠7) :
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
              (section_even_right_six_iff a k x y hy he h0 h7).mp hed
            refine ⟨n,?_⟩
            simpa only [ha,hk] using hp
  · rintro ⟨n,hr⟩
    have hedge := direct_even_section x y hy he
    refine ⟨n+1,?_⟩
    simpa [BB6.Agent8Section.run,hr,hedge]

/-- Every applied normalization edge strictly lowers x+2y by four. -/
def sixEvenRightGate (x y : Nat) : Prop :=
  6≤y ∧ y%2=0 ∧ (x+y)%8≠0 ∧ (x+y)%8≠7

instance sixEvenRightGate_decidable (x y : Nat) :
    Decidable (sixEvenRightGate x y) := by
  unfold sixEvenRightGate
  infer_instance

def sixEvenRightNormalize (x y : Nat) : Nat × Nat :=
  if hg : sixEvenRightGate x y then
    sixEvenRightNormalize (x+y-2) ((y-2)/2)
  else (x,y)
termination_by x+2*y
decreasing_by
  all_goals
    simp_wf
    simp only [sixEvenRightGate] at *
    omega

theorem blank_reach_iff_sixEvenRightNormalize (x y : Nat) :
    BB6.Agent3.CReach x y ↔
    BB6.Agent3.CReach (sixEvenRightNormalize x y).1
                       (sixEvenRightNormalize x y).2 := by
  generalize hz : x+2*y=z
  induction z using Nat.strongRecOn generalizing x y with
  | ind z ih =>
      unfold sixEvenRightNormalize
      by_cases hg : sixEvenRightGate x y
      · rw [dif_pos hg]
        rcases hg with ⟨hy,he,h0,h7⟩
        have hh := six_even_right_blank_reach_iff x y hy he h0 h7
        have hlt : (x+y-2)+2*((y-2)/2)<z := by omega
        have hrec := ih _ hlt (x+y-2) ((y-2)/2) (by rfl)
        exact hh.trans hrec
      · rw [dif_neg hg]

/-- Executable sufficient nonreachability test on the authentic blank
    section orbit, certified for arbitrarily large input counters. -/
def sixEvenRightExcluded (x y : Nat) : Bool :=
  let p := sixEvenRightNormalize x y
  decide (5≤p.2 ∧ p.2%2=1 ∧
    ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2))

theorem sixEvenRightExcluded_sound (x y : Nat)
    (hex : sixEvenRightExcluded x y = true) :
    ∀ time, BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  intro time ht
  obtain ⟨n,hn⟩ :=
    (blank_reach_iff_sixEvenRightNormalize x y).mp ⟨time,ht⟩
  have hh : 5≤(sixEvenRightNormalize x y).2 ∧
      (sixEvenRightNormalize x y).2%2=1 ∧
      (((sixEvenRightNormalize x y).1+(sixEvenRightNormalize x y).2)%4=1 ∨
       ((sixEvenRightNormalize x y).1+(sixEvenRightNormalize x y).2)%4=2) := by
    simpa [sixEvenRightExcluded] using (of_decide_eq_true hex)
  rcases hh with ⟨hy,ho,hbad⟩
  cases n with
  | zero =>
      have heq : ((sixEvenRightNormalize x y).1,
          (sixEvenRightNormalize x y).2)=(5,1) := by
        apply Option.some.inj
        simpa [BB6.Agent8Section.run] using hn.symm
      have hp := congrArg Prod.snd heq
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (sixEvenRightNormalize x y).1 (sixEvenRightNormalize x y).2 hn hy ho
      omega

#print axioms section_even_right_six_inverse
#print axioms section_even_right_six_iff
#print axioms six_even_right_blank_reach_iff
#print axioms blank_reach_iff_sixEvenRightNormalize
#print axioms sixEvenRightExcluded_sound

end BB6.Agent46
