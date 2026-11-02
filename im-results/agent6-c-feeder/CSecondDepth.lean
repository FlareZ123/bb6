import SecondInverseDepth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent6
open BB6.Agent3 BB6.Agent46

/-- Every successful even-middle bounce has an odd output sum, including
    arbitrary recursion depth, directly from the exact inverse grammar. -/
theorem evenBack_sum_odd (x y k c : Nat) (h : EvenBack x y k c) :
    (x+y)%2=1 := by
  induction h with
  | small k hk hx hy => omega
  | large k hk hy hbd hx => omega
  | step k c hk hc h ih => exact ih

/-- Every exact section predecessor of this infinite odd-odd feeder family
    is the specified affine line. This checks every special section branch,
    and uses Agent38's global odd-bounce directness theorem. -/
theorem section_second_feeder_only_parent (q a k : Nat)
    (h : secNext (a,k)=some (4*(128*q+33)-1,2*(128*q+33)-1)) :
    a=24*(16*q+4) ∧ k=20*(16*q+4)-1 := by
  have hfour : ((4*(128*q+33)-1)+(2*(128*q+33)-1))%8=4 := by omega
  have hevenSum : ((4*(128*q+33)-1)+(2*(128*q+33)-1))%2=0 := by omega
  by_cases ha0 : a=0
  · by_cases hk0 : k=0
    · simp [secNext,exactSection,ha0,hk0] at h
    · by_cases hk1 : k=1
      · simp [secNext,exactSection,ha0,hk0,hk1] at h
        omega
      · have hb : (bounce 1 (2*k+1)).2=some (4*(128*q+33)-1,2*(128*q+33)-1) := by
          simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
        have hdir := BB6Agent38.bounce_odd_four_direct (2*k+1) 1
          (4*(128*q+33)-1) (2*(128*q+33)-1) (by decide) hb hfour
        omega
  · by_cases ha1 : a=1
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,ha1,hk0,hk1] at h
          omega
        · by_cases hk2 : k=2
          · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2] at h
            omega
          · by_cases hk3 : k=3
            · simp [secNext,exactSection,ha0,ha1,hk0,hk1,hk2,hk3] at h
              omega
            · have hb : (bounce 4 (2*k-3)).2=some (4*(128*q+33)-1,2*(128*q+33)-1) := by
                simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
              have he : EvenBack (4*(128*q+33)-1) (2*(128*q+33)-1) 4 (2*k-3) :=
                (evenBack_iff_bounce _ _ _ _ (by decide)).mpr hb
              have hsum := evenBack_sum_odd _ _ _ _ he
              omega
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,ha1,hk0] at h
        omega
      · by_cases hregion : 2*k≤a
        · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
          omega
        · have hb : (bounce (a-1) (2*k-a+3)).2=some (4*(128*q+33)-1,2*(128*q+33)-1) := by
            simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
          by_cases hodd : (a-1)%2=1
          · have hdir := BB6Agent38.bounce_odd_four_direct (2*k-a+3) (a-1)
              (4*(128*q+33)-1) (2*(128*q+33)-1) hodd hb hfour
            omega
          · have heven : (a-1)%2=0 := by omega
            have he : EvenBack (4*(128*q+33)-1) (2*(128*q+33)-1) (a-1) (2*k-a+3) :=
              (evenBack_iff_bounce _ _ _ _ heven).mpr hb
            have hsum := evenBack_sum_odd _ _ _ _ he
            omega

/-- Every orbit point of the exact feeder family would have to have a
    predecessor on the already universally excluded second inverse line. -/
theorem blank_no_second_feeder (q : Nat) :
    ¬ CReach (4*(128*q+33)-1) (2*(128*q+33)-1) := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hr
      omega
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at hr
      | some p =>
          rcases p with ⟨a,k⟩
          have ht : secNext (a,k)=some (4*(128*q+33)-1,2*(128*q+33)-1) := by
            simpa [BB6.Agent8Section.run,hp] using hr
          obtain ⟨ha,hk⟩ := section_second_feeder_only_parent q a k ht
          have hline : CReach (24*(16*q+4)) (20*(16*q+4)-1) := by
            refine ⟨t,?_⟩
            rw [ha,hk] at hp
            exact hp
          exact blank_no_twostep_target_line q hline

/-- Global full-blank exclusion of another genuinely infinite one-left
    source stopping configuration family. -/
theorem blank_no_one_128q33 (q : Nat) :
    ¬ CReach 1 (4*(128*q+33)) := by
  intro h
  have hf := (blank_one_four_iff_feeder (128*q+33) (by omega)).mp h
  exact blank_no_second_feeder q hf

private theorem depth592_implies_k132 (depth k : Nat)
    (hd : depth%1024=592)
    (hrel : 2*k+3*depth+8=2^(depth+1)*8) :
    k%512=132 := by
  have hp : 128 ∣ 2^(depth+1) := by
    change 2^7 ∣ 2^(depth+1)
    exact Nat.pow_dvd_pow 2 (by omega)
  obtain ⟨u,hu⟩ := hp
  have hdvd : 1024 ∣ 2^(depth+1)*8 := by
    refine ⟨u,?_⟩
    rw [hu]
    omega
  have hmod : (2*k+3*depth+8)%1024=0 := by
    rw [hrel]
    exact Nat.mod_eq_zero_of_dvd hdvd
  omega

/-- A further fully parameterized one-left halting depth class is impossible,
    independent of any finite trace or simulation cutoff. -/
theorem dyadic_one_depth_592_mod1024_excluded
    (k depth time : Nat) (hk : 4≤k)
    (hlevel : 2*k-3=haltLevel 4 depth)
    (hd : depth%1024=592)
    (hr : BB6.Agent8Section.run secNext time (some (5,1))=some (1,k)) :
    False := by
  have hc := haltLevel_closed 4 depth
  have hrel : 2*k+3*depth+8=2^(depth+1)*8 := by omega
  have hmod := depth592_implies_k132 depth k hd hrel
  have heq : k=4*(128*(k/512)+33) := by omega
  have hh : CReach 1 k := ⟨time,hr⟩
  rw [heq] at hh
  exact blank_no_one_128q33 (k/512) hh

#print axioms evenBack_sum_odd
#print axioms section_second_feeder_only_parent
#print axioms blank_no_second_feeder
#print axioms blank_no_one_128q33
#print axioms dyadic_one_depth_592_mod1024_excluded

end BB6.Agent6
