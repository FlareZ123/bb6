import ThirdStageOddDepth
import GenericSection
import Lean.Elab.Tactic.Omega

namespace BB6Agent34
open BB6.Agent46

/-- Complete uniform original-section inverse for odd x,y with y>=5 and
    (x+y)%8=4. The exact predecessor is determined by two linear equations. -/
theorem section_odd_four_exact (a k x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hsum : (x+y)%8=4) :
    secNext (a,k)=some (x,y) ↔
      2*a+4=x+y ∧ 2*k+3=a+y := by
  constructor
  · intro h
    by_cases ha0 : a=0
    · by_cases hk0 : k=0
      · simp [secNext,exactSection,ha0,hk0] at h
      · by_cases hk1 : k=1
        · simp [secNext,exactSection,ha0,hk0,hk1] at h
          omega
        · have hb : (bounce 1 (2*k+1)).2=some (x,y) := by
            simpa only [secNext,exactSection,if_pos ha0,if_neg hk0,if_neg hk1] using h
          have hh := BB6Agent38.bounce_odd_one_sum0_mod8 (2*k+1) 1 x y (by decide) hb
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
              · have hb : (bounce 4 (2*k-3)).2=some (x,y) := by
                  simpa only [secNext,exactSection,if_neg ha0,if_pos ha1,if_neg hk0,if_neg hk1,if_neg hk2,if_neg hk3] using h
                have hh := BB6Agent38.bounce_even_sum_odd _ _ _ _ (by decide : 4%2=0) hb
                omega
      · by_cases hk0 : k=0
        · simp [secNext,exactSection,ha0,ha1,hk0] at h
          omega
        · by_cases hregion : 2*k≤a
          · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
            omega
          · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
              simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
            by_cases hodd : (a-1)%2=1
            · obtain ⟨hc,heqx,heqy,hbmod⟩ :=
                BB6Agent38.bounce_odd_four_direct _ _ _ _ hodd hb hsum
              constructor <;> omega
            · have heven : (a-1)%2=0 := by omega
              have hh := BB6Agent38.bounce_even_sum_odd _ _ _ _ heven hb
              omega
  · rintro ⟨ha,hk⟩
    have hage : 4≤a := by omega
    have ha0 : a≠0 := by omega
    have ha1 : a≠1 := by omega
    have hk0 : k≠0 := by omega
    have hregion : ¬2*k≤a := by omega
    have hKodd : (a-1)%2=1 := by omega
    have hcin : 4≤2*k-a+3 := by omega
    have hcmax : 2*k-a+3≤2*(a-1)+6 := by omega
    have hC : 2*k-a+3=y := by omega
    have hX : 2*(a-1)+6-y=x := by omega
    simp only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion]
    rw [hC]
    simp [bounce, (show ¬ y<4 by omega), hKodd, (show y≤2*(a-1)+6 by omega), hX]

def CReach (a k : Nat) : Prop :=
  ∃ t, BB6.Agent8Section.run secNext t (some (5,1))=some (a,k)

/-- Genuine blank-orbit all-time iff for the entire odd-odd sum-four sector. -/
theorem odd_four_reach_iff (x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hsum : (x+y)%8=4) :
    CReach x y ↔ ∃ a k, CReach a k ∧ 2*a+4=x+y ∧ 2*k+3=a+y := by
  constructor
  · rintro ⟨t,ht⟩
    cases t with
    | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
    | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at ht
      | some p =>
        rcases p with ⟨a,k⟩
        have hstep : secNext (a,k)=some (x,y) := by
          simpa [BB6.Agent8Section.run,hp] using ht
        have hpair := (section_odd_four_exact a k x y hx hy hy5 hsum).mp hstep
        exact ⟨a,k,⟨n,hp⟩,hpair.1,hpair.2⟩
  · rintro ⟨a,k,⟨n,hn⟩,ha,hk⟩
    refine ⟨n+1,?_⟩
    change (BB6.Agent8Section.run secNext n (some (5,1))).bind secNext=some (x,y)
    rw [hn]
    simp [(section_odd_four_exact a k x y hx hy hy5 hsum).mpr ⟨ha,hk⟩]

#print axioms section_odd_four_exact
#print axioms odd_four_reach_iff
theorem odd_four_unique_parent (x y : Nat)
    (hx : x%2=1) (hy : y%2=1) (hy5 : 5≤y)
    (hsum : (x+y)%8=4) :
    ∃ p : Nat × Nat, secNext p=some (x,y) ∧
      ∀ q : Nat × Nat, secNext q=some (x,y) → q=p := by
  let a : Nat := (x+y-4)/2
  let k : Nat := (a+y-3)/2
  have heqa : 2*a+4=x+y := by dsimp [a]; omega
  have heqk : 2*k+3=a+y := by dsimp [k]; omega
  refine ⟨(a,k), (section_odd_four_exact a k x y hx hy hy5 hsum).mpr ⟨heqa,heqk⟩, ?_⟩
  intro p hp
  rcases p with ⟨b,c⟩
  obtain ⟨hb,hc⟩ := (section_odd_four_exact b c x y hx hy hy5 hsum).mp hp
  apply Prod.ext <;> omega

#print axioms odd_four_unique_parent
end BB6Agent34
