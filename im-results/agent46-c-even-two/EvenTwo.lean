import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46E2
open BB6.Agent46

/-- Every even high output whose counter sum is 2 mod 4 has one
    and only one source, in the direct affine branch. -/
theorem section_sum_two_even_iff_affine (a k x y : Nat)
    (hy : 4≤y) (heven : y%2=0) (hs : (x+y)%4=2) :
    secNext (a,k)=some (x,y) ↔
      a=x+y-2 ∧ k=(y-2)/2 := by
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
          have hh := BB6.Agent3.bounce_large_image _ _ _ _ hb hy
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
                have hh := BB6.Agent3.bounce_large_image _ _ _ _ hb hy
                omega
      · by_cases hk0 : k=0
        · simp [secNext,exactSection,ha0,ha1,hk0] at h
          omega
        · by_cases hregion : 2*k≤a
          · simp [secNext,exactSection,ha0,ha1,hk0,hregion] at h
            omega
          · have hb : (bounce (a-1) (2*k-a+3)).2=some (x,y) := by
              simpa only [secNext,exactSection,if_neg ha0,if_neg ha1,if_neg hk0,if_neg hregion] using h
            have hh := BB6.Agent3.bounce_large_image _ _ _ _ hb hy
            omega
  · rintro ⟨rfl,rfl⟩
    have ha0 : x+y-2≠0 := by omega
    have ha1 : x+y-2≠1 := by omega
    have hk0 : (y-2)/2≠0 := by omega
    have hreg : 2*((y-2)/2)≤x+y-2 := by omega
    simp [secNext,exactSection,ha0,ha1,hk0,hreg]
    omega


/-- Exact all-time blank-section reachability reduction for even-right outputs
    whose counter sum has residue two modulo four. -/
theorem blank_reach_iff_even_two (x y : Nat)
    (hy : 4≤y) (heven : y%2=0) (hs : (x+y)%4=2) :
    (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1))=some (x,y)) ↔
    (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1))=
      some (x+y-2,(y-2)/2)) := by
  let a := x+y-2
  let k := (y-2)/2
  have hedge : BB6.Agent46.secNext (a,k)=some (x,y) :=
    (section_sum_two_even_iff_affine a k x y hy heven hs).mpr ⟨rfl,rfl⟩
  change (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1))=some (x,y)) ↔
    (∃ n, BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1))=some (a,k))
  constructor
  · rintro ⟨n,hn⟩
    cases n with
    | zero =>
        simp [BB6.Agent8Section.run] at hn
        omega
    | succ n =>
        cases hr : BB6.Agent8Section.run BB6.Agent46.secNext n (some (5,1)) with
        | none => simp [BB6.Agent8Section.run,hr] at hn
        | some p =>
            rcases p with ⟨b,c⟩
            have hed : BB6.Agent46.secNext (b,c)=some (x,y) := by
              simpa [BB6.Agent8Section.run,hr] using hn
            have eq := (section_sum_two_even_iff_affine b c x y hy heven hs).mp hed
            have hb : b=a := by omega
            have hc : c=k := by omega
            refine ⟨n,?_⟩
            rwa [hb,hc] at hr
  · rintro ⟨n,hn⟩
    refine ⟨n+1,?_⟩
    simp [BB6.Agent8Section.run,hn,hedge]

#print axioms section_sum_two_even_iff_affine
#print axioms blank_reach_iff_even_two
end BB6.Agent46E2
