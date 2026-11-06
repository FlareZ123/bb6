import ValSixSecondInverse
import ReachAffine
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix
open BB6.Agent46

/-- A complementary valuation-six source-root sector has exactly
one viable immediate predecessor from the actual blank orbit,
although the abstract original section has two bounce branches. -/
theorem second_val_six_root_iff (x y : Nat)
    (hx:x%16=5) (hy:y%16=10) (hmod:(x+y+1)%256=192) :
    BB6.Agent3.CReach x y ↔ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
  constructor
  · rintro ⟨time,hr⟩
    cases time with
    | zero =>
        simp [BB6.Agent8Section.run] at hr
        omega
    | succ t =>
        cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
        | none => simp [BB6.Agent8Section.run,hp] at hr
        | some p =>
            rcases p with ⟨a,k⟩
            have hedge : secNext (a,k)=some (x,y) := by
              simpa [BB6.Agent8Section.run,hp] using hr
            rcases section_val_six_second_inverse a k x y hx hy hmod hedge with hdir | hbd
            · rcases hdir with ⟨ha,hkeq⟩
              have hkp : k=(y-2)/2 := by omega
              refine ⟨t,?_⟩
              simpa only [ha,hkp] using hp
            · rcases hbd with h1 | h3
              · obtain ⟨hodd,hbad,hlarge⟩ :=
                  second_first_bounce_forbidden x y a k hx hy hmod h1
                cases t with
                | zero =>
                    simp [BB6.Agent8Section.run] at hp
                    omega
                | succ t' =>
                    have hi := BB6.Agent3.blank_section_odd_image t' a k hp hlarge hodd
                    omega
              · obtain ⟨hk4,hkeven,hsum,hq5,hqodd,hqbad⟩ :=
                  second_third_bounce_forbidden x y a k hx hy hmod h3
                have hroot : BB6.Agent3.CReach a k := ⟨t,hp⟩
                have hgrand : BB6.Agent3.CReach (a+k-2) ((k-2)/2) :=
                  (BB6.Agent15.blank_reach_iff_affine a k hk4 hkeven hsum).mp hroot
                rcases hgrand with ⟨s,hs⟩
                cases s with
                | zero =>
                    simp [BB6.Agent8Section.run] at hs
                    omega
                | succ s =>
                    have hi := BB6.Agent3.blank_section_odd_image s
                      (a+k-2) ((k-2)/2) hs hq5 hqodd
                    omega
  · rintro ⟨t,hr⟩
    have hedge := direct_even_section x y (by omega) (by omega)
    refine ⟨t+1,?_⟩
    simpa [BB6.Agent8Section.run,hr,hedge]

#print axioms second_val_six_root_iff
end BB6.Agent3ValSix
