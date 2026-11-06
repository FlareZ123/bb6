import ValSixInverse
import EvenRightSixOrbit
import ReachAffine
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3ValSix
open BB6.Agent46

theorem val_six_blank_unreachable (x y : Nat)
    (hx:x%16=13) (hy:y%16=2) (hy34:34≤y)
    (hmod:(x+y+1)%256=64) (hbig:320≤x+y+1) :
    ¬ BB6.Agent3.CReach x y := by
  intro h
  rcases h with ⟨time,hr⟩
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
          rcases section_val_six_inverse a k x y hx hy hy34 hmod hbig hedge with hdir | hbd
          · rcases hdir with ⟨ha,hkeq⟩
            have hkp : k=(y-2)/2 := by omega
            have hroot : BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
              refine ⟨t,?_⟩
              simpa only [ha,hkp] using hp
            let aa := x+y-2
            let kk := (y-2)/2
            obtain ⟨hk4,hkeven,hsum,hq5,hqodd,hqbad⟩ :=
              direct_forbidden x y hx hy hy34 hmod
            have hgrand : BB6.Agent3.CReach (aa+kk-2) ((kk-2)/2) :=
              (BB6.Agent15.blank_reach_iff_affine aa kk hk4 hkeven hsum).mp hroot
            rcases hgrand with ⟨s,hs⟩
            cases s with
            | zero =>
                simp [BB6.Agent8Section.run] at hs
                omega
            | succ s =>
                have hi := BB6.Agent3.blank_section_odd_image s
                  (aa+kk-2) ((kk-2)/2) hs hq5 hqodd
                omega
          · rcases hbd with h1 | h3
            · obtain ⟨hodd,hbad,hlarge⟩ :=
                first_bounce_forbidden x y a k hx hy hmod h1
              cases t with
              | zero =>
                  simp [BB6.Agent8Section.run] at hp
                  omega
              | succ t' =>
                  have hi := BB6.Agent3.blank_section_odd_image t' a k hp hlarge hodd
                  omega
            · obtain ⟨hk4,hkeven,hsum,hq5,hqodd,hqbad⟩ :=
                third_bounce_forbidden x y a k hx hy hmod hbig h3
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

#print axioms val_six_blank_unreachable
end BB6.Agent3ValSix
