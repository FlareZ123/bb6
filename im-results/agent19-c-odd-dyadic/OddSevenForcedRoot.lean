import OddSevenGeneralInverse
import EvenRightSixOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Seven
open BB6.Agent46

/-- On the full odd/even 2-adic sum-seven sector with right counter 6
mod 8, the authentic blank orbit can reach a target exactly when it
reaches its unique viable direct-section parent. The alternative
bounce predecessor is impossible on the actual blank orbit. -/
theorem sumseven_forced_root_iff (x y : Nat)
    (hx : x%2=1) (hy : y%8=6)
    (hmod : (x+y+1)%32=16) (hbig : 48≤x+y+1) :
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
            rcases section_sumseven_mod32_inverse a k x y hx (by omega)
                (by omega) hmod hbig hedge with hdir | hbd
            · rcases hdir with ⟨ha,hk⟩
              refine ⟨t,?_⟩
              have ht : k=(y-2)/2 := by omega
              simpa only [ha,ht] using hp
            · rcases hbd with ⟨ha,hk⟩
              have hodd : k%2=1 := by omega
              have hlarge : 5≤k := by omega
              have hbad : (a+k)%4=2 := by omega
              cases t with
              | zero =>
                  simp [BB6.Agent8Section.run] at hp
                  omega
              | succ t' =>
                  have hi := BB6.Agent3.blank_section_odd_image t' a k hp hlarge hodd
                  omega
  · rintro ⟨t,hr⟩
    have hedge := direct_even_section x y (by omega) (by omega)
    refine ⟨t+1,?_⟩
    simpa [BB6.Agent8Section.run,hr,hedge]

#print axioms sumseven_forced_root_iff
end BB6.Agent19Seven
