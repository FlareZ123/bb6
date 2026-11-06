import OddSevenGeneralInverse
import EvenRightSixOrbit
import OddOddLowVal
import Agent3COrbitIff
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Second
open BB6.Agent46

/-- Exact congruences forcing the alternative bounce-source parent
    into an odd/odd source gate whose only own predecessor violates the
    authentic blank orbit odd-image invariant. -/
private theorem second_branch_arithmetic (a k x y:Nat)
    (hx:x%2=1) (hy:y%8=2) (hmod:(x+y+1)%32=16)
    (hcyl:(5*x+9*y)%128=115) (hbig:48≤x+y+1)
    (hy6:6≤y) (ha:4*a+12=x+y+1) (hk:2*k+a+10=x+2*y) :
    a%2=1 ∧ k%2=1 ∧ (a+k)%16=8 ∧ 5≤k ∧ 24≤a+k ∧
    5≤((a+3*k-10)/4) ∧ ((a+3*k-10)/4)%2=1 ∧
    (((a+k-4)/2)+((a+3*k-10)/4))%4=1 := by
  omega

/-- A second distinct sum-seven sector whose genuine blank-root
    ancestry forces the direct-affine predecessor, even though the
    source inverse has a potentially different bounce predecessor. -/
theorem second_sumseven_forced_root_iff (x y : Nat)
    (hx:x%2=1) (hy:y%8=2) (hy6:6≤y)
    (hmod:(x+y+1)%32=16)
    (hcyl:(5*x+9*y)%128=115) (hbig:48≤x+y+1) :
    BB6.Agent3.CReach x y ↔
    BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
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
            rcases BB6.Agent19Seven.section_sumseven_mod32_inverse
                a k x y hx (by omega) hy6 hmod (by omega) hedge
              with hdir | hbd
            · rcases hdir with ⟨ha,hk⟩
              refine ⟨t,?_⟩
              have hkeq : k=(y-2)/2 := by omega
              simpa only [ha,hkeq] using hp
            · rcases hbd with ⟨ha,hk⟩
              obtain ⟨haa,hkk,hsum16,hk5,hsumBig,hp5,hpodd,hpbad⟩ :=
                second_branch_arithmetic a k x y hx hy hmod hcyl hbig hy6 ha hk
              have h4 : (a+k)%4=0 := by omega
              have hn16 : (a+k)%16≠0 := by omega
              have hroot : BB6.Agent3.CReach
                    ((a+k-4)/2) ((a+3*k-10)/4) := by
                simpa only [BB6.Agent3.CReach] using
                  (BB6.Agent3.oddodd_lowval_blank_reach_iff
                    a k haa hkk hk5 h4 hn16 hsumBig).mp ⟨t,hp⟩
              rcases hroot with ⟨n,hn⟩
              cases n with
              | zero =>
                  simp [BB6.Agent8Section.run] at hn
                  omega
              | succ n =>
                  have hi := BB6.Agent3.blank_section_odd_image n
                    ((a+k-4)/2) ((a+3*k-10)/4) hn hp5 hpodd
                  omega
  · rintro ⟨t,hr⟩
    have hedge := direct_even_section x y hy6 (by omega)
    refine ⟨t+1,?_⟩
    simpa [BB6.Agent8Section.run,hr,hedge]

#print axioms second_sumseven_forced_root_iff
end BB6.Agent19Second
