import OddSevenInverse
import OddSpecialLift
import Lean.Elab.Tactic.Omega

namespace BB6.Agent19Seven
open BB6.Agent46

/-- Source-complete all-time nonreachability through a nonunique
    sum-seven modulo eight inverse region. Both authentic source
    predecessor branches are root-forbidden. -/
theorem blank_no_sumseven_new (u v : Nat) (hv : 1≤v) :
    ¬ BB6.Agent3.CReach (32*u+1) (256*v+46) := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hr
  | succ t =>
      cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
      | none => simp [BB6.Agent8Section.run,hp] at hr
      | some p =>
          rcases p with ⟨a,k⟩
          have hedge : secNext (a,k)=some (32*u+1,256*v+46) := by
            simpa [BB6.Agent8Section.run,hp] using hr
          rcases section_sumseven_target_inverse a k u v hv hedge with hdir | hbd
          · rcases hdir with ⟨ha,hk⟩
            subst a
            subst k
            have heq : 32*u+256*v+45=16*(2*u+16*v+2)+13 := by omega
            rw [heq] at hp
            exact BB6.Agent19Special.blank_no_special_lift_a
              (2*u+16*v+2) v hv ⟨t,hp⟩
          · rcases hbd with ⟨ha,hk⟩
            subst a
            subst k
            cases t with
            | zero =>
                simp [BB6.Agent8Section.run] at hp
            | succ t' =>
                have hi := BB6.Agent3.blank_section_odd_image t'
                  (8*u+64*v+9) (12*u+224*v+37) hp (by omega) (by omega)
                omega

#print axioms blank_no_sumseven_new
end BB6.Agent19Seven
