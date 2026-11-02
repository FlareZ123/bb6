import C48Inverse
import ReachAffine
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Every section state in the affine family (768q+576,640q+479)
    is inaccessible to the authentic Machine C blank section. -/
theorem blank_no_c48_target (q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (768*q+576,640*q+479) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ t =>
    cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at h
    | some p =>
      rcases p with ⟨a,k⟩
      have ht : secNext (a,k)=some (768*q+576,640*q+479) := by
        simpa [BB6.Agent8Section.run,hp] using h
      rcases target_section_inverse48 q a k ht with ⟨ha,hk⟩ | ⟨ha,hk⟩
      · have hy : k%2=1 := by omega
        have hs : (a+k)%4=2 := by omega
        have hstart := BB6Agent38.blank_section_mod4 t a k hp hy hs
        have hfirst := (Prod.mk.inj hstart).1
        omega
      · have hparent :
          BB6.Agent8Section.run secNext t (some (5,1)) =
            some (176*q+129,936*q+696) := by
          simpa [ha,hk] using hp
        obtain ⟨tp,hprev⟩ :=
          (BB6.Agent15.blank_reach_iff_affine (176*q+129) (936*q+696)
            (by omega) (by omega) (by omega)).mp ⟨t,hparent⟩
        have hnorm :
            ((176*q+129)+(936*q+696)-2,((936*q+696)-2)/2) =
              (1112*q+823,468*q+347) := by
          apply Prod.mk.injEq.mpr
          constructor <;> omega
        rw [hnorm] at hprev
        have hstart := BB6Agent38.blank_section_mod4 tp
          (1112*q+823) (468*q+347) hprev (by omega) (by omega)
        have hfirst := (Prod.mk.inj hstart).1
        omega

#print axioms blank_no_c48_target
end BB6.Agent46
