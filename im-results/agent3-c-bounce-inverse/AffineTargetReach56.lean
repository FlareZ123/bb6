import AffineTarget56
import Agent38SectionParity
import ThirdStageOddDepth
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Second infinite affine target family is inaccessible from the authentic
    Machine C blank entry at every finite section time. -/
theorem blank_no_affine_target56 (q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (1536*q+672,1280*q+559) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ t =>
    cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at h
    | some p =>
      rcases p with ⟨a,k⟩
      have ht : secNext (a,k)=some (1536*q+672,1280*q+559) := by
        simpa [BB6.Agent8Section.run,hp] using h
      rcases target_section_inverse56 q a k ht with ⟨ha,hk⟩ | ⟨ha,hk⟩
      · have hy : k%2=1 := by omega
        have hs : (a+k)%4=2 := by omega
        have hstart := BB6Agent38.blank_section_mod4 t a k hp hy hs
        have hfirst := (Prod.mk.inj hstart).1
        omega
      · have hcontra := BB6Agent38.blank_section_no_odd_special
          t a k (by omega) (by omega) (by omega) (by omega)
        exact hcontra hp

#print axioms blank_no_affine_target56
end BB6.Agent46
