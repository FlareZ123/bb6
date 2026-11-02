import AffineTarget
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- The genuine blank Machine C section never reaches the entire affine
    output family targeted by the fully quantified inverse theorem. -/
theorem blank_no_affine_target (q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (384*q+96,320*q+79) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ t =>
    cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at h
    | some p =>
      rcases p with ⟨a,k⟩
      have ht : secNext (a,k)=some (384*q+96,320*q+79) := by
        simpa [BB6.Agent8Section.run,hp] using h
      have hc := target_section_inverse q a k ht
      have hy : k%2=1 := by
        rcases hc with ⟨ha,hk⟩ | ⟨ha,hk⟩ <;> omega
      have hs : (a+k)%4=2 := by
        rcases hc with ⟨ha,hk⟩ | ⟨ha,hk⟩ <;> omega
      have hstart := BB6Agent38.blank_section_mod4 t a k hp hy hs
      have hfirst := (Prod.mk.inj hstart).1
      rcases hc with ⟨ha,hk⟩ | ⟨ha,hk⟩ <;> omega

#print axioms blank_no_affine_target
end BB6.Agent46
