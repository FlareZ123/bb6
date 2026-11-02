import C16Inverse
import ReachAffine
import ThirdStageOddDepth
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Complete all-time exclusion for the genuine Machine C blank section
    of the affine class t=256q+16, using both the global mod-four and the
    deeper odd-special output invariant. -/
theorem blank_no_c16_target (q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (3072*q+192,2560*q+159) := by
  intro h
  cases time with
  | zero => simp [BB6.Agent8Section.run] at h
  | succ t =>
    cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at h
    | some p =>
      rcases p with ⟨a,k⟩
      have ht : secNext (a,k)=some (3072*q+192,2560*q+159) := by
        simpa [BB6.Agent8Section.run,hp] using h
      rcases target_section_inverse16 q a k ht with ⟨ha,hk⟩ | ⟨ha,hk⟩
      · have hy : k%2=1 := by omega
        have hs : (a+k)%4=2 := by omega
        have hstart := BB6Agent38.blank_section_mod4 t a k hp hy hs
        have hfirst := (Prod.mk.inj hstart).1
        omega
      · have hparent :
          BB6.Agent8Section.run secNext t (some (5,1)) =
            some (704*q+41,3744*q+228) := by
          simpa [ha,hk] using hp
        obtain ⟨tp,hprev⟩ :=
          (BB6.Agent15.blank_reach_iff_affine (704*q+41) (3744*q+228)
            (by omega) (by omega) (by omega)).mp ⟨t,hparent⟩
        have hnorm :
            ((704*q+41)+(3744*q+228)-2,((3744*q+228)-2)/2) =
              (4448*q+267,1872*q+113) := by
          apply Prod.ext <;> omega
        rw [hnorm] at hprev
        have hcontra := BB6Agent38.blank_section_no_odd_special tp
          (4448*q+267) (1872*q+113)
          (by omega) (by omega) (by omega) (by omega)
        exact hcontra hprev

#print axioms blank_no_c16_target
end BB6.Agent46
