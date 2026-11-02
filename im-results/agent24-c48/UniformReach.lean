import UniformInverse
import Agent38SectionParity
import ReachAffine
import FeederOrbitGeneric
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Every positive odd-s blank-section hit of the exact section feeder
    has a forced affine ancestor. The other uniformly classified parent
    is excluded by the genuine blank-orbit mod-four theorem. -/
theorem uniform_feeder_forces_affine (s : Nat) (hs : 1≤s)
    (hodd : s%2=1) :
    BB6.Agent3.CReach (192*s) (160*s-1) →
      BB6.Agent3.CReach (278*s-11) (117*s-4) := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
    simp [BB6.Agent8Section.run] at hr
    omega
  | succ t =>
    cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
    | none => simp [BB6.Agent8Section.run,hp] at hr
    | some p =>
      rcases p with ⟨a,k⟩
      have ht : secNext (a,k)=some (192*s,160*s-1) := by
        simpa [BB6.Agent8Section.run,hp] using hr
      rcases uniform_section_inverse s a k hs hodd ht with
        ⟨ha,hk⟩ | ⟨ha,hk⟩
      · have hy : k%2=1 := by omega
        have hsum : (a+k)%4=2 := by omega
        have hstart := BB6Agent38.blank_section_mod4 t a k hp hy hsum
        have hfirst := (Prod.mk.inj hstart).1
        omega
      · have hparent :
          BB6.Agent8Section.run secNext t (some (5,1)) =
            some (44*s-3,234*s-6) := by
          simpa [ha,hk] using hp
        obtain ⟨tp,hprev⟩ :=
          (BB6.Agent15.blank_reach_iff_affine (44*s-3) (234*s-6)
            (by omega) (by omega) (by omega)).mp ⟨t,hparent⟩
        have heq :
            ((44*s-3)+(234*s-6)-2,((234*s-6)-2)/2) =
              (278*s-11,117*s-4) := by
          apply Prod.ext <;> omega
        rw [heq] at hprev
        exact ⟨tp,hprev⟩

/-- All low gateways with feeder t=16s and s odd can be reached only
    after the smaller explicit affine section ancestor is reached. -/
theorem uniform_one_gate_forces_affine (s : Nat) (hs : 1≤s)
    (hodd : s%2=1) :
    BB6.Agent3.CReach 1 (256*s+4) →
      BB6.Agent3.CReach (278*s-11) (117*s-4) := by
  intro h
  have ht : 1≤16*s := by omega
  have heq : 256*s+4=16*(16*s)+4 := by omega
  rw [heq] at h
  obtain ⟨time,hr⟩ := (BB6.Agent3.generic_one_gate_reach_iff (16*s) ht).mp h
  have ha : 12*(16*s)=192*s := by omega
  have hk : 10*(16*s)-1=160*s-1 := by omega
  rw [ha,hk] at hr
  exact uniform_feeder_forces_affine s hs hodd ⟨time,hr⟩

#print axioms uniform_feeder_forces_affine
#print axioms uniform_one_gate_forces_affine
end BB6.Agent46
