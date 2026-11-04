import UniformS25Inverse
import UniformOrbitIff
import ReachAffine
import Agent38SectionParity
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192

namespace BB6.Agent46

/-- Two source-authenticated backward section links force the affine
    mod-four-forbidden ancestor from every genuine blank Q(q) visit. -/
theorem s25_two_step_forces_bad (q : Nat) :
    BB6.Agent3.CReach (35584*q+6939) (14976*q+2921) →
      BB6.Agent3.CReach (44120*q+8593) (10708*q+2085) := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
    simp [BB6.Agent8Section.run] at hr
    omega
  | succ t =>
    cases hp : BB6.Agent8Section.run secNext t (some (5,1)) with
    | none =>
      simp [BB6.Agent8Section.run,hp] at hr
    | some p =>
      rcases p with ⟨a,k⟩
      have hed : secNext (a,k)=some (35584*q+6939,14976*q+2921) := by
        simpa [BB6.Agent8Section.run,hp] using hr
      obtain ⟨ha,hk⟩ := s25_first_inverse q a k hed
      have hparent :
          BB6.Agent8Section.run secNext t (some (5,1)) =
            some (25280*q+4928,20128*q+3923) := by
        simpa only [ha,hk] using hp
      cases t with
      | zero =>
        simp [BB6.Agent8Section.run] at hparent
        omega
      | succ u =>
        cases hp2 : BB6.Agent8Section.run secNext u (some (5,1)) with
        | none =>
          simp [BB6.Agent8Section.run,hp2] at hparent
        | some p =>
          rcases p with ⟨b,c⟩
          have hed2 : secNext (b,c)=
              some (25280*q+4928,20128*q+3923) := by
            simpa [BB6.Agent8Section.run,hp2] using hparent
          obtain ⟨hb,hc⟩ := s25_second_inverse q b c hed2
          have hparent2 :
              BB6.Agent8Section.run secNext u (some (5,1)) =
                some (22704*q+4423,21416*q+4172) := by
            simpa only [hb,hc] using hp2
          obtain ⟨v,hv⟩ :=
            (BB6.Agent15.blank_reach_iff_affine
              (22704*q+4423) (21416*q+4172)
              (by omega) (by omega) (by omega)).mp ⟨u,hparent2⟩
          have heq :
              ((22704*q+4423)+(21416*q+4172)-2,
                ((21416*q+4172)-2)/2) =
                (44120*q+8593,10708*q+2085) := by
            apply Prod.ext <;> omega
          rw [heq] at hv
          exact ⟨v,hv⟩

/-- A new all-time exclusion of the surviving s=25 modulo 128
    Machine C affine low feeder class, under authentic blank reachability. -/
theorem blank_no_s25_affine (q : Nat) :
    ¬ BB6.Agent3.CReach (35584*q+6939) (14976*q+2921) := by
  intro h
  obtain ⟨t,ht⟩ := s25_two_step_forces_bad q h
  have hforbidden := BB6Agent38.blank_section_mod4 t
      (44120*q+8593) (10708*q+2085) ht (by omega) (by omega)
  have hfirst := (Prod.mk.inj hforbidden).1
  omega

/-- Exact source-connected blank exclusion for a full congruence class
    of the original Machine C a=1 two-step gateway. -/
theorem blank_no_s25_one_gate (q : Nat) :
    ¬ BB6.Agent3.CReach 1 (32768*q+6404) := by
  intro hr
  have hs : 1≤128*q+25 := by omega
  have hodd : (128*q+25)%2=1 := by omega
  have harg : 256*(128*q+25)+4=32768*q+6404 := by omega
  have hparent :=
    (uniform_one_gate_reach_iff_affine (128*q+25) hs hodd).mp
      (by simpa only [harg] using hr)
  have hfirst : 278*(128*q+25)-11=35584*q+6939 := by omega
  have hsecond : 117*(128*q+25)-4=14976*q+2921 := by omega
  rw [hfirst,hsecond] at hparent
  exact blank_no_s25_affine q hparent

#print axioms s25_two_step_forces_bad
#print axioms blank_no_s25_affine
#print axioms blank_no_s25_one_gate

end BB6.Agent46
