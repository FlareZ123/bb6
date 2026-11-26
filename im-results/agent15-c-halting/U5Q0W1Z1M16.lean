import U5Q0OddOddFan
import M32SectionEmbedding
import CSourceBridge16
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace BB6.Agent15U5Q0W17
open BB6.Agent15
open BB6.Agent46

private theorem cReach_parent_of_left_gt5 (x y : Nat) (hx : 5 < x)
    (h : CReach x y) :
    ∃ a k, CReach a k ∧ secNext (a,k)=some (x,y) := by
  rcases h with ⟨n,hn⟩
  cases n with
  | zero =>
      simp [BB6.Agent8Section.run] at hn
      omega
  | succ n =>
      cases hp : BB6.Agent8Section.run secNext n (some (5,1)) with
      | none =>
          simp [BB6.Agent8Section.run,hp] at hn
      | some p =>
          refine ⟨p.1,p.2,⟨n,hp⟩,?_⟩
          simpa [BB6.Agent8Section.run,hp] using hn

private theorem cReach_not_seen16 (a k : Nat)
    (hseen : CCert16.seen (CCert16.q a) (CCert16.q k)
      (CCert16.q 0)=false) : ¬ CReach a k := by
  intro hr
  have hline : BB6CLine.Reach (a,k,0) := m32_section_reach_embeds hr
  have hcert := CCert16.source_reachable_embeds16 hline
  have hs := CCert16.reachable_seen hcert
  rw [hseen] at hs
  cases hs

/-- The M16 quotient excludes the exact q=0 parent on the cylinder
    t=207+672*r. The parent residues are constantly (18,10,0). -/
theorem q0_w1_z1_parent_unreachable (r : Nat) :
    ¬ CReach (8898+28896*r) (8794+28560*r) := by
  have hqa : CCert16.q (8898+28896*r)=CCert16.q 18 := by
    apply CCert16.q_congr_big
    · omega
    · decide
    · omega
  have hqk : CCert16.q (8794+28560*r)=CCert16.q 10 := by
    apply CCert16.q_congr_big
    · omega
    · decide
    · omega
  have hseen : CCert16.seen (CCert16.q (8898+28896*r))
      (CCert16.q (8794+28560*r)) (CCert16.q 0)=false := by
    rw [hqa,hqk]
    decide
  exact cReach_not_seen16 _ _ hseen

/-- A new infinite original-blank exclusion cylinder for the U5
    odd/odd target. Its exact source fan has a unique q=0 parent,
    and that parent is absent from the kernel-certified M16 quotient. -/
theorem q0_w1_z1_target_unreachable (r : Nat) :
    ¬ CReach (44*(207+672*r)-1) (42*(207+672*r)-1) := by
  let t := 207+672*r
  have ht : t=207+672*r := rfl
  intro hX
  obtain ⟨a,k,hprev,hstep⟩ :=
    cReach_parent_of_left_gt5 (44*t-1) (42*t-1) (by rw [ht]; omega) hX
  have hfan := (BB6.Agent3U5Q0Fan.q0_oddodd_parent_fan_iff
    t a k (by rw [ht]; omega)).mp hstep
  rcases hfan with ⟨q,U,hpow,hUge,hUeven,ha,hkpos,hlow,hcost⟩
  have hmod : (43*t-1)%8=4 := by rw [ht]; omega
  have hq0 : q=0 := by
    by_cases hq : q=0
    · exact hq
    · have hqpos : 1≤q := by omega
      have hpowdiv : 4∣4^q := by
        obtain ⟨q',hqeq⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q≠0)
        refine ⟨4^q',?_⟩
        rw [hqeq,pow_succ]
        simp [Nat.mul_comm]
      have hUdiv : 2∣U := ⟨U/2,by omega⟩
      have h8 : 8∣4^q*U := by
        have hprod := Nat.mul_dvd_mul hpowdiv hUdiv
        simpa using hprod
      have h8' : 8∣43*t-1 := by rw [hpow]; exact h8
      have hmod0 := Nat.mod_eq_zero_of_dvd h8'
      omega
  have hU : U=43*t-1 := by simpa [hq0] using hpow.symm
  have ha' : a=43*t-3 := by rw [hU] at ha; omega
  have hk' : 2*k=85*t-7 := by rw [hU] at hcost; omega
  have haEq : a=8898+28896*r := by rw [ht] at ha'; omega
  have hkEq : k=8794+28560*r := by rw [ht] at hk'; omega
  have hparent : ¬ CReach a k := by
    rw [haEq,hkEq]
    exact q0_w1_z1_parent_unreachable r
  exact hparent hprev

#print axioms q0_w1_z1_parent_unreachable
#print axioms q0_w1_z1_target_unreachable
end BB6.Agent15U5Q0W17
