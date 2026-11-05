import FourSectorNormalize
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46E2
open BB6.Agent46

/-- Exact four-sector source normalizer plus the certified odd-counter
    blank-image obstruction. -/
def fourSectorExcluded (x y : Nat) : Bool :=
  let p := fourSectorNormalize x y
  decide (5≤p.2 ∧ p.2%2=1 ∧
    ((p.1+p.2)%4=1 ∨ (p.1+p.2)%4=2))

theorem fourSectorExcluded_sound (x y : Nat)
    (hex : fourSectorExcluded x y = true) :
    ∀ time, BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  intro time ht
  obtain ⟨n,hn⟩ := (blank_reach_iff_fourSectorNormalize x y).mp ⟨time,ht⟩
  have hh : 5≤(fourSectorNormalize x y).2 ∧
      (fourSectorNormalize x y).2%2=1 ∧
      (((fourSectorNormalize x y).1+(fourSectorNormalize x y).2)%4=1 ∨
       ((fourSectorNormalize x y).1+(fourSectorNormalize x y).2)%4=2) := by
    simpa [fourSectorExcluded] using (of_decide_eq_true hex)
  rcases hh with ⟨hy,ho,hbad⟩
  cases n with
  | zero =>
      have heq : fourSectorNormalize x y=(5,1) := by
        simpa [BB6.Agent8Section.run] using hn.symm
      have hp := congrArg Prod.snd heq
      omega
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (fourSectorNormalize x y).1 (fourSectorNormalize x y).2 hn hy ho
      omega

/-- A whole infinite family of authentic m=0 high stopping inputs
    is inaccessible from the genuine blank section. Unlike the older
    three-sector filter, the proof uses the new fourth exact source branch. -/
theorem high_m0_j6_mod32_unreachable (q time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (64*q+15,96*q+25) := by
  intro ht
  have hfirst : ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
      some (80*q+18,88*q+20) := by
    obtain ⟨n,hn⟩ := (BB6.Agent3.oddodd_val3_blank_reach_iff
      (64*q+15) (96*q+25)
      (by omega) (by omega) (by omega) (by omega) (by omega)).mp
      ⟨time,ht⟩
    have ha : ((64*q+15)+(96*q+25)-4)/2=80*q+18 := by omega
    have hk : ((64*q+15)+3*(96*q+25)-10)/4=88*q+20 := by omega
    exact ⟨n,by simpa only [ha,hk] using hn⟩
  obtain ⟨n1,h1⟩ := hfirst
  have hsecond : ∃ n, BB6.Agent8Section.run secNext n (some (5,1)) =
      some (168*q+36,44*q+9) := by
    obtain ⟨n,hn⟩ := (blank_reach_iff_even_two (80*q+18) (88*q+20)
      (by omega) (by omega) (by omega)).mp ⟨n1,h1⟩
    have ha : (80*q+18)+(88*q+20)-2=168*q+36 := by omega
    have hk : ((88*q+20)-2)/2=44*q+9 := by omega
    exact ⟨n,by simpa only [ha,hk] using hn⟩
  obtain ⟨n2,h2⟩ := hsecond
  cases n2 with
  | zero =>
      simp [BB6.Agent8Section.run] at h2
  | succ n =>
      have hi := BB6.Agent3.blank_section_odd_image n
        (168*q+36) (44*q+9) h2 (by omega) (by omega)
      omega

/-- The excluded source inputs are actual members of Machine C's second
    stopping-parameter family at m=0 and j=32*q+6. -/
theorem high_m0_j6_gate_equation (q : Nat) :
    (96*q+25)+(32*q+6)+3*0+5 =
      2^(2*0+2)*((32*q+6)+3) := by omega

#print axioms fourSectorExcluded_sound
#print axioms high_m0_j6_mod32_unreachable
#print axioms high_m0_j6_gate_equation
end BB6.Agent46E2
