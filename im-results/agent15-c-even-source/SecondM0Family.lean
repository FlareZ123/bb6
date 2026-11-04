import EvenEvenReach
import OddOddLowVal
import Agent3CImage
import Lean.Elab.Tactic.Omega

namespace BB6.Agent15
open BB6.Agent46

/-- Every legitimate second-family immediate-stop input in the
    arithmetic subfamily (j,m)=(32t+6,0) is excluded from the genuine
    blank-origin section orbit by a forced O then B inverse chain.
    This theorem does not classify other Machine C stopping inputs. -/
theorem blank_no_second_mzero_j6 (t time : Nat) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠
      some (64*t+15,96*t+25) := by
  intro h
  have hO := BB6.Agent3.oddodd_lowval_blank_reach_iff
    (64*t+15) (96*t+25)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  have heqO1 :
      ((64*t+15+96*t+25-4)/2)=80*t+18 := by omega
  have heqO2 :
      ((64*t+15+3*(96*t+25)-10)/4)=88*t+20 := by omega
  rw [heqO1,heqO2] at hO
  obtain ⟨n,hn⟩ := hO.mp ⟨time,h⟩
  have hB := blank_reach_iff_even_even (80*t+18) (88*t+20)
    (by omega) (by omega) (by omega) (by omega)
  have heqB1 : 80*t+18+88*t+20-2=168*t+36 := by omega
  have heqB2 : ((88*t+20-2)/2)=44*t+9 := by omega
  rw [heqB1,heqB2] at hB
  obtain ⟨s,hs⟩ := hB.mp ⟨n,hn⟩
  cases s with
  | zero =>
      simp [BB6.Agent8Section.run] at hs
      omega
  | succ s =>
      have hi := BB6.Agent3.blank_section_odd_image s
        (168*t+36) (44*t+9) hs (by omega) (by omega)
      omega

/-- Every pair excluded above satisfies the exact nonzero second-family
    stopping equation from Agent 15's complete halting classification. -/
theorem second_mzero_j6_is_stopping_equation (t : Nat) :
    (96*t+25)+(32*t+6)+3*0+5 =
      2^(2*0+2)*((32*t+6)+3) := by
  omega

#print axioms blank_no_second_mzero_j6
#print axioms second_mzero_j6_is_stopping_equation
end BB6.Agent15
