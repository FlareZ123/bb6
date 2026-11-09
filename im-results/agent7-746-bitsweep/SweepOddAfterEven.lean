import SweepAlternatingExits

namespace CascadeFastReturn
open CascadeBitSweep

/-- At source level k≥8 entered by a successful even edge from level k-1,
    the directly executable factorizer produces an ODD residual >4k+10.
    For nonfatal entries the terminal completed exit is therefore odd.
    The arithmetic statement itself holds even at an immediate fatal entry. -/
theorem even_entry_terminal_residual_odd (j a x : Nat)
    (hj : 7≤j)
    (ha : firstFailIndex a=j)
    (hax : bitOutcome a=some x)
    (haeven : (a+j)%2=0)
    (hx : firstFailIndex x=j+1) :
    let k := j+1
    let md := terminalPair k (deficitAt k x)
    4*k+10<md.2 ∧ md.2%2=1 := by
  let k := j+1
  let D := deficitAt k x
  let md := terminalPair k D
  obtain ⟨c,hclo,hchi,hband⟩ := even_level_entry_deficit_band j a x ha hax haeven hx
  have hdmin := level_deficit_min x
  rw [hx] at hdmin
  have hspec := terminalPair_spec k D hdmin
  change D=2^md.1*md.2 ∧ 2*k+6≤md.2 ∧
    (md.2%2=1 ∨ md.2<4*k+12) at hspec
  obtain ⟨hfac,hlo,hexit⟩ := hspec
  have hlarge : 4*k+10<md.2 := by
    by_cases hsmall : md.2≤4*k+10
    · have hh : 8≤k := by omega
      have hcpos : 0<c := by omega
      have hcupper : c≤2*k+4 := by omega
      have hdpos : 0<md.2 := by omega
      have hpeq : 2^(k+2)+c=2^md.1*md.2 := by
        rw [show k+2=j+3 by omega]
        rw [←hband]
        exact hfac
      exact False.elim (no_small_dyadic_factor k c md.1 md.2 hh hcpos hcupper hdpos hsmall hpeq)
    · omega
  have hodd : md.2%2=1 := by
    rcases hexit with hh | hs
    · exact hh
    · omega
  exact ⟨hlarge,hodd⟩

#print axioms even_entry_terminal_residual_odd
end CascadeFastReturn
