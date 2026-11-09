import SweepShortEvenEntry

namespace CascadeFastReturn
open CascadeBitSweep

/-- After every sufficiently high successful even level entry, the
    executable source-exact level macro, when successful, finishes by an odd
    original first-reset edge. Thus the one-event-per-level machine has an
    alternating event-type constraint independent of its initial root. -/
theorem even_entry_macro_finishes_odd (j a x v : Nat)
    (hj : 7≤j)
    (ha : firstFailIndex a=j)
    (he : bitOutcome a=some x)
    (haeven : (a+j)%2=0)
    (hx : firstFailIndex x=j+1)
    (hnot : ¬fatalAt x)
    (hm : (levelMacro x).2=some v) :
    ∃m u, (levelMacro x).1=m+1 ∧
      runBit x m=some u ∧ firstFailIndex u=j+1 ∧
      (u+(j+1))%2=1 ∧ bitOutcome u=some v := by
  let k := j+1
  let D := deficitAt k x
  let md := terminalPair k D
  have hspec := terminalPair_spec k D (by
    simpa [k] using level_deficit_min x)
  change D=2^md.1*md.2 ∧ 2*k+6≤md.2 ∧
    (md.2%2=1 ∨ md.2<4*k+12) at hspec
  obtain ⟨hfactor,hdmin,_⟩ := hspec
  have hpar := (even_entry_terminal_residual_odd j a x hj ha he haeven hx).2
  change md.2%2=1 at hpar
  obtain ⟨u,hrun,hu,hdu,_⟩ :=
    runBit_full_level_block k x md.1 md.2 (by exact hx) hnot hdmin hfactor
  have huheight : u=atHeight k 0 md.2 := by
    have hbound := (firstFailIndex_spec u).2
    rw [hu] at hbound
    dsimp [deficitAt] at hdu
    dsimp [atHeight]
    omega
  have huodd : (u+k)%2=1 := by
    have hh := deficit_parity k u hu
    rw [hdu,hpar] at hh
    omega
  have hmroot : bitOutcome (atHeight k 0 md.2)=some v := by
    have hn : x+firstFailIndex x+4 ≠4*2^(firstFailIndex x) := hnot
    simpa only [levelMacro,if_neg hn] using hm
  refine ⟨md.1,u,?_,hrun,by simpa [k] using hu,by simpa [k] using huodd,?_⟩
  · have hn : x+firstFailIndex x+4 ≠4*2^(firstFailIndex x) := hnot
    simp only [levelMacro,if_neg hn]
  · rw [huheight]
    exact hmroot

#print axioms even_entry_macro_finishes_odd
end CascadeFastReturn
