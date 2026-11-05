import EvenSectorLift
import EvenSeed

namespace BB6.Agent8Lift
open BB6.Agent1

/-- Every genuinely reachable even-left hub with right counter >=4
    has an exact synthetic two-action-per-stage history from a
    genuinely reached reset, with uniquely reconstructed seed height. -/
theorem reached_even_hub_has_canonical_early_reset
    (b d : Nat) (hr : Reach b d)
    (hb : b%2=0) (hd : 4≤d) (heven : d%2=0) :
    ∃ j c s : Nat, c%2=0 ∧ b=E j ∧ d=c+4 ∧
      Reach 2 s ∧ s=seed j c ∧ Run (2*j) 2 s b d := by
  obtain ⟨j,s,hs,hpow,hsum⟩ :=
    even_hub_reset_seed b d hr hb (by omega) heven
  let c:=d-4
  have hd' : d=c+4 := by dsimp [c]; omega
  have hc : c%2=0 := by omega
  have hb' : b=E j := by
    have he:=E_closed j
    omega
  have hs' : s=seed j c := by
    have hsc:=seed_closed j c
    omega
  refine ⟨j,c,s,hc,hb',hd',hs,hs',?_⟩
  simpa only [hs', hb', hd'] using synthetic_even_hub j c hc

#print axioms reached_even_hub_has_canonical_early_reset
end BB6.Agent8Lift
