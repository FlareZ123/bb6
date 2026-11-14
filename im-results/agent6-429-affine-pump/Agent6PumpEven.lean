import Agent6Pump
import BB429Rank
import BB429Burst
import Lean.Elab.Tactic.Omega

namespace Agent6PumpEven
set_option maxHeartbeats 10000000

/-- An all-first-branch prefix from first counter 11, followed by one
    even-counter/even-gap reset, returns to first counter 11.  The rank
    identity makes the output affine in the prefix length. -/
theorem even_gap_reset (L w u b : Nat)
    (hfirst : BB429Burst.firstRun L (11,w) = some (u,b))
    (hb : b % 2 = 0)
    (hd : 2 ≤ u - b/2)
    (hdeven : (u-b/2) % 2 = 0) :
    BB429.run (L+1) (11,w) = some (11,w+3*L+20) := by
  have hsource : BB429.run L (11,w) = some (u,b) :=
    BB429DyadicStarts.first_prefix_is_source _ _ _ hfirst
  have hrank : 2*u+b = 22+w+3*L := by
    have h := (BB429Burst.prefix_formula 11 w L u b hfirst).2
    omega
  have hfirstFalse : ¬ b ≥ 2*u+3 := by omega
  have hR2 : b ≠ 2*u+2 := by omega
  have hR1 : b ≠ 2*u+1 := by omega
  have hR0 : b ≠ 2*u := by omega
  have hd1 : u-b/2 ≠ 1 := by omega
  have hnext : BB429.next (u,b) = some (11,2*u+b-2) := by
    simp [BB429.next,hfirstFalse,hR2,hR1,hR0,hb,hd1,hdeven]
  have hval : 2*u+b-2 = w+3*L+20 := by omega
  rw [BB429.run_add, hsource]
  simp [BB429.run,hnext,hval]

/-- Four first-branch steps from (11,w), for every w>=408, land at
    (221,w-408). -/
private theorem first_four (w : Nat) (hw : 408 ≤ w) :
    BB429Burst.firstRun 4 (11,w) = some (221,w-408) := by
  have hguard : 4*((11+3)*2^3) ≤ 2*11+w+3*3+9 := by omega
  obtain ⟨a,b,hfirst⟩ :=
    (BB429Burst.prefix_exists_iff 11 w 3).mpr hguard
  obtain ⟨ha,hb⟩ := BB429Burst.prefix_formula 11 w 4 a b hfirst
  have hpow : (11+3)*2^4 = 224 := by decide
  have ha' : a = 221 := by omega
  have hb' : b = w-408 := by omega
  simpa [ha',hb'] using hfirst

/-- For 408<=w<=846 and w=2 (mod 4), the exact accelerated map makes
    four first-branch steps and one even/even reset:
      (11,w) -> (11,w+32).
    This is a universal family, not just the three root-orbit instances. -/
theorem five_step_cycle (w : Nat)
    (hlo : 408 ≤ w) (hhi : w ≤ 846) (hmod : w % 4 = 2) :
    BB429.run 5 (11,w) = some (11,w+32) := by
  have hfirst := first_four w hlo
  have hform : w = 4*(w/4)+2 := by omega
  have hqlo : 102 ≤ w/4 := by omega
  have hqhi : w/4 ≤ 211 := by omega
  have hbform : w-408 = 4*(w/4-102)+2 := by omega
  have hdform : 221-(w-408)/2 = 220-2*(w/4-102) := by omega
  have hb : (w-408) % 2 = 0 := by omega
  have hd : 2 ≤ 221-(w-408)/2 := by omega
  have hdeven : (221-(w-408)/2) % 2 = 0 := by omega
  have h := even_gap_reset 4 w 221 (w-408) hfirst hb hd hdeven
  simpa using h

/-- The three consecutive five-step cycles used by the observed J(0,744)
    continuation: 774 -> 806 -> 838 -> 870. -/
theorem three_cycles :
    BB429.run 15 (11,774) = some (11,870) := by
  have h0 := five_step_cycle 774 (by decide) (by decide) (by decide)
  have h1 := five_step_cycle 806 (by decide) (by decide) (by decide)
  have h2 := five_step_cycle 838 (by decide) (by decide) (by decide)
  have h12 : BB429.run 10 (11,806) = some (11,870) := by
    rw [show 10 = 5+5 by decide, BB429.run_add, h1]
    simpa using h2
  rw [show 15 = 5+10 by decide, BB429.run_add, h0]
  simpa using h12

/-- The terminal seven accelerated transitions after the three +32 cycles:
    five first branches reach (445,17), then the odd/odd and even/odd
    branches reach (440,34) and (0,924). -/
theorem tail_from_870 :
    BB429.run 7 (11,870) = some (0,924) := by
  have hfirst : BB429Burst.firstRun 5 (11,870) = some (445,17) := by decide
  have hsource : BB429.run 5 (11,870) = some (445,17) :=
    BB429DyadicStarts.first_prefix_is_source _ _ _ hfirst
  have h1 : BB429.next (445,17) = some (440,34) := by decide
  have h2 : BB429.next (440,34) = some (0,924) := by decide
  rw [show 7 = 5+2 by decide, BB429.run_add, hsource]
  simp [BB429.run,h1,h2]

/-- Exact 22-step trajectory in the source's accelerated two-counter map
    from (11,774) to (0,924), matching the terminal segment of the
    J(0,744)->J(0,924) orbit decomposition. -/
theorem route_11_774_to_0_924 :
    BB429.run 22 (11,774) = some (0,924) := by
  rw [show 22 = 15+7 by decide, BB429.run_add, three_cycles]
  exact tail_from_870

#print axioms even_gap_reset
#print axioms five_step_cycle
#print axioms three_cycles
#print axioms tail_from_870
#print axioms route_11_774_to_0_924

end Agent6PumpEven
