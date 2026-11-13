import Q4RightEndpoint
import S1CountedInc0
import CostRecurrence
import CountedReset
import Lean.Elab.Tactic.Omega

/-!
# Generic odd m=2 source reset stage

The existing q4 endpoint theorem is uniform in every odd bounded inner
counter.  This module composes it with the source counted drain and proves
the complete proposed increment transition for every odd n, rather than
only the root's small n=1 specialization.

This is an intermediate source theorem: it advances the arbitrary middle
section but does not by itself prove the complete BB(6) itinerary.
-/

namespace BB6Coverage.Agent42M2OddGeneric

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent24Q4Endpoint
open BB6Coverage.Agent48CountedInc0
open BB6Coverage.Agent8CountedReset
open BB6ChampionArithmetic

set_option maxHeartbeats 3000000

/-- Exact S1 drain of an all-ones binary counter, proved directly from
the parity-complete one-step S1 decrement and the generic CountedReset
composition.  This avoids depending on the separate prefix/drain adapter. -/
private theorem s1Config_drain_ones
    (L n m a k : Nat) (h : Int)
    (hbound : 2^k-1 < 2^a) :
    run tm2 (drainCost (2^k-1) 0)
      (s1Config L n m a (2^k-1) 0 h) =
      some (s1Config L n m a 0 (2^k-1) h) := by
  let l : List Bool := markerWord m ++ d0 ++ binDec L n ++ lh
  have hInc0 : ∀ z c, 0 < z → z < 2^a →
      run tm2 (inc0Cost z c) (s0Config l a z c h) =
        some (s0Config l a (z-1) (c+1) h) := by
    intro z c hz hzlt
    obtain ⟨q,r,len,hfactor,ha,hq,hrun⟩ :=
      s1Config_counted_decrement L n m a z c h hz hzlt
    have hv := v2_of_odd_factorization z q r hfactor
    simpa [inc0Cost,hv,l,s1Config] using hrun
  have hrun := countedIncs0_binary l a k h hbound hInc0
  rw [← drainCost_binary k] at hrun
  simpa [l,s1Config] using hrun

/-- Every odd bounded inner counter admits the complete m=2 reset
transition, including the exact counted drain.  The endpoint is the
canonical S1 configuration with inner counter n-1, marker 1, exponent
a+b+2, zero left carry counter, and right counter 2^b-1. -/
theorem m2Odd_counted_increment_source
    (L n a b : Nat) (h : Int)
    (hn : n % 2 = 1) (hbound : n < 2^L) :
    run tm2 (proposedIncrementCost 2 n a b)
      (s1Config L n 2 a 0 b h) =
      some (s1Config L (n-1) 1 (a+b+2) 0 (2^b-1)
        (h+5+3*b)) := by
  have hprefix := oddRst2_q4_counted_source L n a b h hn hbound
  have hexp : b < a+b+2 := by omega
  have hpow : 2^b ≤ 2^(a+b+2) :=
    Nat.pow_le_pow_right (by decide : 0 < 2) (Nat.le_of_lt hexp)
  have hpos : 0 < 2^b := Nat.pow_pos (by decide)
  have hbound' : 2^b-1 < 2^(a+b+2) := by omega
  have htail := s1Config_drain_ones L (n-1) 1 (a+b+2) b
    (h+5+3*b) hbound'
  have hv : v2 n = 0 := v2_of_odd n (by omega)
  have hpre : resetPrefixCost 2 n a b = 71+12*a+3*b := by
    simp [resetPrefixCost,hv]
    omega
  have hcost : proposedIncrementCost 2 n a b =
      (71+12*a+3*b) + drainCost (2^b-1) 0 := by
    rw [proposedIncrementCost_decomp,hpre]
  rw [hcost,run_add,hprefix]
  simp only [Option.bind_some]
  exact htail

#print axioms s1Config_drain_ones
#print axioms m2Odd_counted_increment_source

end BB6Coverage.Agent42M2OddGeneric
