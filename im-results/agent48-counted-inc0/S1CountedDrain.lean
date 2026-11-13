import S1CountedInc0
import CountedReset
import Lean.Elab.Tactic.Omega

/-!
# S1 all-ones counted drain

This module instantiates Agent 8's generic S0 counted-drain composition
with Agent 48's parity-complete S1 decrement theorem.  The encoder defines
S1 as S0 with the left context
`markerWord m ++ d0 ++ binDec L n ++ lh`; hence the one-step theorem
discharges the uniform Inc0 premise without a new machine simulation.
-/

namespace BB6Coverage.Agent48CountedInc0

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent8CountedReset

/-- The parity-complete source decrement in the exact Inc0 cost interface
used by the generic counted-drain theorem. -/
theorem s1Config_counted_decrement_inc0
    (L n m a z c : Nat) (h : Int)
    (hz : 0 < z) (hzlt : z < 2^a) :
    run tm2 (inc0Cost z c)
      (s1Config L n m a z c h) =
      some (s1Config L n m a (z-1) (c+1) h) := by
  obtain ⟨q,r,len,hfactor,ha,hq,hrun⟩ :=
    s1Config_counted_decrement L n m a z c h hz hzlt
  have hv := v2_of_odd_factorization z q r hfactor
  simpa [inc0Cost,hv] using hrun

/-- Any bounded S1 counter can be drained completely, transferring every
unit to the right unary counter, with the exact recursively accumulated
Inc0 cost. -/
theorem s1Config_counted_drain
    (L n m a k c : Nat) (h : Int)
    (hbound : 2^k-1 < 2^a) :
    run tm2 (drainCost (2^k-1) c)
      (s1Config L n m a (2^k-1) c h) =
      some (s1Config L n m a 0 (c+(2^k-1)) h) := by
  let l : List Bool := markerWord m ++ d0 ++ binDec L n ++ lh
  have hInc0 : ∀ z c', 0 < z → z < 2^a →
      run tm2 (inc0Cost z c') (s0Config l a z c' h) =
        some (s0Config l a (z-1) (c'+1) h) := by
    intro z c' hz hzlt
    have hrun := s1Config_counted_decrement_inc0
      L n m a z c' h hz hzlt
    simpa [l,s1Config] using hrun
  have hrun := countedIncs0 l a (2^k-1) c h hbound hInc0
  simpa [l,s1Config] using hrun

/-- The all-ones S1 drain has exactly Agent 8's source carry-pattern cost. -/
theorem s1Config_counted_drain_pattern
    (L n m a k : Nat) (h : Int)
    (hbound : 2^k-1 < 2^a) :
    run tm2 (drainPattern k)
      (s1Config L n m a (2^k-1) 0 h) =
      some (s1Config L n m a 0 (2^k-1) h) := by
  have hrun := s1Config_counted_drain L n m a k 0 h hbound
  rw [drainCost_binary] at hrun
  simpa using hrun

/-- Closed-form exact runtime for the all-ones S1 drain. -/
theorem s1Config_counted_drain_closed
    (L n m a k : Nat) (h : Int)
    (hbound : 2^k-1 < 2^a) :
    run tm2 (6*4^k + 42*2^k - 12*k - 48)
      (s1Config L n m a (2^k-1) 0 h) =
      some (s1Config L n m a 0 (2^k-1) h) := by
  have hrun := s1Config_counted_drain L n m a k 0 h hbound
  rw [drainCost_binary_closed] at hrun
  simpa using hrun

#print axioms s1Config_counted_decrement_inc0
#print axioms s1Config_counted_drain_pattern
#print axioms s1Config_counted_drain
#print axioms s1Config_counted_drain_pattern
#print axioms s1Config_counted_drain_closed

end BB6Coverage.Agent48CountedInc0
