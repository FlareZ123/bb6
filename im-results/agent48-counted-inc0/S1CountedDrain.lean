import S1CountedInc0
import CountedReset
import Lean.Elab.Tactic.Omega

/-!
# S1 counted drain

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

/-- Drain any bounded S1 counter, transferring every unit to the right
unary counter, with the exact recursively accumulated Inc0 cost. -/
theorem s1Config_counted_drain_general
    (L n m a z c : Nat) (h : Int)
    (hbound : z < 2^a) :
    run tm2 (drainCost z c)
      (s1Config L n m a z c h) =
      some (s1Config L n m a 0 (c+z) h) := by
  let l : List Bool := markerWord m ++ d0 ++ binDec L n ++ lh
  have hInc0 : ∀ z' c', 0 < z' → z' < 2^a →
      run tm2 (inc0Cost z' c') (s0Config l a z' c' h) =
        some (s0Config l a (z'-1) (c'+1) h) := by
    intro z' c' hz hzlt
    have hrun := s1Config_counted_decrement_inc0
      L n m a z' c' h hz hzlt
    simpa [l,s1Config] using hrun
  have hrun := countedIncs0 l a z c h hbound hInc0
  simpa [l,s1Config] using hrun

/-- All-ones specialization of the general S1 counted drain. -/
theorem s1Config_counted_drain
    (L n m a k c : Nat) (h : Int)
    (hbound : 2^k-1 < 2^a) :
    run tm2 (drainCost (2^k-1) c)
      (s1Config L n m a (2^k-1) c h) =
      some (s1Config L n m a 0 (c+(2^k-1)) h) := by
  have hrun := s1Config_counted_drain_general
    L n m a (2^k-1) c h hbound
  simpa using hrun

/-- Compose any canonical S1 reset-prefix witness with the
parity-complete source drain, for an arbitrary bounded counter and an
arbitrary starting right-counter value. -/
theorem s1Config_reset_prefix_then_counted_drain_general
    (L n m a z c0 : Nat) (h : Int) (cfg : Config) (prefixCost : Nat)
    (hprefix : run tm2 prefixCost cfg =
      some (s1Config L n m a z c0 h))
    (hbound : z < 2^a) :
    run tm2 (prefixCost + drainCost z c0) cfg =
      some (s1Config L n m a 0 (c0+z) h) := by
  rw [run_add,hprefix]
  simp only [Option.bind_some]
  exact s1Config_counted_drain_general L n m a z c0 h hbound

/-- All-ones specialization of the general prefix+drain composition. -/
theorem s1Config_reset_prefix_then_counted_drain
    (L n m a b : Nat) (h : Int) (cfg : Config) (prefixCost : Nat)
    (hprefix : run tm2 prefixCost cfg =
      some (s1Config L n m a (2^b-1) 0 h))
    (hbound : 2^b-1 < 2^a) :
    run tm2 (prefixCost + drainCost (2^b-1) 0) cfg =
      some (s1Config L n m a 0 (2^b-1) h) := by
  simpa using s1Config_reset_prefix_then_counted_drain_general
    L n m a (2^b-1) 0 h cfg prefixCost hprefix hbound

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
#print axioms s1Config_counted_drain_general
#print axioms s1Config_reset_prefix_then_counted_drain_general
#print axioms s1Config_reset_prefix_then_counted_drain
#print axioms s1Config_counted_drain_pattern
#print axioms s1Config_counted_drain
#print axioms s1Config_counted_drain_closed

end BB6Coverage.Agent48CountedInc0
