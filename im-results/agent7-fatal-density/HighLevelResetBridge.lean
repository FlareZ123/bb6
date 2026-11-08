import OriginalNextBridge
import ResetChain

/-!
# Exact bridge between the original Cryptids high-level map and ResetParent

The upstream machine-specific highLevelNext is the same deterministic C-step
map as the repository's source model. This file makes the first-return
semantics explicit: the first visit to the section .C u 0, with every
intermediate state live and having nonzero second coordinate, is equivalent
to the existing all-valuation ResetParent grammar.

The root-orbit theorem then identifies the reset-height subsequence of the
true upstream high-level run with ResetChain 2. This is an exact
reformulation of the #746 source dynamics, not a halt/nonhalt decision.
-/

namespace Agent7HighLevelResetBridge

open CascadeSource CascadeResetInverse CascadeSweep
open BusyBeaver.M_1RB0LF_1LC1RA_0RE0RD_HHH1LE_1LF1RC_1LC1LA
open Agent10Original746

/-- The actual upstream high-level transition lifts every source C-step. -/
private theorem highLevel_step_of_Cstep (a b u v : Nat)
    (h : Cstep a b = some (u,v)) :
    highLevelNext (.C a b) = some (.C u v) := by
  have hh := Agent10Original746.exact_high_level_step a b
  rw [h] at hh
  cases hn : highLevelNext (.C a b) with
  | none => simp [hn] at hh
  | some s =>
    cases s with
    | C x y =>
      simp [hn] at hh
      rcases hh with ⟨rfl,rfl⟩
      rfl

/-- Conversely, every actual upstream high-level edge is a source C-step. -/
private theorem Cstep_of_highLevel_step (a b u v : Nat)
    (h : highLevelNext (.C a b) = some (.C u v)) :
    Cstep a b = some (u,v) := by
  have hh := Agent10Original746.exact_high_level_step a b
  rw [h] at hh
  exact hh.symm

/-- Iterate the authentic high-level map from an arbitrary C-state. -/
def runFromPair (x : Nat × Nat) : Nat → Option HighLevelState
  | 0 => some (.C x.1 x.2)
  | n+1 => (runFromPair x n).bind highLevelNext

/-- After one source C-step, the remaining high-level run is the run from its
successor. -/
theorem runFromPair_step (x y : Nat × Nat)
    (h : Cstep x.1 x.2 = some y) (n : Nat) :
    runFromPair x (n+1) = runFromPair y n := by
  induction n with
  | zero =>
    simp [runFromPair, highLevel_step_of_Cstep x.1 x.2 y.1 y.2 h]
  | succ n ih =>
    change (runFromPair x (n+1)).bind highLevelNext =
      (runFromPair y n).bind highLevelNext
    rw [ih]

/-- A genuine first return to the reset section: at a positive time the
second coordinate is zero, while every strict intermediate state exists and
has nonzero second coordinate. -/
def HighLevelFirstReset (x : Nat × Nat) (u : Nat) : Prop :=
  ∃ k, 0 < k ∧ runFromPair x k = some (.C u 0) ∧
    ∀ i, 0 < i → i < k →
      ∃ a b, runFromPair x i = some (.C a b) ∧ b ≠ 0

/-- A source first-reset outcome gives exactly the same first return in the
upstream high-level map. -/
theorem outcome_to_highLevelFirstReset_aux {x : Nat × Nat} {out : Option Nat}
    (ho : Outcome x out) :
    ∀ u, out = some u → HighLevelFirstReset x u := by
  induction ho with
  | @halt x' hstep =>
      intro u hout
      cases hout
  | @reset x' u' hstep =>
      intro u hout
      have hu : u' = u := Option.some.inj hout
      subst u
      refine ⟨1, by omega, ?_, ?_⟩
      · simp [runFromPair, highLevel_step_of_Cstep x'.1 x'.2 u' 0 hstep]
      · intro i hi1 hi2
        omega
  | @follow x y out hstep hy hrest ih =>
      intro u hout
      rcases ih u hout with ⟨k,hk,hfinal,hmid⟩
      refine ⟨k+1, by omega, ?_, ?_⟩
      · rw [runFromPair_step x y hstep k]
        exact hfinal
      · intro i hi1 hi2
        by_cases hfirst : i=1
        · subst i
          refine ⟨y.1,y.2,?_,hy⟩
          simp [runFromPair, highLevel_step_of_Cstep x.1 x.2 y.1 y.2 hstep]
        · have htwo : 1 < i := by omega
          let j := i-1
          have hj : 0 < j := by dsimp [j]; omega
          have hjk : j < k := by dsimp [j]; omega
          obtain ⟨a,b,hstate,hb⟩ := hmid j hj hjk
          refine ⟨a,b,?_,hb⟩
          have hrun := runFromPair_step x y hstep j
          have hidx : j+1=i := by dsimp [j]; omega
          rw [← hidx, hrun]
          exact hstate

/-- Thus every first reset in the high-level map is a source first-reset
outcome. Strong recursion is on the finite return time. -/
theorem highLevelFirstReset_to_outcome_aux (k : Nat) :
    ∀ (x : Nat × Nat) (u : Nat), 0 < k →
      runFromPair x k = some (.C u 0) →
      (∀ i, 0 < i → i < k →
        ∃ a b, runFromPair x i = some (.C a b) ∧ b ≠ 0) →
      Outcome x (some u) := by
  induction k using Nat.strongRecOn with
  | ind k ih =>
      intro x u hk hfinal hmid
      by_cases hbase : k=1
      · subst k
        have hstep : highLevelNext (.C x.1 x.2) = some (.C u 0) := by
          simpa [runFromPair] using hfinal
        exact Outcome.reset (Cstep_of_highLevel_step x.1 x.2 u 0 hstep)
      · have hk2 : 2 ≤ k := by omega
        obtain ⟨a,b,hstate,hb⟩ := hmid 1 (by omega) (by omega)
        have hstep : highLevelNext (.C x.1 x.2) = some (.C a b) := by
          simpa [runFromPair] using hstate
        have hc : Cstep x.1 x.2 = some (a,b) :=
          Cstep_of_highLevel_step x.1 x.2 a b hstep
        let y : Nat × Nat := (a,b)
        have htail_final : runFromPair y (k-1) = some (.C u 0) := by
          have hrun := runFromPair_step x y hc (k-1)
          have hidx : (k-1)+1=k := by omega
          have hfinal' : runFromPair x ((k-1)+1) = some (.C u 0) := by
            simpa [hidx] using hfinal
          rw [hrun] at hfinal'
          exact hfinal'
        have htail_mid : ∀ j, 0 < j → j < k-1 →
            ∃ a' b', runFromPair y j = some (.C a' b') ∧ b' ≠ 0 := by
          intro j hj1 hj2
          have hidx : j+1<k := by omega
          obtain ⟨a',b',hstate',hb'⟩ := hmid (j+1) (by omega) hidx
          refine ⟨a',b',?_,hb'⟩
          have hrun := runFromPair_step x y hc j
          calc
            runFromPair y j = runFromPair x (j+1) := hrun.symm
            _ = some (.C a' b') := hstate'
        exact Outcome.follow hc hb
          (ih (k-1) (by omega) y u (by omega) htail_final htail_mid)

/-- Exact equivalence between the external high-level first return and the
repository's source-C first-reset semantics. -/
theorem outcome_iff_highLevelFirstReset (x : Nat × Nat) (u : Nat) :
    Outcome x (some u) ↔ HighLevelFirstReset x u :=
  ⟨fun h => outcome_to_highLevelFirstReset_aux h u rfl,
   fun h => by
     rcases h with ⟨k,hk,hfinal,hmid⟩
     exact highLevelFirstReset_to_outcome_aux k x u hk hfinal hmid⟩

/-- The actual Cryptids high-level first return to .C u 0 is equivalent,
with no omitted valuation branch, to the two-arm ResetParent grammar. -/
theorem reset_parent_iff_highLevelFirstReset (h u : Nat) :
    HighLevelFirstReset (h,0) u ↔ ResetParent h u := by
  exact (outcome_iff_highLevelFirstReset (h,0) u).symm.trans
    (reset_parent_iff h u)

/-- One actual high-level edge follows every source C-step edge. -/
private theorem run_succ_of_Cstep (k a b u v : Nat)
    (hrun : Agent10Original746.run k = some (.C a b))
    (hstep : Cstep a b = some (u,v)) :
    Agent10Original746.run (k+1) = some (.C u v) := by
  change (Agent10Original746.run k).bind highLevelNext = _
  rw [hrun, highLevel_step_of_Cstep a b u v hstep]

/-- Every source-C path from the genuine post-initial root appears in the
actual upstream high-level orbit. -/
theorem run_of_reach {x : Nat × Nat}
    (hr : ReachC (2,0) x) :
    ∃ k, Agent10Original746.run k = some (.C x.1 x.2) := by
  induction hr with
  | refl =>
      exact ⟨0,rfl⟩
  | @push start y z hreach hstep ih =>
      rcases ih with ⟨k,hk⟩
      rcases z with ⟨u,v⟩
      exact ⟨k+1, run_succ_of_Cstep k y.1 y.2 u v hk hstep⟩

/-- Reset states on the true upstream orbit are exactly the source
ResetChain states. -/
theorem original_highLevel_reset_chain_iff (u : Nat) :
    (∃ k, Agent10Original746.run k = some (.C u 0)) ↔ ResetChain 2 u := by
  constructor
  · rintro ⟨k,hk⟩
    exact (root_reset_chain_iff u).mp
      (Agent10Original746.run_reaches k u 0 hk)
  · intro hc
    obtain ⟨k,hk⟩ := run_of_reach (reset_chain_to_cpath hc)
    exact ⟨k,hk⟩

/-- The same reset-chain characterization, counted from the true original
high-level start C(0,3), whose first step reaches C(2,0). -/
theorem original_start_reset_chain_iff (u : Nat) :
    (∃ k, Agent10Original746.startRun (k+1) = some (.C u 0)) ↔
      ResetChain 2 u := by
  constructor
  · rintro ⟨k,hk⟩
    rw [Agent10Original746.startRun_successor] at hk
    exact (original_highLevel_reset_chain_iff u).mp ⟨k,hk⟩
  · intro hc
    obtain ⟨k,hk⟩ := (original_highLevel_reset_chain_iff u).mpr hc
    exact ⟨k, by rw [Agent10Original746.startRun_successor]; exact hk⟩

#print axioms outcome_iff_highLevelFirstReset
#print axioms reset_parent_iff_highLevelFirstReset
#print axioms original_highLevel_reset_chain_iff
#print axioms original_start_reset_chain_iff

end Agent7HighLevelResetBridge
