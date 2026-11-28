import UpstreamPhysicalBridge
import Mod1536CRT
import AffineRay3787
import AffineRay7933
import Lean.Elab.Tactic.Omega

/-!
Conditional theorem about the *original* six-state F321 machine, combining
the pinned Cryptids source-acceleration bridge with independently checked
source-counter CRT and exact affine predecessor cone exclusions.

This DOES NOT assert that the original machine halts or never halts.
-/
namespace BB6.Agent31F321Physical
open BB6.Agent31F321Density
open BusyBeaver
open BusyBeaver.M_1RBHHH_1RC1LE_0RD0RF_0RE0LA_1LF0LB_1LA1LD

theorem original_blank_halt_forces_strong_terminal_filter
 (hh : BusyBeaver.IsHalt target) :
 ∃ (d n : Nat),
   CounterReach 1 1 n (d+1) d ∧
   d % 1536 ∈ BB6.Agent31F321CRT.possibleGates1536 ∧
   d % 6144 ≠ 3787 ∧
   d % 12288 ≠ 7933 := by
  obtain ⟨d,n,hr,_⟩ := original_blank_halt_implies_mod384_terminal hh
  refine ⟨d,n,hr,
    BB6.Agent31F321CRT.source_terminal_mod1536_candidates d n hr, ?_, ?_⟩
  · intro hmod
    let k := d / 6144
    have ha : d+1=6144*k+3788 := by dsimp [k]; omega
    have hd : d=6144*k+3787 := by dsimp [k]; omega
    have hreach : CounterReach 1 1 n (6144*k+3788) (6144*k+3787) := by
      simpa only [←ha,←hd] using hr
    exact (BB6.Agent31F321Ray3787.gate3787_mod6144_never k n) hreach
  · intro hmod
    let k := d / 12288
    have ha : d+1=12288*k+7934 := by dsimp [k]; omega
    have hd : d=12288*k+7933 := by dsimp [k]; omega
    have hreach : CounterReach 1 1 n (12288*k+7934) (12288*k+7933) := by
      simpa only [←ha,←hd] using hr
    exact (BB6.Agent31F321Ray7933.gate7933_mod12288_never k n) hreach

#print axioms original_blank_halt_forces_strong_terminal_filter
end BB6.Agent31F321Physical
