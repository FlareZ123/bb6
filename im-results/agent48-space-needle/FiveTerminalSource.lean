import FiveTerminal
import NeedleTerminalAffineSource
import Lean.Elab.Tactic.Omega
set_option maxRecDepth 4096
set_option maxHeartbeats 0

namespace BB6.Agent48.SpaceNeedleFive
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD
open BB6.Agent48.SpaceNeedle
open BB6.Agent20.SpaceNeedleTriple

/-- All five feeders are different even without assumptions on their quotients. -/
theorem oddTower_five_distinct (q0 q3 q20 q38 q83 : Nat) :
  let d0 := oddTower q0 0
  let d3 := oddTower q3 3
  let d20 := oddTower q20 20
  let d38 := oddTower q38 38
  let d83 := oddTower q83 83
  d0≠d3 ∧ d0≠d20 ∧ d0≠d38 ∧ d0≠d83 ∧
  d3≠d20 ∧ d3≠d38 ∧ d3≠d83 ∧
  d20≠d38 ∧ d20≠d83 ∧ d38≠d83 := by
  have e0 : oddTower q0 0 = 2*q0+1 := by
    have h := oddTower_factor q0 0
    have hp : (2:Nat)^0=1 := by decide
    rw [hp] at h
    omega
  have e3 : oddTower q3 3 = 16*q3+22 := by
    have h := oddTower_factor q3 3
    have hp : (2:Nat)^3=8 := by decide
    rw [hp] at h
    omega
  have e20 : oddTower q20 20 = 2097152*q20+3145726 := by
    have h := oddTower_factor q20 20
    have hp : (2:Nat)^20=1048576 := by decide
    rw [hp] at h
    omega
  have e38 : oddTower q38 38 = 549755813888*q38+824633720830 := by
    have h := oddTower_factor q38 38
    have hp : (2:Nat)^38=274877906944 := by decide
    rw [hp] at h
    omega
  have e83 : oddTower q83 83 = 19342813113834066795298816*q83+29014219670751100192948222 := by
    have h := oddTower_factor q83 83
    have hp : (2:Nat)^83=9671406556917033397649408 := by decide
    rw [hp] at h
    omega
  have h := five_distinct q0 q3 q20 q38 q83
  dsimp at h ⊢
  simpa only [e0,e3,e20,e38,e83] using h

/-- Infinite family of targets with five source-valid distinct terminal predecessors.
The existential witnesses are synthetic; no blank-root reachability is asserted. -/
theorem original_five_terminal_predecessors (t : Nat) :
  ∃ d0 d3 d20 d38 d83 : Nat,
    d0≠d3 ∧ d0≠d20 ∧ d0≠d38 ∧ d0≠d83 ∧
    d3≠d20 ∧ d3≠d38 ∧ d3≠d83 ∧
    d20≠d38 ∧ d20≠d83 ∧ d38≠d83 ∧
    highLevelNext (.N d0) = some (.N (2^(exponent t)-2)) ∧
    highLevelNext (.N d3) = some (.N (2^(exponent t)-2)) ∧
    highLevelNext (.N d20) = some (.N (2^(exponent t)-2)) ∧
    highLevelNext (.N d38) = some (.N (2^(exponent t)-2)) ∧
    highLevelNext (.N d83) = some (.N (2^(exponent t)-2)) := by
  obtain ⟨q0,q3,q20,q38,q83,hq0,hq3,hq20,hq38,hq83⟩ := five_equations t
  have hK : 1 ≤ exponent t := by
    unfold exponent
    exact Nat.le_trans (by decide : 1 ≤ 115559872543250362436240044170777864346536) (Nat.le_add_right _ _)
  have he0 : NeedleInverse.den 0*q0+NeedleInverse.bias 0=(2:Nat)^(exponent t) := by
    change 5*q0+6=(2:Nat)^(exponent t)
    exact hq0
  have he3 : NeedleInverse.den 3*q3+NeedleInverse.bias 3=(2:Nat)^(exponent t) := by
    change 19*q3+30=(2:Nat)^(exponent t)
    exact hq3
  have he20 : NeedleInverse.den 20*q20+NeedleInverse.bias 20=(2:Nat)^(exponent t) := by
    change 2097155*q20+3145751=(2:Nat)^(exponent t)
    exact hq20
  have he38 : NeedleInverse.den 38*q38+NeedleInverse.bias 38=(2:Nat)^(exponent t) := by
    change 549755813891*q38+824633720873=(2:Nat)^(exponent t)
    exact hq38
  have he83 : NeedleInverse.den 83*q83+NeedleInverse.bias 83=(2:Nat)^(exponent t) := by
    change 19342813113834066795298819*q83+29014219670751100192948310=(2:Nat)^(exponent t)
    exact hq83
  obtain ⟨h03,h020,h038,h083,h320,h338,h383,h2038,h2083,h3883⟩ :=
    oddTower_five_distinct q0 q3 q20 q38 q83
  exact ⟨oddTower q0 0,oddTower q3 3,oddTower q20 20,oddTower q38 38,oddTower q83 83,
    h03,h020,h038,h083,h320,h338,h383,h2038,h2083,h3883,
    authentic_affine_successor q0 0 (exponent t) hK he0,
    authentic_affine_successor q3 3 (exponent t) hK he3,
    authentic_affine_successor q20 20 (exponent t) hK he20,
    authentic_affine_successor q38 38 (exponent t) hK he38,
    authentic_affine_successor q83 83 (exponent t) hK he83⟩

#print axioms oddTower_five_distinct
#print axioms original_five_terminal_predecessors
end BB6.Agent48.SpaceNeedleFive
