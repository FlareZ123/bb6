import RestartDepthBounds

namespace BB6.Agent9RestartDepthBounds

/-
This arithmetic leaf isolates the positive-slack (delta=1, Is=20) case.
It uses the existing terminal-cost cap, the high-depth defect, the exact
energy identity, and the original inverse power/mass equations. It is a
draft pending local Lean 4.36.0-rc2 preflight and source composition.
-/

/-- The delta=1, Is=20 branch would force a negative inverse-parent
    half-counter, contradicting the source guard bp>=8. -/
theorem deltaOneIs20_parent_left_impossible
    (P M t d q D k c : Nat)
    (hP : 2^83 ≤ P)
    (hcap : 128*(M+3) < 93*P)
    (hdefect : 49*D+14*M=58*P+6)
    (ht : t=5 ∨ t=6)
    (hEnergy : 14*k=40*P+42*c+50)
    (hD : D=c+3)
    (hPower : 2^t*D=d+q+3)
    (hMass : 2*k+c+2*t+2=2*q+d)
    (hq : 4≤q) : False := by
  have hcap14 : 1792*(M+3) < 1302*P := by
    calc
      1792*(M+3) = 14*(128*(M+3)) := by omega
      _ < 14*(93*P) := Nat.mul_lt_mul_of_pos_left hcap (by decide)
      _ = 1302*P := by omega
  have hcapExpand : 1792*M+5376 < 1302*P := by
    calc
      1792*M+5376 = 1792*(M+3) := by omega
      _ < 1302*P := hcap14
  have hdefect128 : 6272*D+1792*M=7424*P+768 := by omega
  have hDlarge : 2*D>P := by omega
  have hqsum : q+2^t*D=2*k+D+2*t+2 := by omega
  have hEnergyD : 14*k+76=40*P+42*D := by omega
  have hformula :
      7*q+7*(2^t*D)+62=40*P+49*D+14*t := by omega
  rcases ht with ht5 | ht6
  · subst t
    have hEq : 7*q+175*D=40*P+8 := by omega
    have hBig : 175*D>40*P+8 := by omega
    omega
  · subst t
    have hEq : 7*q+399*D=40*P+22 := by omega
    have hBig : 399*D>40*P+22 := by omega
    omega

#print axioms deltaOneIs20_parent_left_impossible

end BB6.Agent9RestartDepthBounds
