import M32HighSourceBridge
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace CCert

/-- Four additional infinite reset-gate residue classes excluded by the
    original-source B8/M32 reachable-set certificate. These are outside
    Agent 43's previously source-bridged M16 reset residue classes. -/
theorem reset_m32_extra_unreachable (j : Nat) (hj : 4 ≤ j)
    (hres : j%32=0 ∨ j%32=7 ∨ j%32=16 ∨ j%32=22) :
    ¬ BB6CLine.Reach (2*j+1,3*j+4,0) := by
  intro h
  have hs := reachable_seen (source_reachable_embeds32 h)
  rcases hres with h0 | h7 | h16 | h22
  · have ha : q (2*j+1) = q 65 :=
      q_congr_big _ _ (by omega) (by decide) (by omega)
    have hk : q (3*j+4) = q 100 :=
      q_congr_big _ _ (by omega) (by decide) (by omega)
    rw [ha,hk] at hs
    have hf : seen (q 65) (q 100) (q 0) = false := by decide
    rw [hf] at hs
    cases hs
  · have ha : q (2*j+1) = q 79 :=
      q_congr_big _ _ (by omega) (by decide) (by omega)
    have hk : q (3*j+4) = q 121 :=
      q_congr_big _ _ (by omega) (by decide) (by omega)
    rw [ha,hk] at hs
    have hf : seen (q 79) (q 121) (q 0) = false := by decide
    rw [hf] at hs
    cases hs
  · have ha : q (2*j+1) = q 97 :=
      q_congr_big _ _ (by omega) (by decide) (by omega)
    have hk : q (3*j+4) = q 148 :=
      q_congr_big _ _ (by omega) (by decide) (by omega)
    rw [ha,hk] at hs
    have hf : seen (q 97) (q 148) (q 0) = false := by decide
    rw [hf] at hs
    cases hs
  · have ha : q (2*j+1) = q 109 :=
      q_congr_big _ _ (by omega) (by decide) (by omega)
    have hk : q (3*j+4) = q 166 :=
      q_congr_big _ _ (by omega) (by decide) (by omega)
    rw [ha,hk] at hs
    have hf : seen (q 109) (q 166) (q 0) = false := by decide
    rw [hf] at hs
    cases hs

/-- The small reset gate j=3 is also absent from the original M32 closure. -/
theorem reset_j3_unreachable :
    ¬ BB6CLine.Reach (7,13,0) := by
  intro h
  have hs := reachable_seen (source_reachable_embeds32 h)
  have hf : seen (q 7) (q 13) (q 0) = false := by decide
  rw [hf] at hs
  cases hs

/-- The M32 quotient admits the side gate n=8. It therefore cannot
    exclude the whole n=0 (mod 8) side family. -/
theorem side_multiple_eight_m32_admitted :
    seen (q 0) (q 32) (q 215) = true := by decide

#print axioms reset_m32_extra_unreachable
#print axioms reset_j3_unreachable
#print axioms side_multiple_eight_m32_admitted

end CCert
