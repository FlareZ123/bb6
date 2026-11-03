import SpaceNeedleOddMacroCertified
import Lean.Elab.Tactic.Omega
set_option maxHeartbeats 0

namespace BB6.Agent48.SpaceNeedle
open BusyBeaver.M_1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD

/-- Every original high-level step strictly before an accelerated macro's
recorded exit count remains a live high-level configuration. -/
theorem oddMacroNext_prefix_safe (d j : Nat)
    (hj : j < (oddMacroNext d).2) :
    ∃ e, runHigh j (some (.N d)) = some (.N e) := by
  by_cases hd : d%2=1
  · let p := splitTwos (d+1)
    have hp := splitTwos_spec (d+1) (by omega)
    have hmacro : oddMacroNext d=(some (.N (5^p.1*p.2-1)),p.1) := by
      simp [oddMacroNext,hd,p]
    rw [hmacro] at hj
    have hj' : j<p.1 := hj
    let s := p.1-j
    have hs : 0<s := by dsimp [s]; omega
    have hsum : j+s=p.1 := by dsimp [s]; omega
    have hfactor : d=2^p.1*p.2-1 := by
      have h := hp.1
      dsimp [p] at *
      omega
    have heq : 2^p.1*p.2=2^(j+s)*p.2 := by rw [hsum]
    have hsrun := odd_block_prefix j s p.2 hp.2.2
    have hfinal : runHigh j (some (.N d)) = some (.N (5^j*2^s*p.2-1)) := by
      rw [hfactor,heq]
      exact hsrun
    exact ⟨5^j*2^s*p.2-1,hfinal⟩
  · have he : d%2=0 := by omega
    have hmacro : (oddMacroNext d).2=1 := by simp [oddMacroNext,he]
    rw [hmacro] at hj
    have hzero : j=0 := by omega
    subst j
    exact ⟨d,rfl⟩

end BB6.Agent48.SpaceNeedle
#print axioms BB6.Agent48.SpaceNeedle.oddMacroNext_prefix_safe
