import Agent3CImage
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3
open BB6.Agent46

/-- Reversing any odd bounce continuation is exact for c≥4. -/
theorem bounce_odd_reverse (k c x y : Nat)
    (hk : k%2=1) (hc : 4≤c)
    (h : (bounce (2*k+3) c).2=some (x,y)) :
    (bounce k (c+2*k+3)).2=some (x,y) := by
  have hl : ¬c+2*k+3<4 := by omega
  have hs : ¬c+2*k+3≤2*k+6 := by omega
  rw [bounce]
  simp only [if_neg hl, if_pos hk, if_neg hs]
  have hc0 : c+2*k+3-(2*k+3)=c := by omega
  rw [hc0]
  exact h

/-- Reversing any even bounce continuation is exact for c≥4. -/
theorem bounce_even_reverse (k c x y : Nat)
    (hk : k%2=0) (hc : 4≤c)
    (h : (bounce (2*k+4) c).2=some (x,y)) :
    (bounce k (c+2*k+5)).2=some (x,y) := by
  have hl : ¬c+2*k+5<4 := by omega
  have he : ¬k%2=1 := by omega
  have h4 : c+2*k+5≠4 := by omega
  have h5 : c+2*k+5≠5 := by omega
  have hs : ¬c+2*k+5≤2*k+8 := by omega
  rw [bounce]
  simp only [if_neg hl, if_neg he, if_neg h4, if_neg h5, if_neg hs]
  have hc0 : c+2*k+5-(2*k+5)=c := by omega
  rw [hc0]
  exact h

#print axioms bounce_odd_reverse
#print axioms bounce_even_reverse
end BB6.Agent3
