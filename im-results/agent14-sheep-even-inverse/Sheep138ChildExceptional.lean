import Sheep138ChildHighH
import SheepExceptionalGap

namespace Sheep138ChildExceptional

private theorem special_equation (a h u d c n : Nat)
    (hz : 3*2^a+a+3=1+2^h*u)
    (ht : d*(1+3^h*u)+c=2^n) :
    (3*(d*3^h))*2^a + (d*3^h)*a +
      2*(d*3^h)+2^h*(d+c) = 2^(n+h) := by
  have hform : 3*2^a+a+2=2^h*u := by omega
  have hmul :
      (d*3^h)*(3*2^a+a+2)+2^h*(d+c) =
        (d*(1+3^h*u)+c)*2^h := by
    rw [hform]
    grind
  have hleft :
      (3*(d*3^h))*2^a+(d*3^h)*a+2*(d*3^h)+2^h*(d+c) =
      (d*3^h)*(3*2^a+a+2)+2^h*(d+c) := by
    grind
  calc
    (3*(d*3^h))*2^a+(d*3^h)*a+2*(d*3^h)+2^h*(d+c)
      = (d*3^h)*(3*2^a+a+2)+2^h*(d+c) := hleft
    _ = (d*(1+3^h*u)+c)*2^h := hmul
    _ = 2^n*2^h := by rw [ht]
    _ = 2^(n+h) := by rw [Nat.pow_add]

private theorem no_special_45 (N a : Nat) (hN : 141≤N) :
    45*2^a+15*a+47 ≠ 2^N := by
  exact SheepExceptionalGap.no_exp_linear N a 45 15 47 6 hN
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem no_special_135 (N a : Nat) (hN : 141≤N) :
    135*2^a+45*a+124 ≠ 2^N := by
  exact SheepExceptionalGap.no_exp_linear N a 135 45 124 8 hN
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem no_special_405 (N a : Nat) (hN : 141≤N) :
    405*2^a+135*a+338 ≠ 2^N := by
  exact SheepExceptionalGap.no_exp_linear N a 405 135 338 9 hN
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem no_special_1215 (N a : Nat) (hN : 141≤N) :
    1215*2^a+405*a+946 ≠ 2^N := by
  exact SheepExceptionalGap.no_exp_linear N a 1215 405 946 11 hN
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem no_special_243 (N a : Nat) (hN : 141≤N) :
    243*2^a+81*a+311 ≠ 2^N := by
  exact SheepExceptionalGap.no_exp_linear N a 243 81 311 8 hN
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

private theorem no_special_729 (N a : Nat) (hN : 141≤N) :
    729*2^a+243*a+784 ≠ 2^N := by
  exact SheepExceptionalGap.no_exp_linear N a 729 243 784 10 hN
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

/-- No special odd-part-three source reaches any first rational child. -/
theorem child1_no_special (k y a h u : Nat)
    (ht : 15*y+2=2^(141+4860*k))
    (hout : y=1+3^h*u)
    (hz : 3*2^a+a+3=1+2^h*u) : False := by
  have hlt := Sheep138ChildHighH.child1_h_lt_four k y h u ht hout
  have hcases : h=0 ∨ h=1 ∨ h=2 ∨ h=3 := by omega
  have htarget : 15*(1+3^h*u)+2=2^(141+4860*k) := by rw [←hout]; exact ht
  have heq := special_equation a h u 15 2 (141+4860*k) hz htarget
  rcases hcases with h0|h1|h2|h3
  · subst h
    have h : 45*2^a+15*a+47=2^(141+4860*k) := by simpa using heq
    exact no_special_45 (141+4860*k) a (by omega) h
  · subst h
    have h : 135*2^a+45*a+124=2^(142+4860*k) := by
      simpa [show 141+4860*k+1=142+4860*k by omega] using heq
    exact no_special_135 (142+4860*k) a (by omega) h
  · subst h
    have h : 405*2^a+135*a+338=2^(143+4860*k) := by
      simpa [show 141+4860*k+2=143+4860*k by omega] using heq
    exact no_special_405 (143+4860*k) a (by omega) h
  · subst h
    have h : 1215*2^a+405*a+946=2^(144+4860*k) := by
      simpa [show 141+4860*k+3=144+4860*k by omega] using heq
    exact no_special_1215 (144+4860*k) a (by omega) h

/-- No special odd-part-three source reaches any second rational child. -/
theorem child2_no_special (k y a h u : Nat)
    (ht : 81*y+68=2^(143+4860*k))
    (hout : y=1+3^h*u)
    (hz : 3*2^a+a+3=1+2^h*u) : False := by
  have hlt := Sheep138ChildHighH.child2_h_lt_two k y h u ht hout
  have hcases : h=0 ∨ h=1 := by omega
  have htarget : 81*(1+3^h*u)+68=2^(143+4860*k) := by rw [←hout]; exact ht
  have heq := special_equation a h u 81 68 (143+4860*k) hz htarget
  rcases hcases with h0|h1
  · subst h
    have h : 243*2^a+81*a+311=2^(143+4860*k) := by simpa using heq
    exact no_special_243 (143+4860*k) a (by omega) h
  · subst h
    have h : 729*2^a+243*a+784=2^(144+4860*k) := by
      simpa [show 143+4860*k+1=144+4860*k by omega] using heq
    exact no_special_729 (144+4860*k) a (by omega) h

#print axioms child1_no_special
#print axioms child2_no_special
end Sheep138ChildExceptional
