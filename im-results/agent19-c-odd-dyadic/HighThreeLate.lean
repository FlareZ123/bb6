import HighThreeLateArithmetic
import DyadicThreeCone
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11HighThreeLate

/-- A source-exact all-time blank nonreachability criterion for high
    stopping targets at arbitrary inverse depth, including depths
    GREATER than the stopping exponent. -/
theorem late_high_no_blank (r j m k : Nat)
    (hr : 2≤r) (hm : 3≤m)
    (hm4 : m%4=(2*r+1)%4)
    (hstop : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hmod : (k+2)%2^(r+2)=3*2^r)
    (hsize : 7*2^r≤k+2) :
    ¬ BB6.Agent3.CReach (2*j+3) k := by
  obtain ⟨u,hu,hu4,hb,hmass⟩ :=
    late_high_arithmetic r j m k hr hm hm4 hstop hmod hsize
  exact BB6.Agent19ThreeCone.dyadic_three_cone_no_blank
    r (2*j+3) k u hu hu4 hb hmass

/-- An explicit infinite class beyond all older small-depth
    dyadic congruence gates: m=3, depth seven, j=372 modulo 512. -/
theorem late_high_372_family_no_blank (t : Nat) :
    ¬ BB6.Agent3.CReach (747+1024*t) (95614+130560*t) := by
  let j := 372+512*t
  let k := 95614+130560*t
  have hstop : k+j+3*3+5=2^(2*3+2)*(j+3) := by
    dsimp [k,j]
    omega
  have hmod : (k+2)%2^(7+2)=3*2^7 := by
    dsimp [k]
    omega
  have hsize : 7*2^7≤k+2 := by
    dsimp [k]
    omega
  have h := late_high_no_blank 7 j 3 k
    (by decide) (by decide) (by decide) hstop hmod hsize
  have hx : 2*j+3=747+1024*t := by dsimp [j]; omega
  rw [hx] at h
  exact h

#print axioms late_high_no_blank
#print axioms late_high_372_family_no_blank
end BB6.Agent11HighThreeLate
