import MixedFourNormalize
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- Exact two-step forced inverse barrier in an even-right section
    rectangle not entirely eliminated by the existing M512 quotient.
    The first inverse is the source-exact Agent24 six-sector rule;
    the second is Agent3's original-source odd-low-valuation rule. -/
theorem blank_no_rectangle_27_zero (x y : Nat)
    (hx : x%32=27) (hy : y%32=0) (hsize : 64≤y) :
    ¬ CReach x y := by
  have hg : 6≤y ∧ y%2=0 ∧ (x+y)%8≠0 ∧ (x+y)%8≠7 := by omega
  intro hr
  have h1 : CReach (x+y-2) ((y-2)/2) :=
    (BB6.Agent46.six_even_right_blank_reach_iff x y
      hg.1 hg.2.1 hg.2.2.1 hg.2.2.2).mp hr
  let a := x+y-2
  let k := (y-2)/2
  have hgate : a%2=1 ∧ k%2=1 ∧ 5≤k ∧
      (a+k)%4=0 ∧ (a+k)%16≠0 ∧ 24≤a+k := by
    dsimp [a,k]
    omega
  have h2 : CReach ((a+k-4)/2) ((a+3*k-10)/4) :=
    (oddodd_lowval_blank_reach_iff a k hgate.1
      hgate.2.1 hgate.2.2.1 hgate.2.2.2.1
      hgate.2.2.2.2.1 hgate.2.2.2.2.2).mp h1
  have hbad : 5≤(a+3*k-10)/4 ∧
      ((a+3*k-10)/4)%2=1 ∧
      (((a+k-4)/2)+((a+3*k-10)/4))%4=1 := by
    dsimp [a,k]
    omega
  rcases h2 with ⟨time,hn⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hn
      omega
  | succ t =>
      have hi := blank_section_odd_image t
        ((a+k-4)/2) ((a+3*k-10)/4)
        hn hbad.1 hbad.2.1
      omega

#print axioms blank_no_rectangle_27_zero
end BB6.Agent3
