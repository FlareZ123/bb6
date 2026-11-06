import MixedFourNormalize
import Agent3COrbitIff
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- A genuine successful C section output with odd second coordinate at least
five cannot have coordinate sum 1 modulo 4. The initial blank section (5,1)
is excluded by its second coordinate. -/
private theorem blank_no_bad_odd_sum (x y : Nat)
    (hy : 5≤y) (ho : y%2=1) (hmod : (x+y)%4=1) : ¬ CReach x y := by
  rintro ⟨time,hr⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at hr
      omega
  | succ time =>
      have hi := blank_section_odd_image time x y hr hy ho
      omega

/-- Four forced authentic inverse section transitions show that no
blank-start section reaches (1,k) for any k>=256 congruent 124 modulo 128.
The source certificate uses the exact section, not a finite quotient. -/
theorem blank_no_one_124_mod128 (k : Nat)
    (hmod : k%128=124) (hsize : 256≤k) : ¬ CReach 1 k := by
  let x1 := k-1
  let y1 := (k-2)/2
  let x2 := (x1+y1-4)/2
  let y2 := (x1+3*y1-10)/4
  let x3 := x2+y2-2
  let y3 := (y2-2)/2
  let x4 := x3+y3-2
  let y4 := (y3-2)/2
  have hfour : k=4*(k/4) := by omega
  have hj : 1≤k/4 := by omega
  intro hr
  have hr0 : CReach 1 (4*(k/4)) := by rw [←hfour]; exact hr
  have hr1 : CReach x1 y1 := by
    have hh := (blank_one_four_iff_feeder (k/4) hj).mp hr0
    have hx : 4*(k/4)-1=k-1 := by omega
    have hy : 2*(k/4)-1=(k-2)/2 := by omega
    rw [hx, hy] at hh
    exact hh
  have hx1 : x1%128=123 := by dsimp [x1]; omega
  have hy1 : y1%64=61 := by dsimp [y1]; omega
  have hx2 : x2%16=10 := by dsimp [x2]; omega
  have hy2 : y2%16=10 := by dsimp [y2]; omega
  have hx3 : x3%8=2 := by dsimp [x3]; omega
  have hy3 : y3%8=4 := by dsimp [y3]; omega
  have hx4 : x4%4=0 := by dsimp [x4]; omega
  have hy4 : y4%4=1 := by dsimp [y4]; omega
  have sy1 : 5≤y1 := by dsimp [y1]; omega
  have sy2 : 6≤y2 := by dsimp [y2]; omega
  have sy3 : 6≤y3 := by dsimp [y3]; omega
  have sy4 : 5≤y4 := by dsimp [y4]; omega
  have hgate1 : x1%2=1 ∧ y1%2=1 ∧ 5≤y1 ∧
      (x1+y1)%4=0 ∧ (x1+y1)%16≠0 ∧ 24≤x1+y1 := by
    omega
  have hr2 : CReach x2 y2 := by
    have hh := (oddodd_lowval_blank_reach_iff x1 y1 hgate1.1 hgate1.2.1
      hgate1.2.2.1 hgate1.2.2.2.1 hgate1.2.2.2.2.1 hgate1.2.2.2.2.2).mp hr1
    exact hh
  have hgate2 : 6≤y2 ∧ y2%2=0 ∧ (x2+y2)%8≠0 ∧ (x2+y2)%8≠7 := by
    omega
  have hr3 : CReach x3 y3 := by
    exact (BB6.Agent46.six_even_right_blank_reach_iff x2 y2 hgate2.1 hgate2.2.1
      hgate2.2.2.1 hgate2.2.2.2).mp hr2
  have hgate3 : 6≤y3 ∧ y3%2=0 ∧ (x3+y3)%8≠0 ∧ (x3+y3)%8≠7 := by
    omega
  have hr4 : CReach x4 y4 := by
    exact (BB6.Agent46.six_even_right_blank_reach_iff x3 y3 hgate3.1 hgate3.2.1
      hgate3.2.2.1 hgate3.2.2.2).mp hr3
  have hbad : 5≤y4 ∧ y4%2=1 ∧ (x4+y4)%4=1 := by
    omega
  exact blank_no_bad_odd_sum x4 y4 hbad.1 hbad.2.1 hbad.2.2 hr4

#print axioms blank_no_one_124_mod128
end BB6.Agent3
