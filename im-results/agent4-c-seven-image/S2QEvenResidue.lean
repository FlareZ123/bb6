import M0EvenEvenSumZero
import EvenOddFourExact
import Agent3CImage
import Lean.Elab.Tactic.Omega

set_option maxRecDepth 8192

namespace BB6.Agent4SevenS2QEven
open BB6.Agent46

/-- In the complementary lift v=12+11*t-32*z, the direct parent of
    the two-step even-right residual is an even/odd valuation-two state.
    Its unique source parent is odd/odd with forbidden sum 2 mod 4. -/
theorem q_even_direct_parent_unreachable (t z : Nat)
    (hhi : 32*z ≤ 12+11*t)
    (hcong : (2*t-z)%8=1) :
    ¬ BB6.Agent3.CReach
      (14886+14224*t-30344*z) (593+568*t-1212*z) := by
  let x := 14886+14224*t-30344*z
  let y := 593+568*t-1212*z
  let a := 7737+7396*t-15778*z
  let k := 4164+3982*t-8495*z
  have hzodd : z%2=1 := by omega
  have hhi38 : 1216*z ≤ 38*(12+11*t) := Nat.mul_le_mul_left 38 hhi
  have hhi266 : 8512*z ≤ 266*(12+11*t) := Nat.mul_le_mul_left 266 hhi
  have hhi494 : 15808*z ≤ 494*(12+11*t) := Nat.mul_le_mul_left 494 hhi
  have hx : x%2=0 := by dsimp [x]; omega
  have hy : y%2=1 := by dsimp [y]; omega
  have hy5 : 5≤y := by dsimp [y]; omega
  have hmod : (x+y+1)%8=4 := by dsimp [x,y]; omega
  have hxa : (x+y-5)/2=a := by dsimp [x,y,a]; omega
  have hyk : (x+3*y-9)/4=k := by dsimp [x,y,k]; omega
  have hsum : (a+k)%4=2 := by dsimp [a,k]; omega
  have hkodd : k%2=1 := by dsimp [k]; omega
  have hk5 : 5≤k := by dsimp [k]; omega
  have ha5 : 5<a := by dsimp [a]; omega
  intro hr
  have hr' : BB6.Agent3.CReach a k := by
    have hiff := (BB6.Agent3.evenodd_four_blank_reach_iff
      x y hx hy hy5 hmod).mp hr
    simpa only [hxa,hyk] using hiff
  rcases hr' with ⟨time,ht⟩
  cases time with
  | zero =>
      simp [BB6.Agent8Section.run] at ht
      omega
  | succ n =>
      have himage := BB6.Agent3.blank_section_odd_image
        n a k ht hk5 hkodd
      omega

/-- The complementary bounce parent is also excluded: its forced
    six-of-eight parent has odd right counter and sum one mod four. -/
theorem q_even_bounce_parent_unreachable (t z : Nat)
    (hhi : 32*z ≤ 12+11*t)
    (hcong : (2*t-z)%8=1) :
    ¬ BB6.Agent3.CReach
      (3720+3556*t-7586*z) (6173+5902*t-12591*z) := by
  let x := 3720+3556*t-7586*z
  let y := 6173+5902*t-12591*z
  let hx := x+y-2
  let hy := (y-2)/2
  have hhi394 : 12608*z ≤ 394*(12+11*t) := Nat.mul_le_mul_left 394 hhi
  have hhi631 : 20192*z ≤ 631*(12+11*t) := Nat.mul_le_mul_left 631 hhi
  have hye4 : y%4=0 := by dsimp [y]; omega
  have hye : y%2=0 := by omega
  have hy6 : 6≤y := by dsimp [y]; omega
  have hsum2 : (x+y)%4=2 := by dsimp [x,y]; omega
  have hnot0 : (x+y)%8≠0 := by omega
  have hnot7 : (x+y)%8≠7 := by omega
  have hHx : 5<hx := by dsimp [hx,x,y]; omega
  have hHy : 5≤hy := by dsimp [hy,y]; omega
  have hHyEq : 2*hy=y-2 := by dsimp [hy]; omega
  have hHyOdd : hy%2=1 := by omega
  have hHtwice : 2*(hx+hy)=25953+24818*t-52945*z := by
    dsimp [hx,x,y,hy]
    omega
  have hnum8 : (25953+24818*t-52945*z)%8=2 := by omega
  have hHsum : (hx+hy)%4=1 := by omega
  intro hr
  have hparent : BB6.Agent3.CReach hx hy := by
    have hiff := (BB6.Agent46.six_even_right_blank_reach_iff
      x y hy6 hye hnot0 hnot7).mp hr
    exact hiff
  exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
    hx hy hHx hHy hHyOdd hHsum hparent

/-- For the affine even-even target left by the two six-right reductions,
    both source parents are excluded on the residue cylinder
    2*t-z=1 (mod 8).  The upper bound on z is the naturality condition
    v=12+11*t-32*z >= 0 for the complementary image lift. -/
theorem q_even_normalizer_residual_unreachable (t z : Nat)
    (hhi : 32*z ≤ 12+11*t)
    (hcong : (2*t-z)%8=1) :
    ¬ BB6.Agent3.CReach
      (13700+13088*t-27920*z) (1188+1136*t-2424*z) := by
  let x := 13700+13088*t-27920*z
  let y := 1188+1136*t-2424*z
  let S := 1861+1778*t-3793*z
  let dx := 14886+14224*t-30344*z
  let dy := 593+568*t-1212*z
  let ex := 3720+3556*t-7586*z
  let ey := 6173+5902*t-12591*z
  have hhi76 : 2432*z ≤ 76*(12+11*t) := Nat.mul_le_mul_left 76 hhi
  have hhi119 : 3808*z ≤ 119*(12+11*t) := Nat.mul_le_mul_left 119 hhi
  have hhi873 : 27936*z ≤ 873*(12+11*t) := Nat.mul_le_mul_left 873 hhi
  have hx : 5<x := by dsimp [x]; omega
  have hxe : x%2=0 := by dsimp [x]; omega
  have hy : 6≤y := by dsimp [y]; omega
  have hye : y%2=0 := by dsimp [y]; omega
  have hsum : x+y=8*S := by dsimp [x,y,S]; omega
  have hS4 : S%4=2 := by dsimp [S]; omega
  have hSgt : 2<S := by dsimp [S]; omega
  have hDx : x+y-2=dx := by dsimp [x,y,dx]; omega
  have hDy : (y-2)/2=dy := by dsimp [y,dy]; omega
  have hEx : 2*S-2=ex := by dsimp [S,ex]; omega
  have hEy : (x+2*y-2*S-8)/2=ey := by
    dsimp [x,y,S,ey]
    omega
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    rw [hDx,hDy]
    exact q_even_direct_parent_unreachable t z hhi hcong
  have hE : ¬ BB6.Agent3.CReach
      (2*S-2) ((x+2*y-2*S-8)/2) := by
    rw [hEx,hEy]
    exact q_even_bounce_parent_unreachable t z hhi hcong
  exact BB6.Agent11M0SumZeroVerified.blank_no_v2one_target
    x y S hx hxe hy hye hsum hS4 hSgt hD hE

/-- A nonempty one-parameter subfamily satisfying the naturality
    inequalities and the source-exclusion congruence. -/
theorem q_even_progression_unreachable (n : Nat) (hn : 1≤n) :
    ¬ BB6.Agent3.CReach
      (13700+13088*(32*n+2)-27920*(8*n+3))
      (1188+1136*(32*n+2)-2424*(8*n+3)) := by
  have hhi : 32*(8*n+3) ≤ 12+11*(32*n+2) := by omega
  have hcong : (2*(32*n+2)-(8*n+3))%8=1 := by omega
  exact q_even_normalizer_residual_unreachable
    (32*n+2) (8*n+3) hhi hcong

#print axioms q_even_direct_parent_unreachable
#print axioms q_even_bounce_parent_unreachable
#print axioms q_even_normalizer_residual_unreachable
#print axioms q_even_progression_unreachable

end BB6.Agent4SevenS2QEven
