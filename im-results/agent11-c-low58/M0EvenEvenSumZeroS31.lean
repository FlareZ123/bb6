import M0EvenEvenSumZero
import EvenOddFourExact
import Lean.Elab.Tactic.Omega

namespace BB6.Agent11M0SumZeroS31
open BB6.Agent3

/-- For s=32*w+31, the B_s sum-zero target has both source parents
    excluded: the direct parent is an even/odd-four state whose unique
    parent is odd with sum 2 mod 4; the bounce parent is odd with sum
    1 mod 4. -/
theorem blank_no_B_s31 (w : Nat) :
    ¬ BB6.Agent3.CReach (2844+2880*w) (6668+6752*w) := by
  let x := 2844+2880*w
  let y := 6668+6752*w
  let S := 1189+1204*w
  have hD : ¬ BB6.Agent3.CReach (x+y-2) ((y-2)/2) := by
    have hx : x+y-2=9510+9632*w := by dsimp [x,y]; omega
    have hy : (y-2)/2=3333+3376*w := by dsimp [y]; omega
    rw [hx,hy]
    intro hreach
    have hP := (evenodd_four_blank_reach_iff
      (9510+9632*w) (3333+3376*w)
      (by omega) (by omega) (by omega) (by omega)).mp hreach
    exact BB6.Agent11High.blank_no_odd_sum_two
      (6419+6504*w) (4875+4940*w)
      (by omega) (by omega) (by omega) hP
  have hE : ¬ BB6.Agent3.CReach (2*S-2) ((x+2*y-2*S-8)/2) := by
    have hx : 2*S-2=2376+2408*w := by dsimp [S]; omega
    have hy : (x+2*y-2*S-8)/2=6897+6988*w := by
      dsimp [x,y,S]
      omega
    rw [hx,hy]
    exact BB6.Agent11M0SumZeroVerified.blank_no_odd_sum_one
      (2376+2408*w) (6897+6988*w)
      (by omega) (by omega) (by omega) (by omega)
  have hxgt : 5<x := by dsimp [x]; omega
  have hxe : x%2=0 := by dsimp [x]; omega
  have hyge : 6≤y := by dsimp [y]; omega
  have hye : y%2=0 := by dsimp [y]; omega
  have hsum : x+y=8*S := by dsimp [x,y,S]; omega
  have hS4 : S%4≠0 := by dsimp [S]; omega
  have hSgt : 2<S := by dsimp [S]; omega
  exact BB6.Agent11M0SumZeroVerified.blank_no_sumzero_target
    x y S hxgt hxe hyge hye hsum hS4 hSgt hD hE

#print axioms blank_no_B_s31
end BB6.Agent11M0SumZeroS31
