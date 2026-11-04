import BottomBoundary
import DeepSecondFinal
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29Depth
open BB6.Agent46

private theorem two_pow_at_least_linear (n : Nat) : n+1≤2^n := by
  induction n with
  | zero => decide
  | succ n ih =>
      rw [Nat.pow_succ]
      omega

/-- Genuine blank-orbit exclusion for the entire deep second-stopping
    subfamily whose true affine-normalized residual has right counter
    exactly four. This is a semantic reachability theorem, not merely
    a modular or finite inverse-step filter. -/
theorem second_deep_right_four_unreachable (j m k : Nat)
    (hgate : k+j+3*m+5=2^(2*m+2)*(j+3))
    (hj : j%2=0) (hm : m%2=1) (hs : (j+m)%4=3)
    (hright : (BB6.Agent15.affineNormalize (2*j+3) k).2=4) :
    ¬BB6.Agent15.CReach (2*j+3) k := by
  intro hr
  let p := BB6.Agent15.affineNormalize (2*j+3) k
  have hd := BB6.Agent15.second_halt_deep_sector j m k hgate hj hm hs
  have hodd : p.1%2=1 := by
    have hsum := hd.2.2.2.1
    dsimp [p] at *
    omega
  have hrnorm : BB6.Agent15.CReach p.1 p.2 :=
    (BB6.Agent15.reach_iff_normalize (2*j+3) k).mp hr
  obtain ⟨t,ht⟩ := hrnorm
  have hfour : p.2=4 := hright
  have ht4 : BB6.Agent8Section.run secNext t (some (5,1))=some (p.1,4) := by
    simpa only [hfour] using ht
  have hp3 := (BB6.Agent29Bottom.blank_odd_four_exact_time t p.1 hodd ht4).2
  have hp := two_pow_at_least_linear (BB6.Agent15.oddDepth k)
  have hdepth := hd.2.2.1
  have hmass := hd.2.2.2.1
  have hscale := hd.2.2.2.2
  dsimp [p] at hp3 hmass hscale hfour
  rw [hfour] at hmass hscale
  omega

#print axioms second_deep_right_four_unreachable
end BB6.Agent29Depth
