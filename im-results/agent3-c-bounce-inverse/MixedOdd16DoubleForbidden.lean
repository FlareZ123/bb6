import MixedOdd16TwoOrbit
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

private theorem odd_forbidden_root_16 (u v : Nat)
    (hv : 5≤v) (ho : v%2=1) (hs : (u+v)%4=1) :
    ¬ CReach u v := by
  rintro ⟨n,hn⟩
  cases n with
  | zero => simp [BB6.Agent8Section.run] at hn; omega
  | succ n =>
      have hi := blank_section_odd_image n u v hn hv ho
      omega

/-- An exact binary-source-predecessor barrier over eight uniform
    infinite odd/odd section residue rectangles. Each of both source
    predecessors is individually excluded by the original odd-image
    theorem. This yields a root-unreachable source region even where
    the pre-existing M512 finite quotient admits projected cells. -/
theorem oddodd16_double_forbidden_rectangle (x y : Nat)
    (hx : x%8=5) (hy : y%8=3)
    (hmod : (x+y)%64=48) (hsize : 64≤y) :
    ¬ CReach x y := by
  have hmod32 : (x+y)%32=16 := by omega
  have hoddx : x%2=1 := by omega
  have hoddy : y%2=1 := by omega
  let a0 := (x+y-4)/2
  let k0 := (x+3*y-10)/4
  let a2 := (x+y-16)/8
  let k2 := (7*x+15*y-88)/16
  have hbad0 : 5≤k0 ∧ k0%2=1 ∧ (a0+k0)%4=1 := by
    dsimp [a0,k0]
    omega
  have hbad2 : 5≤k2 ∧ k2%2=1 ∧ (a2+k2)%4=1 := by
    dsimp [a2,k2]
    omega
  have h0 : ¬CReach a0 k0 :=
    odd_forbidden_root_16 a0 k0 hbad0.1 hbad0.2.1 hbad0.2.2
  have h2 : ¬CReach a2 k2 :=
    odd_forbidden_root_16 a2 k2 hbad2.1 hbad2.2.1 hbad2.2.2
  have hc := oddodd_sum16_blank_reach_iff x y hoddx hoddy hsize hmod32
  change CReach x y ↔ CReach a0 k0 ∨ CReach a2 k2 at hc
  intro hr
  rcases hc.mp hr with h | h
  · exact h0 h
  · exact h2 h

#print axioms oddodd16_double_forbidden_rectangle
end BB6.Agent3
