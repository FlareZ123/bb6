import OddEvenOddCone
import Lean.Elab.Tactic.Omega

namespace BB6.Agent3
open BB6.Agent46

/-- A fourth forced source predecessor yields an all-time forbidden
    two-dimensional cone from a new 512-residue affine pullback.
    Unlike the previous 128-cone, the tested M256 and M512 quotients
    admit concrete members of this region. -/
theorem affine_odd_even_odd_cone_unreachable (x y time : Nat)
    (hy20 : 20≤y)
    (hs1 : (x+y)%8=5)
    (hs2 : (2*x+y)%512=326) :
    BB6.Agent8Section.run secNext time (some (5,1)) ≠ some (x,y) := by
  have hall :
      4≤y ∧ y%2=0 ∧ (x+y)%4=1 ∧
      9≤(y-2)/2 ∧ (x+y-2)%8=3 ∧
      ((y-2)/2)%256 = ((x+y-2)+94)%256 := by
    omega
  rcases hall with ⟨hy4,hye,hs4,hb9,ha8,hmod⟩
  intro ht
  obtain ⟨n,hn⟩ := (BB6.Agent15.blank_reach_iff_affine x y hy4 hye hs4).mp
    ⟨time,ht⟩
  exact odd_even_odd_cone_unreachable (x+y-2) ((y-2)/2) n ha8 hmod hb9 hn

#print axioms affine_odd_even_odd_cone_unreachable
end BB6.Agent3
