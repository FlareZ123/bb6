import Lean
import Lean.Elab.Tactic.Omega

namespace BB6.Agent29New

/-- Exact residue consequences for the three forced genuine-source edges
in the previously surviving x=5 (mod16) half of the new sum96 sector. -/
theorem three_link_properties (x y : Nat)
    (hx:x%64=37) (hs:(x+y+1)%128=96) (hy:58≤y) :
    let a := x+y-2
    let k := (y-2)/2
    let b := a+k-2
    let l := (k-2)/2
    let c := (b+l-4)/2
    let d := (b+3*l-10)/4
    4≤k ∧ k%2=0 ∧ (a+k)%4=1 ∧
    b%2=1 ∧ l%2=1 ∧ 5≤l ∧ (b+l)%4=0 ∧
    (b+l)%16≠0 ∧ 24≤b+l ∧
    5≤d ∧ d%2=1 ∧ (c+d)%4=1 := by
  dsimp
  omega

#print axioms three_link_properties
end BB6.Agent29New
