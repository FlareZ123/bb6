import Lean
import Lean.Elab.Tactic.Omega
namespace BB6.Agent29New
theorem four_link_properties (x y : Nat)
    (hx:x%128=117) (hs:(x+y+1)%128=96) (hy:106≤y) :
    let a := x+y-2
    let k := (y-2)/2
    let b := a+k-2
    let l := (k-2)/2
    let c := (b+l-4)/2
    let d := (b+3*l-10)/4
    let e := c+d-2
    let f := (d-2)/2
    4≤k ∧ k%2=0 ∧ (a+k)%4=1 ∧
    b%2=1 ∧ l%2=1 ∧ 5≤l ∧ (b+l)%4=0 ∧
    (b+l)%16≠0 ∧ 24≤b+l ∧
    6≤d ∧ d%2=0 ∧ (c+d)%8≠0 ∧ (c+d)%8≠7 ∧
    5≤f ∧ f%2=1 ∧ ((e+f)%4=1 ∨ (e+f)%4=2) := by
  dsimp
  omega
#print axioms four_link_properties
end BB6.Agent29New
