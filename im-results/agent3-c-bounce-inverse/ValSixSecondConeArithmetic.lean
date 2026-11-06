import Lean
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3ValSix

/-- Backward exact arithmetic chain for a second forbidden two-dimensional
original-blank section cylinder. All guards and terminal image violation. -/
theorem second_cone_arithmetic (x y:Nat)
    (hx:x%256=165) (hy:y%256=26) :
    let a := x+y-2
    let k := (y-2)/2
    let b := a+k-2
    let l := (k-2)/2
    let c := (b+l-4)/2
    let d := (b+3*l-10)/4
    let e := (c+d-5)/2
    let f := (c+3*d-9)/4
    x%16=5 ∧ y%16=10 ∧ (x+y+1)%256=192 ∧
    4≤k ∧ k%2=0 ∧ (a+k)%4=1 ∧
    b%2=1 ∧ l%2=1 ∧ 5≤l ∧ (b+l)%4=0 ∧ (b+l)%16≠0 ∧ 24≤b+l ∧
    c%2=0 ∧ d%2=1 ∧ 5≤d ∧ (c+d+1)%16=8 ∧ 23≤c+d ∧
    f%2=1 ∧ 5≤f ∧ (e+f)%4=2 := by
  dsimp
  omega

#print axioms second_cone_arithmetic
end BB6.Agent3ValSix
