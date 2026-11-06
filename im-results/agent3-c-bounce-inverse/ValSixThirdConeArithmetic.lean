import Lean
import Lean.Elab.Tactic.Omega
namespace BB6.Agent3ValSix

theorem third_cone_arithmetic (x y:Nat)
    (hy:y%64=58) (hmod:(x+y+1)%256=192) :
    let a := x+y-2
    let k := (y-2)/2
    let b := a+k-2
    let l := (k-2)/2
    let c := (b+l-4)/2
    let d := (b+3*l-10)/4
    x%16=5 ∧ y%16=10 ∧
    4≤k ∧ k%2=0 ∧ (a+k)%4=1 ∧
    b%2=1 ∧ l%2=1 ∧ 5≤l ∧ (b+l)%4=0 ∧ (b+l)%16≠0 ∧ 24≤b+l ∧
    d%2=1 ∧ 5≤d ∧ (c+d)%4=1 := by
  dsimp
  omega

#print axioms third_cone_arithmetic
end BB6.Agent3ValSix
