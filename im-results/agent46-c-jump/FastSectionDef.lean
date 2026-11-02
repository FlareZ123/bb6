import BounceProof
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

/-- Complete arithmetic two-counter section map, with exact CLine elapsed time. -/
def exactSection (p : Nat × Nat) : Nat × Option (Nat × Nat) :=
  let (a,k) := p
  if a=0 then
    if k=0 then (2,none)
    else if k=1 then (4,some (0,4))
    else
      let b := bounce 1 (2*k+1)
      (2+b.1,b.2)
  else if a=1 then
    if k=0 then (2,some (5,1))
    else if k=1 then (2,some (2,3))
    else if k=2 then (3,some (2,5))
    else if k=3 then (5,some (0,7))
    else
      let b := bounce 4 (2*k-3)
      (3+b.1,b.2)
  else if k=0 then (2,some (a-2,2))
  else if 2*k≤a then (2*k+1,some (a-2*k,2*k+2))
  else
    let b := bounce (a-1) (2*k-a+3)
    (a-1+b.1,b.2)

def secTime (p : Nat × Nat) : Nat := (exactSection p).1
def secNext (p : Nat × Nat) : Option (Nat × Nat) := (exactSection p).2

end BB6.Agent46
