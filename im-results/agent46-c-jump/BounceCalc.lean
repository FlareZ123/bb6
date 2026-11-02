import JumpBounceSections
import Lean.Elab.Tactic.Omega

namespace BB6.Agent46

def bounce : (k c : Nat) → Nat × Option (Nat × Nat)
  | k,c =>
    if c<4 then (0,none)
    else if k%2=1 then
      if c≤2*k+6 then (c,some (2*k+6-c,c))
      else
        let out := bounce (2*k+3) (c-(2*k+3))
        (2*k+4+out.1,out.2)
    else if c=4 then (2,some (2*k+2,3))
    else if c=5 then (2,none)
    else if c≤2*k+8 then (c-3,some (2*k+8-c,c-1))
    else
      let out := bounce (2*k+4) (c-(2*k+5))
      (2*k+3+out.1,out.2)
termination_by k c => c
decreasing_by
  all_goals
    exact Nat.sub_lt (by omega) (by omega)

def embed0 (p : Nat × Nat) : S := (p.1,p.2,0)

end BB6.Agent46
