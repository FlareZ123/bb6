import Lean.Elab.Tactic.Omega

namespace LeftOneWitness

/-- Source-equation transcription: Agent46 BounceCalc, with a structural fuel. -/
def bounceFuel : Nat → Nat → Nat → Option (Nat × Nat)
  | 0, _, _ => none
  | fuel+1, k, c =>
    if c < 4 then none
    else if k%2 = 1 then
      if c ≤ 2*k+6 then some (2*k+6-c, c)
      else bounceFuel fuel (2*k+3) (c-(2*k+3))
    else if c = 4 then some (2*k+2, 3)
    else if c = 5 then none
    else if c ≤ 2*k+8 then some (2*k+8-c, c-1)
    else bounceFuel fuel (2*k+4) (c-(2*k+5))

def bounce (k c : Nat) : Option (Nat × Nat) := bounceFuel (c+1) k c

/-- Source-equation transcription: Agent46 FastSectionDef.secNext. -/
def next (p : Nat × Nat) : Option (Nat × Nat) :=
  let (a,k) := p
  if a=0 then
    if k=0 then none
    else if k=1 then some (0,4)
    else bounce 1 (2*k+1)
  else if a=1 then
    if k=0 then some (5,1)
    else if k=1 then some (2,3)
    else if k=2 then some (2,5)
    else if k=3 then some (0,7)
    else bounce 4 (2*k-3)
  else if k=0 then some (a-2,2)
  else if 2*k≤a then some (a-2*k,2*k+2)
  else bounce (a-1) (2*k-a+3)

def run : Nat → Option (Nat × Nat)
  | 0 => some (5,1)
  | n+1 => (run n).bind next

/-- The boolean is true precisely when every visited *strictly earlier* section had a != 1. -/
def scan : Nat → Option (Nat × Nat) × Bool
  | 0 => (some (5,1),true)
  | n+1 =>
    let (p, ok) := scan n
    (p.bind next, ok && (p.map Prod.fst != some 1))

set_option maxRecDepth 30000
set_option maxHeartbeats 0

theorem left_one_at_957 : run 957 = some (1,3310) := by decide

theorem earliest_left_one_certificate : scan 957 = (some (1,3310),true) := by decide

#print axioms left_one_at_957
#print axioms earliest_left_one_certificate
end LeftOneWitness
