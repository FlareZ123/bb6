import Generate
namespace BB6.Agent43Block
open BB6.Agent43CarryCert
/-- Untrusted proposals for boundaries.  Each block is independently checked. -/
def proposeFrom (Q H j : Nat) (cs : List Nat) : Nat → List Nat
  | 0 => cs
  | k+1 => proposeFrom Q H (j+H) (blockStep Q j H cs) k

def proposeAt (Q H j : Nat) : List Nat :=
  if j=0 then [1] else
    let cs := step Q 0 [1]
    let k := (j-1)/H
    let r := (j-1)%H
    let ds := proposeFrom Q H 1 cs k
    if r=0 then ds else blockStep Q (1+k*H) r ds
end BB6.Agent43Block
