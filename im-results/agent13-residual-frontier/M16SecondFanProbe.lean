import CSourceBridge16

namespace BB6.Agent13M16SecondFan

/-- Residue of the first parent coordinate supplied by Agent 21. -/
def aResidue (s : Nat) : Nat := (16 - ((2*s+3)%16))%16

/-- Residue of the second parent coordinate, with n=2*r. -/
def kResidue (r s : Nat) : Nat := (s+5+16-(3*r)%16)%16

/-- Since both concrete parent coordinates are at least eight, their
    M16 quotient images are determined by these residues.  Adding 16
    chooses a canonical representative in the large-coordinate branch. -/
def qRep (x : Nat) : Nat := CCert.q (x+16)

def parentAbsent (r s : Nat) : Bool :=
  !(CCert.seen (qRep (aResidue s))
    (qRep (kResidue r s)) (CCert.q 0))

def excludedS (r : Nat) : List Nat :=
  (List.range 16).filter (parentAbsent r)

def rowMask (r : Nat) : Nat :=
  (excludedS r).foldl (fun acc s => acc + 2^s) 0

/-- Exact M16 lookup for all n=2*r (mod 32) and all s=(F/2^n) mod 16.
    A set bit s means the corresponding quotient parent is absent from
    the kernel-certified M16 reachable-state table. -/
#eval (List.range 16).map (fun r => (r, rowMask r, excludedS r))

/-- n-classes for which every one of the sixteen parent cells is absent. -/
#eval (List.range 16).filter (fun r => rowMask r = 65535)

/-- Total number of absent parent cells in this 16-by-16 fan. -/
#eval (List.range 16).foldl (fun acc r => acc + (excludedS r).length) 0

end BB6.Agent13M16SecondFan
