import CSourceBridge16

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace BB6.Agent13M16SecondFan

/-- Residue of the first parent coordinate supplied by Agent 21. -/
def aResidue (s : Nat) : Nat := (16 - ((2*s+3)%16))%16

/-- Residue of the second parent coordinate, with n=2*r. -/
def kResidue (r s : Nat) : Nat := (s+5+16-(3*r)%16)%16

/-- Since both concrete parent coordinates are at least eight, their
    M16 quotient images are determined by these residues. Adding 16
    chooses a canonical representative in the large-coordinate branch. -/
def qRep (x : Nat) : Nat := CCert.q (x+16)

def parentNotExcludedResidue (r s : Nat) : Bool :=
  CCert.seen (qRep (aResidue s))
    (qRep (kResidue r s)) (CCert.q 0)

def parentAbsent (r s : Nat) : Bool :=
  !(parentNotExcludedResidue r s)

def excludedS (r : Nat) : List Nat :=
  (List.range 16).filter (parentAbsent r)

def rowMask (r : Nat) : Nat :=
  (excludedS r).foldl (fun acc s => acc + 2^s) 0

def rowMasks : List Nat := (List.range 16).map rowMask

/-- Exact row masks: bit s is set precisely when the M16 quotient table
    does not contain the corresponding c=0 parent cell. -/
theorem rowMasks_exact :
    rowMasks =
      [38289,27234,19524,47320,22809,42534,17604,35215,
       37269,25194,17484,55480,6489,9894,50244,36745] := by
  decide +kernel

/-- No n mod 32 class has all sixteen possible parent cells absent. -/
theorem no_full_parent_row :
    ∀ r : Fin 16, rowMask r.val ≠ 65535 := by
  decide +kernel

/-- There are exactly 108 absent cells among the 256 parent cells. -/
theorem excluded_parent_count :
    (List.range 16).foldl
      (fun acc r => acc + (excludedS r).length) 0 = 108 := by
  decide +kernel

#print axioms rowMasks_exact
#print axioms no_full_parent_row
#print axioms excluded_parent_count

end BB6.Agent13M16SecondFan

#eval BB6.Agent13M16SecondFan.rowMasks
#eval (List.range 16).map
  (fun r => (r,BB6.Agent13M16SecondFan.excludedS r))
#eval (List.range 16).foldl
  (fun acc r => acc + (BB6.Agent13M16SecondFan.excludedS r).length) 0
#eval (List.range 16).filter
  (fun r => BB6.Agent13M16SecondFan.rowMask r = 65535
