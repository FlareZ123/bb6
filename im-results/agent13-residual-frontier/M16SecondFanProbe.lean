import CSourceBridge16

set_option maxRecDepth 20000
set_option maxHeartbeats 0

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

def rowMasks : List Nat := (List.range 16).map rowMask

/-- Exact row masks: bit s is set precisely when the M16 quotient table
    does not contain the corresponding c=0 parent cell. The individual
    16-cell rows are kernel-reduced separately to keep proof terms small. -/
theorem rowMask_0 : rowMask 0 = 38289 := by decide +kernel

theorem rowMask_1 : rowMask 1 = 27234 := by decide +kernel

theorem rowMask_2 : rowMask 2 = 19524 := by decide +kernel

theorem rowMask_3 : rowMask 3 = 47320 := by decide +kernel

theorem rowMask_4 : rowMask 4 = 22809 := by decide +kernel

theorem rowMask_5 : rowMask 5 = 42534 := by decide +kernel

theorem rowMask_6 : rowMask 6 = 17604 := by decide +kernel

theorem rowMask_7 : rowMask 7 = 35215 := by decide +kernel

theorem rowMask_8 : rowMask 8 = 37269 := by decide +kernel

theorem rowMask_9 : rowMask 9 = 25194 := by decide +kernel

theorem rowMask_10 : rowMask 10 = 17484 := by decide +kernel

theorem rowMask_11 : rowMask 11 = 55480 := by decide +kernel

theorem rowMask_12 : rowMask 12 = 6489 := by decide +kernel

theorem rowMask_13 : rowMask 13 = 9894 := by decide +kernel

theorem rowMask_14 : rowMask 14 = 50244 := by decide +kernel

theorem rowMask_15 : rowMask 15 = 36745 := by decide +kernel

theorem rowMasks_exact :
    rowMasks =
      [38289,27234,19524,47320,22809,42534,17604,35215,37269,25194,17484,55480,6489,9894,50244,36745] := by
  simp [rowMasks, rowMask_0, rowMask_1, rowMask_2, rowMask_3, rowMask_4, rowMask_5, rowMask_6, rowMask_7, rowMask_8, rowMask_9, rowMask_10, rowMask_11, rowMask_12, rowMask_13, rowMask_14, rowMask_15]

/-- No n mod 32 class has all sixteen possible parent cells absent. -/
theorem no_full_parent_row :
    ∀ r : Fin 16, rowMask r.val ≠ 65535 := by
  intro r h
  have hmem : rowMask r.val ∈ rowMasks := by
    unfold rowMasks
    apply List.mem_map.mpr
    exact ⟨r.val,List.mem_range.mpr r.isLt,rfl⟩
  rw [rowMasks_exact] at hmem
  simp at hmem
  omega

#print axioms rowMasks_exact
#print axioms no_full_parent_row

end BB6.Agent13M16SecondFan

#eval BB6.Agent13M16SecondFan.rowMasks
#eval (List.range 16).map
  (fun r => (r,BB6.Agent13M16SecondFan.excludedS r))
#eval (List.range 16).foldl
  (fun acc r => acc + (BB6.Agent13M16SecondFan.excludedS r).length) 0
#eval (List.range 16).filter
  (fun r => BB6.Agent13M16SecondFan.rowMask r = 65535)
