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

def parentNotExcludedResidue (r s : Nat) : Bool :=
  CCert.seen (qRep (aResidue s))
    (qRep (kResidue r s)) (CCert.q 0)

def parentAbsent (r s : Nat) : Bool :=
  !(parentNotExcludedResidue r s)

/-- For F=2^d*q and n=2*r, the quotient's third parent coordinate is
    s = (F/2^(2*r)) mod 16. -/
def sAt (d q r : Nat) : Nat := (2^(d-2*r)*q)%16

/-- At least one even-depth parent cell is not ruled out by the M16 table. -/
def hasUnexcludedParent (d q : Nat) : Bool :=
  (List.range (d/2+1)).any
    (fun r => parentNotExcludedResidue r (sAt d q r))

def noUnexcludedParentQs (d : Nat) : List Nat :=
  (List.range 16).filter
    (fun q => decide (q%2=1) && !(hasUnexcludedParent d q))

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

theorem r1_unexcluded_s0 : parentNotExcludedResidue 1 0 = true := by decide +kernel
theorem r1_unexcluded_s4 : parentNotExcludedResidue 1 4 = true := by decide +kernel
theorem r1_unexcluded_s8 : parentNotExcludedResidue 1 8 = true := by decide +kernel
theorem r1_unexcluded_s12 : parentNotExcludedResidue 1 12 = true := by decide +kernel

/-- For every odd q and every valuation d >= 4, the n=2 parent
    (r=1) is present in the M16 over-approximation. Thus this quotient
    cannot eliminate the complete second-parent fan at high valuations. -/
theorem every_d_ge4_has_unexcluded_parent
    (d q : Nat) (hd : 4≤d) (hq : q%2=1) :
    hasUnexcludedParent d q = true := by
  have hs : sAt d q 1 = 0 ∨ sAt d q 1 = 4 ∨
      sAt d q 1 = 8 ∨ sAt d q 1 = 12 := by
    by_cases hd6 : 6≤d
    · have hpow : 16 ∣ 2^(d-2) := by
        have hp : 2^4 ∣ 2^(d-2) := Nat.pow_dvd_pow 2 (by omega)
        simpa only [show (2:Nat)^4=16 by decide] using hp
      have hprod : 16 ∣ 2^(d-2)*q := by
        rcases hpow with ⟨t,ht⟩
        refine ⟨t*q,?_⟩
        rw [ht]
        simp [Nat.mul_assoc]
      left
      simpa [sAt] using Nat.mod_eq_zero_of_dvd hprod
    · have hd45 : d=4 ∨ d=5 := by omega
      rcases hd45 with h4|h5
      · subst d
        have hq4 : q%4=1 ∨ q%4=3 := by omega
        rcases hq4 with hq1|hq3
        · right; left
          have hval : (4*q)%16=4 := by omega
          simpa [sAt] using hval
        · right; right; right
          have hval : (4*q)%16=12 := by omega
          simpa [sAt] using hval
      · subst d
        right; right; left
        have hval : (8*q)%16=8 := by omega
        simpa [sAt] using hval
  have hseen : parentNotExcludedResidue 1 (sAt d q 1) = true := by
    rcases hs with h0|h4|h8|h12
    · rw [h0]; exact r1_unexcluded_s0
    · rw [h4]; exact r1_unexcluded_s4
    · rw [h8]; exact r1_unexcluded_s8
    · rw [h12]; exact r1_unexcluded_s12
  unfold hasUnexcludedParent
  apply List.any_eq_true.mpr
  exact ⟨1,List.mem_range.mpr (by omega),hseen⟩

/-- Exact low-valuation exceptions: for d=0..3, these are precisely
    the odd q residues for which every parent cell is excluded. -/
theorem low_valuation_no_unexcluded_parent_qs :
    (List.range 4).map noUnexcludedParentQs =
      [[7,15],[5,13],[1,5,9,11,13],[3,7,11,15]] := by
  decide +kernel

#print axioms every_d_ge4_has_unexcluded_parent
#print axioms low_valuation_no_unexcluded_parent_qs

end BB6.Agent13M16SecondFan

#eval BB6.Agent13M16SecondFan.rowMasks
#eval (List.range 16).map
  (fun r => (r,BB6.Agent13M16SecondFan.excludedS r))
#eval (List.range 16).foldl
  (fun acc r => acc + (BB6.Agent13M16SecondFan.excludedS r).length) 0
#eval (List.range 16).filter
  (fun r => BB6.Agent13M16SecondFan.rowMask r = 65535)
#eval (List.range 4).map BB6.Agent13M16SecondFan.noUnexcludedParentQs
