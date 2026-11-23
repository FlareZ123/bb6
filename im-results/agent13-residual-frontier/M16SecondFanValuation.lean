import M16SecondFanProbe

set_option maxRecDepth 20000
set_option maxHeartbeats 0

namespace BB6.Agent13M16SecondFan

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

#eval (List.range 4).map BB6.Agent13M16SecondFan.noUnexcludedParentQs
