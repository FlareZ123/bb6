import FirstInverseComplete

namespace Agent10T0Parent
open CascadeResetInverse

/-- First-failure level certificate used only for the boundary witness. -/
def FirstFailureAt (h k : Nat) : Prop :=
  (∀ j, j < k → 8*2^j ≤ h+j+5) ∧ h+k+5 < 8*2^k

def boundaryEntry (K : Nat) : Nat := 4*2^K-K-4
def boundaryParent (K : Nat) : Nat := 4*2^K-3*K-7

private theorem pow_two_ge_add_four (K : Nat) (hK : 4 ≤ K) :
    K+4 ≤ 2^K := by
  induction K, hK using Nat.le_induction with
  | base => norm_num
  | succ K hK ih =>
      have hpow : 2^(K+1)=2^K*2 := by rw [Nat.pow_succ]
      have hmul : 2*(K+4) ≤ 2*2^K := Nat.mul_le_mul_left 2 ih
      rw [hpow]
      omega

/-- The upper endpoint delta=2K+4 is attained by a genuine even
    ResetParent edge from a level-(K-1) state to the first level-K entry. -/
theorem boundary_is_even_parent (K : Nat) (hK : 266 ≤ K) :
    ResetParent (boundaryParent K) (boundaryEntry K) ∧
    FirstFailureAt (boundaryParent K) (K-1) ∧
    FirstFailureAt (boundaryEntry K) K := by
  have hp : K+4 ≤ 2^K := pow_two_ge_add_four K (by omega)
  have hpow : 2^K=2*2^(K-1) := by
    have h : (K-1)+1=K := by omega
    rw [← h, Nat.pow_succ]
    ac_rfl
  have h4 : 4*2^(K-1)=2*2^K := by rw [hpow]; ring
  have h8 : 8*2^(K-1)=4*2^K := by rw [hpow]; ring
  have h6 : 6*2^(K-1)=3*2^K := by rw [hpow]; ring
  have hParentLow :
      4*2^(K-1) ≤ boundaryParent K+(K-1)+4 := by
    rw [h4]
    dsimp [boundaryParent]
    omega
  have hParentHigh :
      boundaryParent K+(K-1)+5 < 8*2^(K-1) := by
    rw [h8]
    dsimp [boundaryParent]
    omega
  have hParentGuards :
      ∀ j, j<K-1 → 8*2^j≤boundaryParent K+j+5 :=
    guards_from_low (boundaryParent K) (K-1) hParentLow
  have hEntryLow :
      4*2^K ≤ boundaryEntry K+K+4 := by
    dsimp [boundaryEntry]
    omega
  have hEntryHigh :
      boundaryEntry K+K+5 < 8*2^K := by
    dsimp [boundaryEntry]
    omega
  have hEntryGuards :
      ∀ j, j<K → 8*2^j≤boundaryEntry K+j+5 :=
    guards_from_low (boundaryEntry K) K hEntryLow
  have hBandLow :
      6*2^(K-1)-1 ≤ boundaryEntry K := by
    rw [h6]
    dsimp [boundaryEntry]
    omega
  have hBandHigh :
      boundaryEntry K ≤ 8*2^(K-1)-3 := by
    rw [h8]
    dsimp [boundaryEntry]
    omega
  have hEvenEquation :
      2*boundaryEntry K =
        8*2^(K-1)+boundaryParent K+(K-1) := by
    rw [h8]
    dsimp [boundaryEntry,boundaryParent]
    omega
  refine ⟨Or.inl ⟨K-1,⟨hBandLow,hBandHigh⟩,hEvenEquation⟩,?_,?_⟩
  · exact ⟨hParentGuards,hParentHigh⟩
  · exact ⟨hEntryGuards,hEntryHigh⟩

/-- The witness has exactly the disputed entry deficit. -/
theorem boundary_entry_deficit (K : Nat) (hK : 266 ≤ K) :
    8*2^K+K-boundaryEntry K = 4*2^K+2*K+4 := by
  have hp : K+4 ≤ 2^K := pow_two_ge_add_four K (by omega)
  dsimp [boundaryEntry]
  omega

#print axioms boundary_is_even_parent
#print axioms boundary_entry_deficit

end Agent10T0Parent
