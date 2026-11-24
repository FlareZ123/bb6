import CapAnchorRoots

namespace CapSieve

/-- A final terminal band determines the entering band, exponent and weight
    by stripping its exact power of three. -/
def terminalFromBand (i : Nat) : Option (Nat × Nat) :=
  let s := strip3 (2*i+3)
  let k := i-s.1
  if 5≤k then (terminalAt k s.1).map (fun q => (k,q))
  else none

theorem terminal_from_band_iff {i k q : Nat} :
    terminalFromBand i=some (k,q) ↔
    5≤k ∧ ∃ n, i=k+n ∧ terminalAt k n=some q := by
  constructor
  · intro h
    have hvalid : CapNegative.Valid i (2*i+3) := by unfold CapNegative.Valid; omega
    unfold terminalFromBand at h
    dsimp at h
    split at h
    next hk =>
      cases he : terminalAt (i-(strip3 (2*i+3)).1) (strip3 (2*i+3)).1 with
      | none => simp [he] at h
      | some v =>
        rw [he] at h
        simp only [Option.map_some] at h
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
        exact ⟨hk,_,by omega,he⟩
    next h => contradiction
  · rintro ⟨hk,n,rfl,h⟩
    obtain ⟨hc,he⟩ := terminal_at_sound (by omega : 1≤k) h
    have hf : positiveNext k q<k+7 := by
      by_cases hh : positiveNext k q<k+7
      · exact hh
      · have hb : 2*k+7<2*positiveNext k q-3 := by omega
        have hbig := CapNegative.above_grows hb n
        omega
    have hw := entry_weight hc.1 hf
    have hunit : (2*positiveNext k q-3)%3≠0 := by
      rw [hw.2]
      rcases two_unit_phase k with h|h <;> omega
    have hstrip := strip3_unique hunit he.symm
    unfold terminalFromBand
    rw [hstrip]
    dsimp
    rw [show k+n-n=k by omega,if_pos hk,h]
    rfl

theorem anchor_terminal_band_iff {a : Nat} (ha : CanonQ 5 a) :
    (∃ limit, signedHaltBy limit 5 a=true) ↔
    ∃ i k q, terminalFromBand i=some (k,q) ∧ anchorOf k q=some (5,a) := by
  rw [anchor_terminal_iff ha]
  constructor
  · rintro ⟨k,n,q,hk,ht,ha'⟩
    exact ⟨k+n,k,q,terminal_from_band_iff.mpr ⟨hk,n,rfl,ht⟩,ha'⟩
  · rintro ⟨i,k,q,ht,ha'⟩
    obtain ⟨hk,n,_,he⟩ := terminal_from_band_iff.mp ht
    exact ⟨k,n,q,hk,he,ha'⟩

/-- One canonical candidate at most per final terminal band. -/
theorem terminal_final_unique {k n q j m v : Nat}
    (hk : 5≤k) (hj : 5≤j) (he : k+n=j+m)
    (ht : terminalAt k n=some q) (hu : terminalAt j m=some v) :
    k=j ∧ n=m ∧ q=v := by
  have h1 := terminal_from_band_iff.mpr ⟨hk,n,rfl,ht⟩
  have h2 := terminal_from_band_iff.mpr ⟨hj,m,he,hu⟩
  rw [h1] at h2
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h2)
  exact ⟨rfl,by omega,rfl⟩

#print axioms terminal_from_band_iff
#print axioms anchor_terminal_band_iff
#print axioms terminal_final_unique
end CapSieve
