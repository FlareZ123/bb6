import P1RAffineGeneral
namespace BB6.Agent12Affine

/-- Eight new all-q P1 critical sectors n≡18 or34 modulo64. -/
def twoSectorSeeds : List Nat := [226,418,466,482,546,674,802,914]
def seedOK (R:Nat):Bool :=
  decide (32≤R ∧ R%2=0 ∧ 2*R+16≤131072) &&
  goodAff 12 (131072,131072-2*R-16) (0,3)
theorem seeds_valid : twoSectorSeeds.all seedOK = true := by decide +kernel
theorem blank_no_critical_two_seeds (R q : Nat) (h : R ∈ twoSectorSeeds) :
  ¬BB6.Agent1.Reach 2
    (14*2^(65536*q+R)-2*(65536*q+R)-10) := by
  have hgood := (List.all_eq_true.mp seeds_valid) R h
  simp only [seedOK] at hgood
  obtain ⟨hb,hcert⟩ := Bool.and_eq_true_iff.mp hgood
  obtain ⟨hlo,he,hhi⟩ := of_decide_eq_true hb
  exact blank_no_critical_of_affine_check R q hlo he hhi hcert
#print axioms blank_no_critical_two_seeds
end BB6.Agent12Affine
