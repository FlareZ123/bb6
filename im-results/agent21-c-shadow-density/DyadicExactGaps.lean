import DyadicAllowedHigh
import DyadicFirstBranch

namespace BB6.Agent21Duality
open BB6.Agent42ModularCone
open BB6.Agent21Dyadic

/-- A positive power of two that divides a signed integer of exact
    dyadic valuation v cannot have exponent greater than v. -/
theorem exact_val_gap_le (b v r : Nat) (s : Pair)
    (hv : ValValid b s v) (hr : I r∣q s) : r≤v := by
  by_cases hn : r≤v
  · exact hn
  have hle : v+1≤r := by omega
  have hsplit : I (v+1)∣I r := by
    refine ⟨I (r-(v+1)),?_⟩
    rw [I_split hle]
    ac_rfl
  have hdiv := Int.dvd_trans hsplit hr
  have hz := Int.emod_eq_zero_of_dvd hdiv
  rw [hv.2] at hz
  have hp := I_pos v
  omega

/-- Every compatible first letter of a signed inverse word is
    *exactly* one of the branches the modular cone checker enumerates.
    No arbitrary inverse gaps or missing high branches exist. -/
theorem valuation_first_gap_classification
    (b v r : Nat) (s : Pair)
    (hv : ValValid b s v)
    (hr : 0<r)
    (hpar : (r:Int)%2=(s.y+1)%2)
    (hdiv : P r∣-(q s)) :
    (r=1 ∧ s.y%2=0) ∨
      (∃ n : Nat, r=n+2 ∧ Allowed s v n) := by
  have hd' : I r ∣ q s := by
    have hI : I r=P r := by
      simp [I,BB6.Agent42ModularCone.P,P]
    rw [hI]
    have hh : P r∣-(-(q s)) := (dvd_neg.mpr hdiv)
    simpa only [neg_neg] using hh
  have hrle : r≤v := exact_val_gap_le b v r s hv hd'
  by_cases h1 : r=1
  · left
    refine ⟨h1,?_⟩
    rw [h1] at hpar
    omega
  · right
    let n := r-2
    have hn : r=n+2 := by dsimp [n]; omega
    refine ⟨n,hn,?_⟩
    constructor
    · omega
    · unfold BB6.Agent42ModularCone.odd
      dsimp [n]
      omega

#print axioms valuation_first_gap_classification
end BB6.Agent21Duality
