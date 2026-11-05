import S4TogglePhases
import Lean.Elab.Tactic.Omega

namespace S4ToggleGates
open S4Power S4Octet S4Toggle S4TogglePhases
set_option maxHeartbeats 0

theorem gate283 (S : List Nat) :
    P (283::S)=none ↔ Pow2 (W S+1023) := by
  rw [p283, Option.map_eq_none_iff]
  exact G_none_iff_power 1023 S (by omega)

theorem gate281 (S : List Nat) :
    P (281::S)=none ↔ Pow2 (W S+739) := by
  rw [p281, Option.map_eq_none_iff]
  exact G_none_iff_power 739 S (by omega)

theorem gate280 (S : List Nat) :
    P (280::S)=none ↔
    Pow2 (W S+395) ∨
    ∃ U, G 395 S=some U ∧ Pow2 (W U+624) := by
  rw [p280]
  constructor
  · intro hnone
    cases h : G 395 S with
    | none => exact Or.inl ((G_none_iff_power 395 S (by omega)).mp h)
    | some U =>
        have hn : G 624 U=none := by simpa [h] using hnone
        exact Or.inr ⟨U,rfl,(G_none_iff_power 624 U (by omega)).mp hn⟩
  · rintro (hpow | ⟨U,hU,hpow⟩)
    · have hn := (G_none_iff_power 395 S (by omega)).mpr hpow
      simp [hn]
    · have hn := (G_none_iff_power 624 U (by omega)).mpr hpow
      simp [hU,hn]

theorem gate282 (S : List Nat) :
    P (282::S)=none ↔
    Pow2 (W S+396) ∨
    ∃ U, G 396 S=some U ∧
       (Pow2 (W U+343) ∨
        ∃ V, G 343 U=some V ∧ Pow2 (W V+281)) := by
  rw [p282]
  constructor
  · intro hnone
    cases h : G 396 S with
    | none => exact Or.inl ((G_none_iff_power 396 S (by omega)).mp h)
    | some U =>
        cases h2 : G 343 U with
        | none =>
            have hp := (G_none_iff_power 343 U (by omega)).mp h2
            exact Or.inr ⟨U,rfl,Or.inl hp⟩
        | some V =>
            have h3 : G 281 V=none := by simpa [h,h2] using hnone
            exact Or.inr ⟨U,rfl,Or.inr ⟨V,h2,(G_none_iff_power 281 V (by omega)).mp h3⟩⟩
  · rintro (hp | ⟨U,hU,(hp | ⟨V,hV,hp⟩)⟩)
    · have hn := (G_none_iff_power 396 S (by omega)).mpr hp
      simp [hn]
    · have hn := (G_none_iff_power 343 U (by omega)).mpr hp
      simp [hU,hn]
    · have hn := (G_none_iff_power 281 V (by omega)).mpr hp
      simp [hU,hV,hn]

#print axioms gate283
#print axioms gate281
#print axioms gate280
#print axioms gate282
end S4ToggleGates
