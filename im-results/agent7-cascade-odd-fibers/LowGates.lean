import Mass

namespace CascadeSource

/-- A finite check whose final state has greater mass than a fixed target.
    Returning true proves the target unreachable for the entire future orbit. -/
def shield : Nat → (Nat × Nat) → (Nat × Nat) → Bool
  | 0, s, t => decide (mass t < mass s)
  | n+1, s, t =>
      if s = t then false else
        match Cstep s.1 s.2 with
        | none => true
        | some u => shield n u t

/-- Soundness of arbitrary finite prefix certificates; no totality assumption
    and no assumption that the compressed dynamics eventually terminates. -/
theorem shield_sound : ∀ n s t, shield n s t = true → ¬Orbit s t := by
  intro n
  induction n with
  | zero =>
      intro s t h ho
      have hmass : mass t < mass s := by simpa [shield] using h
      have hm := orbit_mass_mono ho
      omega
  | succ n ih =>
      intro s t h ho
      have hne : s ≠ t := by
        intro he
        subst t
        simp [shield] at h
      cases s with
      | mk a b =>
        cases hc : Cstep a b with
        | none =>
            cases ho with
            | refl => exact hne rfl
            | step hstep htail => simp [hc] at hstep
        | some v =>
            have hsub : shield n v t = true := by
              simpa [shield, hne, hc] using h
            cases ho with
            | refl => exact hne rfl
            | step hstep htail =>
                rw [hc] at hstep
                have hp := Option.some.inj hstep
                cases hp
                exact ih _ _ hsub htail

/-- For all time from source-indexed C(2,0), the fourth fatal reset is absent. -/
theorem blank_excludes_fatal_four : ¬Orbit (2,0) (56,0) := by
  apply shield_sound 21
  decide

/-- For all time from source-indexed C(2,0), the fifth fatal reset is absent. -/
theorem blank_excludes_fatal_five : ¬Orbit (2,0) (119,0) := by
  apply shield_sound 28
  decide

#print axioms shield_sound
#print axioms blank_excludes_fatal_four
#print axioms blank_excludes_fatal_five

end CascadeSource
