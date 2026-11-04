import Mass

namespace CascadeSource

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- Finite computed exclusion of an arbitrary list of target C-states. -/
def shieldSet : Nat → (Nat × Nat) → List (Nat × Nat) → Bool
  | 0, s, targets => targets.all (fun t => decide (mass t < mass s))
  | n+1, s, targets =>
      if s ∈ targets then false
      else match Cstep s.1 s.2 with
        | none => true
        | some u => shieldSet n u targets

/-- A true finite-list certificate excludes each listed state for all time. -/
theorem shieldSet_sound : ∀ k s targets,
    shieldSet k s targets = true → ∀ t ∈ targets, ¬Orbit s t := by
  intro k
  induction k with
  | zero =>
      intro s targets h t ht ho
      have hall := (List.all_eq_true.mp h) t ht
      have hm : mass t < mass s := by simpa only [decide_eq_true_eq] using hall
      have horb := orbit_mass_mono ho
      omega
  | succ k ih =>
      intro s targets h t ht ho
      have hnot : s ∉ targets := by
        intro hmem
        simp [shieldSet, hmem] at h
      have hne : s ≠ t := by
        intro hs
        exact hnot (hs ▸ ht)
      cases s with
      | mk a b =>
        cases hc : Cstep a b with
        | none =>
            cases ho with
            | refl => exact hne rfl
            | step hstep htail => simp [hc] at hstep
        | some u =>
            have hsub : shieldSet k u targets = true := by
              simpa [shieldSet, hnot, hc] using h
            cases ho with
            | refl => exact hne rfl
            | step hstep htail =>
                rw [hc] at hstep
                have hp := Option.some.inj hstep
                cases hp
                exact ih _ _ hsub _ ht htail

/-- Fatal first-entry reset height in the exact copied #746 C episode map. -/
def fatalHeight (n : Nat) : Nat := 4*2^n-n-4

/-- Finite target set restricted to the two surviving index classes. -/
def survivingTargets (N : Nat) : List (Nat × Nat) :=
  ((List.range (N+1)).filter (fun n => decide (n%6=4 ∨ n%6=5))).map
    (fun n => (fatalHeight n,0))

/-- Every surviving-class fatal index through 47 is permanently excluded
    from the authentic post-initial accelerated blank-root C(2,0) orbit. -/
theorem blank_excludes_survivors_through_47 (n : Nat)
    (hn : n ≤ 47) (hc : n%6=4 ∨ n%6=5) :
    ¬Orbit (2,0) (fatalHeight n,0) := by
  apply shieldSet_sound 1943 (2,0) (survivingTargets 47) (by decide)
  apply List.mem_map.mpr
  refine ⟨n, ?_, rfl⟩
  apply List.mem_filter.mpr
  constructor
  · exact List.mem_range.mpr (by omega)
  · simpa only [decide_eq_true_eq] using hc

#print axioms shieldSet_sound
#print axioms blank_excludes_survivors_through_47

end CascadeSource
