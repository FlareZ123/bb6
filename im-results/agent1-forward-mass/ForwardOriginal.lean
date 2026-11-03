import FastPrefix14
import FastSectionDef
import SectionMassStrict
import Lean.Elab.Tactic.Omega

namespace BB6.Agent1Forward

/-- The fuel simulator agrees with the original well-founded bounce for all
    natural inputs. Here the imported name denotes the original Agent46 source. -/
theorem fuel_agrees (c : Nat) : ∀ fuel k : Nat, c < fuel →
    FastC.bounceFuel fuel k c = (BB6.Agent46.bounce k c).2 := by
  induction c using Nat.strongRecOn with
  | ind c ih =>
    intro fuel k hf
    cases fuel with
    | zero => omega
    | succ f =>
      rw [BB6.Agent46.bounce.eq_1]
      simp only [FastC.bounceFuel]
      by_cases hlow : c < 4
      · simp [hlow]
      · simp only [if_neg hlow]
        by_cases hodd : k % 2 = 1
        · simp only [if_pos hodd]
          by_cases hstop : c ≤ 2*k+6
          · simp only [if_pos hstop]
          · simp only [if_neg hstop]
            have hlt : c-(2*k+3)<c := by omega
            have hfuel : c-(2*k+3)<f := by omega
            exact ih (c-(2*k+3)) hlt f (2*k+3) hfuel
        · simp only [if_neg hodd]
          by_cases hc4 : c=4
          · simp only [if_pos hc4]
          · simp only [if_neg hc4]
            by_cases hc5 : c=5
            · simp only [if_pos hc5]
            · simp only [if_neg hc5]
              by_cases hstop : c ≤ 2*k+8
              · simp only [if_pos hstop]
              · simp only [if_neg hstop]
                have hlt : c-(2*k+5)<c := by omega
                have hfuel : c-(2*k+5)<f := by omega
                exact ih (c-(2*k+5)) hlt f (2*k+4) hfuel

theorem bounce_agrees (k c : Nat) :
    FastC.bounce k c = (BB6.Agent46.bounce k c).2 := by
  exact fuel_agrees c (c+1) k (by omega)

private theorem if_snd {α β : Type} (cond : Prop) [Decidable cond]
    (x y : α × β) : (if cond then x else y).2 = if cond then x.2 else y.2 := by
  by_cases h : cond <;> simp [h]

theorem next_agrees (p : Nat × Nat) :
    FastC.next p = BB6.Agent46.secNext p := by
  rcases p with ⟨a,k⟩
  simp [FastC.next, BB6.Agent46.secNext, BB6.Agent46.exactSection,
    FastC.bounce, if_snd, fuel_agrees]

theorem run_agrees {α : Type} (f g : α → Option α)
    (h : ∀ p, f p = g p) (s : α) (n : Nat) :
    ForwardMass.run f s n = ForwardMass.run g s n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ForwardMass.run, ih]
    cases hc : ForwardMass.run g s n with
    | none => rfl
    | some p => simpa [hc] using h p

theorem source_trace :
    ForwardMass.run BB6.Agent46.secNext (5,1) 150052 = some (621619,213453) := by
  rw [← run_agrees FastC.next BB6.Agent46.secNext next_agrees]
  exact FastCChunks.prefix_147

theorem gate_terminal : BB6.Agent46.secNext (1,524260) = none := by
  rw [← next_agrees]
  decide

theorem original_mass_monotone : ∀ p q : Nat × Nat,
    BB6.Agent46.secNext p=some q → p.1+2*p.2 ≤ q.1+2*q.2 := by
  intro ⟨a,k⟩ ⟨x,y⟩ hh
  have hstrict := BB6.Agent46.section_mass_strict a k x y hh
  omega

/-- Once the blank orbit passes mass 1048524, no terminal section
    input below that mass can occur at any section index. -/
theorem all_terminal_lower_mass_unreachable
  (goal : Nat × Nat)
  (hterm : BB6.Agent46.secNext goal=none)
  (hmass : goal.1+2*goal.2 < 1048525) :
  ∀ n, ForwardMass.run BB6.Agent46.secNext (5,1) n ≠ some goal := by
  exact ForwardMass.terminal_overshoot BB6.Agent46.secNext
    (fun p : Nat × Nat => p.1+2*p.2) original_mass_monotone (5,1) goal
    (621619,213453) 150052 hterm source_trace (by omega)

theorem m8_low_gate_unreachable :
    ∀ n, ForwardMass.run BB6.Agent46.secNext (5,1) n ≠ some (1,524260) := by
  exact all_terminal_lower_mass_unreachable (1,524260) gate_terminal (by decide)

#print axioms fuel_agrees
#print axioms next_agrees
#print axioms source_trace
#print axioms gate_terminal
#print axioms all_terminal_lower_mass_unreachable
#print axioms m8_low_gate_unreachable
end BB6.Agent1Forward
