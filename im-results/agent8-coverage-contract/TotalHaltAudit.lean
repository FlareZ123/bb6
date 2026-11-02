import HaltSlotFreedom

namespace BB6Coverage

/-- A raw machine without a halting transition has an infinite run from
any start, in particular from the blank A start. -/
theorem total_never (m : Machine)
    (htotal : ∀ s, m s ≠ none) : NeverHalts m := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      cases hc : run m n blank with
      | none => simp [hc] at ih
      | some c =>
          have ht := htotal (readSlot c)
          cases hm : m (readSlot c) with
          | none => exact False.elim (ht hm)
          | some t => simp [run, hc, rawStep, hm]

/-- When a known nonhalting machine has precisely one halt instruction,
all 24 non-halt replacements of that instruction are syntactically
nonhalting, independently of the expensive source nonhalting proof. -/
theorem one_halt_freedom_trivial_part (source full : Machine) (halt : Slot)
    (honly : ∀ s, s ≠ halt → source s ≠ none)
    (hcompat : compatible (freeHaltCylinder source halt) full)
    (hnew : full halt ≠ none) : NeverHalts full := by
  apply total_never full
  intro s
  by_cases hs : s = halt
  · simpa [hs] using hnew
  · have h : freeHaltCylinder source halt s = some (source s) := by
      simp [freeHaltCylinder, hs]
    rw [hcompat s (source s) h]
    exact honly s hs

/-- For one-halt source machines, every cylinder extension that retains
the halt instruction is literally the original source table. -/
theorem one_halt_freedom_nontrivial_singleton (source full : Machine) (halt : Slot)
    (horig : source halt = none)
    (hcompat : compatible (freeHaltCylinder source halt) full)
    (hnew : full halt = none) : full = source := by
  funext s
  by_cases hs : s = halt
  · subst s
    exact hnew.trans horig.symm
  · have h : freeHaltCylinder source halt s = some (source s) := by
      simp [freeHaltCylinder, hs]
    exact hcompat s (source s) h

#print axioms total_never
#print axioms one_halt_freedom_trivial_part
#print axioms one_halt_freedom_nontrivial_singleton
end BB6Coverage
