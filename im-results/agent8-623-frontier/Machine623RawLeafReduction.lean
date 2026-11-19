import Machine623Frontier
import Machine623HaltCylinder

namespace BB6Coverage

/-- The eleven-row physical cylinder is contained in the original
    depth-four global open cylinder.  This is the exact subset relation
    needed to refine that 25^8 leaf rather than count an unrelated table
    family. -/
theorem machine623_depth11_refines_depth4 (m : Machine)
    (hm : compatible (machine623Prefix 11) m) :
    compatible (machine623Prefix 4) m := by
  have hfree : compatible
      (freeHaltCylinder machine623 machine623HaltSlot) m := by
    simpa [machine623_visited_eq_free_halt] using hm
  intro s t hs
  have hnot : s ≠ machine623HaltSlot := by
    intro heq
    subst s
    have hnone : machine623Prefix 4 machine623HaltSlot = none := by decide
    rw [hnone] at hs
    cases hs
  have hsource : machine623 s = t :=
    machine623Prefix_compatible 4 s t hs
  have hchild :
      freeHaltCylinder machine623 machine623HaltSlot s =
        some (machine623 s) := by
    simp [freeHaltCylinder, hnot]
  have hvalue := hfree s (machine623 s) hchild
  simpa [hsource] using hvalue

/-- Every ordinary completion of the final F/0 slot is a total machine:
    all other eleven entries are already fixed and ordinary.  Hence its
    blank run is infinite, without any runtime cutoff. -/
private theorem machine623_ordinary_f0_extension_never (mv : Move)
    (m : Machine)
    (hm : compatible
      (refine (machine623Prefix 11) machine623HaltSlot (some mv)) m) :
    NeverHalts m := by
  have hsplit :
      compatible (machine623Prefix 11) m ∧
        m machine623HaltSlot = some mv :=
    (compatible_refine_iff (machine623Prefix 11) m machine623HaltSlot
      machine623_halt_slot_unassigned (some mv)).mp hm
  rcases hsplit with ⟨hparent, hslot⟩
  rcases machine623_only_one_nontrivial_completion m hparent with hroot | hnever
  · subst m
    simp [machine623, machine623HaltSlot] at hslot
  · exact hnever

/-- Exact 25-way proof-carrying split of the eleven-row #623 cylinder.
    The 24 ordinary F/0 actions are certified all-time nonhalting leaves;
    the unique halting action is retained as an explicitly open singleton. -/
def machine623FinalSlotAudit :
    FrontierAudit (DecidedBelow 6) (machine623Prefix 11) :=
  .branch (machine623Prefix 11) machine623HaltSlot
    machine623_halt_slot_unassigned
    (fun t _ =>
      match t with
      | none =>
          .unresolved
            (refine (machine623Prefix 11) machine623HaltSlot none)
      | some mv =>
          .certified
            (refine (machine623Prefix 11) machine623HaltSlot (some mv))
            (.leaf _ (fun m hm =>
              Or.inl (machine623_ordinary_f0_extension_never mv m hm))))

theorem machine623FinalSlotAudit_exhaustive (m : Machine)
    (hm : compatible (machine623Prefix 11) m) :
    DecidedBelow 6 m ∨ machine623FinalSlotAudit.open m :=
  machine623FinalSlotAudit.exhaustive m hm

/-- A concise exact statement of the reduction: every completion of this
    cylinder is either all-time nonhalting or the original #623 table.  The
    proof splits directly on the unique free halt slot, avoiding a dependent
    open-predicate rewrite. -/
theorem machine623_depth11_only_root_remains (m : Machine)
    (hm : compatible (machine623Prefix 11) m) :
    NeverHalts m ∨ m = machine623 := by
  by_cases hhalt : m machine623HaltSlot = none
  · have hcompat :
        compatible (freeHaltCylinder machine623 machine623HaltSlot) m := by
      simpa [machine623_visited_eq_free_halt] using hm
    exact Or.inr
      (one_halt_freedom_nontrivial_singleton machine623 m
        machine623HaltSlot
        ((machine623_halts_only_at_F0 machine623HaltSlot).2 rfl)
        hcompat hhalt)
  · cases hvalue : m machine623HaltSlot with
    | none => exact False.elim (hhalt hvalue)
    | some mv =>
        exact Or.inl
          (machine623_ordinary_f0_extension_never mv m
            ((compatible_refine_iff (machine623Prefix 11) m
              machine623HaltSlot machine623_halt_slot_unassigned
              (some mv)).mpr ⟨hm, hvalue⟩))

/-- Exact terminal-cylinder accounting: 24 certified singleton tables,
    one open singleton table, and no omitted completion. -/
theorem machine623FinalSlotAudit_report :
    machine623FinalSlotAudit.report = (24, 1) := by
  decide

theorem machine623FinalSlotAudit_report_conserves :
    machine623FinalSlotAudit.report.1 +
      machine623FinalSlotAudit.report.2 = 25 := by
  rw [machine623FinalSlotAudit_report]
  decide

/-- Seven additional physically visited inputs refine the original 25^8
    depth-four cylinder to the 25-completion cylinder. -/
theorem machine623_depth11_mass_ratio :
    cylinderMass (machine623Prefix 4) =
      25^7 * cylinderMass (machine623Prefix 11) := by
  calc
    cylinderMass (machine623Prefix 4) = 25^8 :=
      machine623_first_four_mass
    _ = 25^7 * 25 := by decide
    _ = 25^7 * cylinderMass (machine623Prefix 11) :=
      congrArg (fun n => 25^7 * n) machine623_prefix_mass

#print axioms machine623_depth11_refines_depth4
#print axioms machine623_ordinary_f0_extension_never
#print axioms machine623FinalSlotAudit_exhaustive
#print axioms machine623FinalSlotAudit_open_iff_root
#print axioms machine623_depth11_only_root_remains
#print axioms machine623FinalSlotAudit_report
#print axioms machine623_depth11_mass_ratio

end BB6Coverage
