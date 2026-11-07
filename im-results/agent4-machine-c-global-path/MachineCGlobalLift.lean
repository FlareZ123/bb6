import MachineCElevenFrontier

namespace BB6Coverage

/-- The only missing/halting instruction in the canonical Machine C raw
    table is F/0, the single unassigned entry of its 11-row sparse
    cylinder. -/
def machineCHaltSlot : Slot := (⟨5, by decide⟩, false)

theorem machineC_only_halt_row :
    ∀ s : Slot, machineC s = none ↔ s = machineCHaltSlot := by decide

theorem machineCPrefix_eleven_all_other_rows :
    ∀ s : Slot, s ≠ machineCHaltSlot →
      machineCPrefix 11 s = some (machineC s) := by decide

/-- Every time-step of a hypothetical infinite canonical Machine C run
    must avoid F/0. This is deliberately a conditional theorem:
    source-verified Machine C nonhalting is not yet known. -/
theorem machineC_never_halts_avoids_F0
    (hnever : NeverHalts machineC) (n : Nat) (d : Config)
    (hseen : run machineC n blank = some d) :
    readSlot d ≠ machineCHaltSlot := by
  intro heq
  have hhalt : machineC (readSlot d) = none :=
    (machineC_only_halt_row (readSlot d)).mpr heq
  have hnext := halting_entry machineC blank d n hseen hhalt
  have hsome := hnever (n+1)
  simp [hnext] at hsome

/-- **Root-to-global certificate bridge.** An all-time proof that the
    original canonical Machine C does not halt would *automatically*
    certify every one of the 25 total machines extending its first
    11 consulted rows. The genuine halting row F/0 may be set to any of
    the 25 outcomes; it is never consulted along that hypothesized
    original blank execution. This requires a real NeverHalts witness,
    which no current Machine C research supplies. -/
theorem machineC_nonhalt_lifts_to_entire_cylinder
    (hnever : NeverHalts machineC)
    (m : Machine) (hm : compatible (machineCPrefix 11) m) :
    NeverHalts m := by
  intro n
  have huniform : run machineC n blank = run m n blank := by
    apply common_prefix_of_partial_table (machineCPrefix 11)
      machineC m blank n (machineCPrefix_compatible 11) hm
    intro k hk d hd
    exact machineCPrefix_eleven_all_other_rows
      (readSlot d) (machineC_never_halts_avoids_F0 hnever k d hd)
  simpa only [huniform] using hnever n

theorem machineC_nonhalt_cover_leaf (hnever : NeverHalts machineC)
    (bound : Nat) :
    Cover (DecidedBelow bound) (machineCPrefix 11) := by
  apply Cover.leaf
  intro m hm
  left
  exact machineC_nonhalt_lifts_to_entire_cylinder hnever m hm

#print axioms machineC_only_halt_row
#print axioms machineCPrefix_eleven_all_other_rows
#print axioms machineC_never_halts_avoids_F0
#print axioms machineC_nonhalt_lifts_to_entire_cylinder
#print axioms machineC_nonhalt_cover_leaf

end BB6Coverage
