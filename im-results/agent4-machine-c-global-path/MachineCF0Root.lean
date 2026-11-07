import MachineCGlobalLift

namespace BB6Coverage

/-- A complete, unbounded physical-tape characterization of Machine C's
    original halted instruction. A statement about the actual blank run,
    not a verdict that the instruction is ever reached. -/
theorem machineC_halts_iff_reads_F0 :
    (∃ n, run machineC n blank = none) ↔
      ∃ n d, run machineC n blank = some d ∧
        readSlot d = machineCHaltSlot := by
  constructor
  · rintro ⟨n, hn⟩
    induction n with
    | zero => simp [run] at hn
    | succ n ih =>
      cases hprev : run machineC n blank with
      | none => exact ih hprev
      | some d =>
        have hstep : rawStep machineC d = none := by
          change (run machineC n blank).bind (rawStep machineC) = none at hn
          simpa [hprev] using hn
        cases hm : machineC (readSlot d) with
        | none =>
          exact ⟨n, d, hprev, (machineC_only_halt_row _).mp hm⟩
        | some move =>
          simp [rawStep, hm] at hstep
  · rintro ⟨n, d, hr, hs⟩
    exact ⟨n+1, halting_entry machineC blank d n hr
      ((machineC_only_halt_row _).mpr hs)⟩

/-- The all-time genuine blank run is infinite exactly when it never
    consults its sole original halting entry F/0. -/
theorem machineC_nonhalting_iff_never_reads_F0 :
    NeverHalts machineC ↔
      ¬ ∃ n d, run machineC n blank = some d ∧
        readSlot d = machineCHaltSlot := by
  constructor
  · intro hn ⟨n, d, hr, hs⟩
    exact (machineC_never_halts_avoids_F0 hn n d hr) hs
  · intro h n
    cases hr : run machineC n blank with
    | some c => simp [hr]
    | none =>
      have ⟨k, d, hd, hs⟩ :=
        machineC_halts_iff_reads_F0.mp ⟨n, hr⟩
      exact False.elim (h ⟨k, d, hd, hs⟩)

/-- Exact global 25-completion root obligation: the whole cylinder is
    nonhalting iff the original full physical run avoids F/0 forever. -/
theorem machineC_entire_cylinder_nonhalt_iff_F0_avoided :
    (∀ m, compatible (machineCPrefix 11) m → NeverHalts m) ↔
      ¬ ∃ n d, run machineC n blank = some d ∧
        readSlot d = machineCHaltSlot := by
  constructor
  · intro hall
    exact machineC_nonhalting_iff_never_reads_F0.mp
      (hall machineC (machineCPrefix_compatible 11))
  · intro h m hm
    exact machineC_nonhalt_lifts_to_entire_cylinder
      (machineC_nonhalting_iff_never_reads_F0.mpr h) m hm

/-- Given that n is the first physical F/0 consultation in the original
    run, all compatible machines share its entire prefix through n moves. -/
theorem machineC_first_F0_common_prefix
    (n : Nat) (d : Config)
    (hseen : run machineC n blank = some d)
    (hbefore : ∀ k, k < n → ∀ c,
      run machineC k blank = some c →
        readSlot c ≠ machineCHaltSlot)
    (m : Machine) (hm : compatible (machineCPrefix 11) m) :
    run m n blank = some d := by
  have hprefix : ∀ k, k < n → ∀ c,
      run machineC k blank = some c →
        machineCPrefix 11 (readSlot c) =
          some (machineC (readSlot c)) := by
    intro k hk c hc
    exact machineCPrefix_eleven_all_other_rows _
      (hbefore k hk c hc)
  have hagree := common_prefix_of_partial_table
    (machineCPrefix 11) machineC m blank n
    (machineCPrefix_compatible 11) hm hprefix
  rw [← hagree]
  exact hseen

/-- If F/0 is eventually consulted for the first time after n moves,
    assigning HALT at F/0 gives precisely the original n+1 step score
    for all extensions that agree on the other eleven instructions. -/
theorem machineC_first_F0_halt_completion
    (n : Nat) (d : Config)
    (hseen : run machineC n blank = some d)
    (hslot : readSlot d = machineCHaltSlot)
    (hbefore : ∀ k, k < n → ∀ c,
      run machineC k blank = some c →
        readSlot c ≠ machineCHaltSlot)
    (m : Machine) (hm : compatible (machineCPrefix 11) m)
    (hhalt : m machineCHaltSlot = none) :
    HaltsAfter m n := by
  have hrun := machineC_first_F0_common_prefix
    n d hseen hbefore m hm
  constructor
  · simp [hrun]
  · apply halting_entry m blank d n hrun
    simpa only [hslot] using hhalt

#print axioms machineC_halts_iff_reads_F0
#print axioms machineC_nonhalting_iff_never_reads_F0
#print axioms machineC_entire_cylinder_nonhalt_iff_F0_avoided
#print axioms machineC_first_F0_common_prefix
#print axioms machineC_first_F0_halt_completion

end BB6Coverage
