import MacroSearch
import EntryMacroLeft

namespace BB6Coverage

/-- Certification combines finite halting, infinite directional rays,
    zero-only finite control, blank-ray macros from A, and macros entered
    after a bounded genuine blank-start prefix into any control state. -/
def entryDecisionOracle (p : PartialMachine)
    (bound rayLimit macroLimit entryLimit : Nat) : Bool :=
  macroDecisionOracle p bound rayLimit macroLimit ||
    finiteEntryMacroBiOracle p entryLimit macroLimit

theorem entryDecisionOracle_sound (p : PartialMachine)
    (bound rayLimit macroLimit entryLimit : Nat)
    (h : entryDecisionOracle p bound rayLimit macroLimit entryLimit = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hm | he
  · exact macroDecisionOracle_sound p bound rayLimit macroLimit hm
  · exact finiteEntryMacroBiOracle_sound p entryLimit macroLimit bound he

def entryMacroCoverSearch (p : PartialMachine)
    (bound rayLimit macroLimit entryLimit : Nat) : Nat → Bool
  | 0 => entryDecisionOracle p bound rayLimit macroLimit entryLimit
  | depth+1 =>
      if entryDecisionOracle p bound rayLimit macroLimit entryLimit = true
      then true
      else match findUnassigned p allSlots with
        | none => false
        | some slot =>
            choices.all (fun t => entryMacroCoverSearch (refine p slot t)
              bound rayLimit macroLimit entryLimit depth)

theorem entryMacroCoverSearch_sound
    (bound rayLimit macroLimit entryLimit depth : Nat) :
    ∀ p : PartialMachine,
      entryMacroCoverSearch p bound rayLimit macroLimit entryLimit depth = true →
      Cover (DecidedBelow bound) p := by
  induction depth with
  | zero =>
      intro p h
      exact entryDecisionOracle_sound p bound rayLimit macroLimit entryLimit h
  | succ depth ih =>
      intro p h
      by_cases hleaf :
          entryDecisionOracle p bound rayLimit macroLimit entryLimit = true
      · exact entryDecisionOracle_sound p bound rayLimit macroLimit entryLimit hleaf
      · cases hslot : findUnassigned p allSlots with
        | none =>
            simp [entryMacroCoverSearch, hleaf, hslot] at h
        | some slot =>
            have hchildren : choices.all
                (fun t => entryMacroCoverSearch (refine p slot t)
                  bound rayLimit macroLimit entryLimit depth) = true := by
              simpa [entryMacroCoverSearch, hleaf, hslot] using h
            have hs : p slot = none :=
              findUnassigned_sound p allSlots slot hslot
            apply Cover.branch p slot hs
            intro t ht
            exact ih (refine p slot t)
              ((List.all_eq_true.mp hchildren) t ht)

/-- Strictly more capable for this sparse machine than the old A-only
    macro decision with the same finite testing cutoffs. -/
theorem entryToB_old_reject :
    macroDecisionOracle entryToBExample 2 0 3 = false := by decide

theorem entryToB_new_accept :
    entryDecisionOracle entryToBExample 2 0 3 2 = true := by
  have he : finiteEntryMacroOracle entryToBExample 2 3 = true := by
    apply List.any_eq_true.mpr
    refine ⟨1, by decide, ?_⟩
    apply List.any_eq_true.mpr
    exact ⟨2, by decide, entryToB_check⟩
  simp [entryDecisionOracle, finiteEntryMacroBiOracle, he]

theorem entryToB_new_search_leaf :
    Cover (DecidedBelow 2) entryToBExample :=
  entryMacroCoverSearch_sound 2 0 3 2 0 entryToBExample
    (by simpa [entryMacroCoverSearch] using entryToB_new_accept)

#print axioms entryDecisionOracle_sound
#print axioms entryMacroCoverSearch_sound
#print axioms entryToB_new_search_leaf

theorem entryToBLeft_new_accept :
    entryDecisionOracle entryToBLeftExample 2 0 3 2 = true := by
  have hl : finiteEntryMacroLeftOracle entryToBLeftExample 2 3 = true := by
    apply List.any_eq_true.mpr
    refine ⟨1, by decide, ?_⟩
    apply List.any_eq_true.mpr
    exact ⟨2, by decide, entryToBLeft_check⟩
  simp [entryDecisionOracle, finiteEntryMacroBiOracle, hl]

theorem entryToBLeft_new_search_leaf :
    Cover (DecidedBelow 2) entryToBLeftExample :=
  entryMacroCoverSearch_sound 2 0 3 2 0 entryToBLeftExample
    (by simpa [entryMacroCoverSearch] using entryToBLeft_new_accept)

#print axioms entryToBLeft_new_search_leaf

end BB6Coverage
