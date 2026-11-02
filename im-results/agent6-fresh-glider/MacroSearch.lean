import MacroOracle
import SparsePruneSearch

namespace BB6Coverage

/-- A proof-producing generalization of the existing finite decision oracle,
    adding bidirectional finite blank-ray macro repetition. -/
def macroDecisionOracle (p : PartialMachine)
    (bound rayLimit macroLimit : Nat) : Bool :=
  finiteDecisionOracle p bound rayLimit || finiteMacroOracle p macroLimit

theorem macroDecisionOracle_sound (p : PartialMachine)
    (bound rayLimit macroLimit : Nat)
    (h : macroDecisionOracle p bound rayLimit macroLimit = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hd | hm
  · exact finiteDecisionOracle_sound p bound rayLimit hd
  · exact finiteMacroOracle_sound p macroLimit bound hm

/-- Fully exhaustive 25-way sparse branching with the additional
    macro leaf. A false output is inconclusive. -/
def macroCoverSearch (p : PartialMachine)
    (bound rayLimit macroLimit : Nat) : Nat → Bool
  | 0 => macroDecisionOracle p bound rayLimit macroLimit
  | depth+1 =>
      if macroDecisionOracle p bound rayLimit macroLimit = true then true else
        match findUnassigned p allSlots with
        | none => false
        | some slot =>
            choices.all (fun t =>
              macroCoverSearch (refine p slot t) bound rayLimit macroLimit depth)

theorem macroCoverSearch_sound (bound rayLimit macroLimit depth : Nat) :
    ∀ p : PartialMachine,
      macroCoverSearch p bound rayLimit macroLimit depth = true →
      Cover (DecidedBelow bound) p := by
  induction depth with
  | zero =>
      intro p h
      exact macroDecisionOracle_sound p bound rayLimit macroLimit h
  | succ depth ih =>
      intro p h
      by_cases hleaf : macroDecisionOracle p bound rayLimit macroLimit = true
      · exact macroDecisionOracle_sound p bound rayLimit macroLimit hleaf
      · cases hslot : findUnassigned p allSlots with
        | none =>
            simp [macroCoverSearch, hleaf, hslot] at h
        | some slot =>
            have hchildren : choices.all
                (fun t => macroCoverSearch (refine p slot t)
                  bound rayLimit macroLimit depth) = true := by
              simpa [macroCoverSearch, hleaf, hslot] using h
            have hs : p slot = none :=
              findUnassigned_sound p allSlots slot hslot
            apply Cover.branch p slot hs
            intro t ht
            exact ih (refine p slot t) ((List.all_eq_true.mp hchildren) t ht)

/-- A five-slot family beyond the previous fixed three- and four-step
    glider catalogue is recognized by the generic macro-powered search. -/
theorem five_step_macro_decision :
    macroDecisionOracle fiveStepMacroTable 2 0 5 = true := by
  have hright : finiteMacroRightOracle fiveStepMacroTable 5 = true := by
    apply List.any_eq_true.mpr
    refine ⟨4, by decide, ?_⟩
    apply List.any_eq_true.mpr
    exact ⟨0, by decide, five_step_macro_check⟩
  simp [macroDecisionOracle, finiteMacroOracle, hright]

theorem five_step_macro_search :
    macroCoverSearch fiveStepMacroTable 2 0 5 0 = true := by
  simpa [macroCoverSearch] using five_step_macro_decision

theorem five_step_macro_search_leaf :
    Cover (DecidedBelow 2) fiveStepMacroTable :=
  macroCoverSearch_sound 2 0 5 0 fiveStepMacroTable five_step_macro_search

#print axioms macroDecisionOracle_sound
#print axioms macroCoverSearch_sound
#print axioms five_step_macro_search_leaf

end BB6Coverage
