import MarkerMirror
import EntryMacroSearch

namespace BB6Coverage

/-- A finite canonical decision combines the established sparse proof rules
    with a signed-head-checked, translated moving-marker certificate. -/
def markerDecisionOracle (p : PartialMachine)
    (bound rayLimit macroLimit entryLimit : Nat) : Bool :=
  entryDecisionOracle p bound rayLimit macroLimit entryLimit ||
    finiteMarkerBiOracle p entryLimit macroLimit

theorem markerDecisionOracle_sound (p : PartialMachine)
    (bound rayLimit macroLimit entryLimit : Nat)
    (h : markerDecisionOracle p bound rayLimit macroLimit entryLimit = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with he | hm
  · exact entryDecisionOracle_sound p bound rayLimit macroLimit entryLimit he
  · exact finiteMarkerBiOracle_sound p entryLimit macroLimit bound hm

/-- All 25 possible transition actions remain represented in a successful
    sparse search. Returning false leaves the branch open, and makes no
    nonhalting or runtime assertion. -/
def markerCoverSearch (p : PartialMachine)
    (bound rayLimit macroLimit entryLimit : Nat) : Nat → Bool
  | 0 => markerDecisionOracle p bound rayLimit macroLimit entryLimit
  | depth+1 =>
      if markerDecisionOracle p bound rayLimit macroLimit entryLimit = true
      then true
      else match findUnassigned p allSlots with
        | none => false
        | some slot =>
            choices.all (fun t => markerCoverSearch (refine p slot t)
              bound rayLimit macroLimit entryLimit depth)

theorem markerCoverSearch_sound
    (bound rayLimit macroLimit entryLimit depth : Nat) :
    ∀ p : PartialMachine,
      markerCoverSearch p bound rayLimit macroLimit entryLimit depth = true →
      Cover (DecidedBelow bound) p := by
  induction depth with
  | zero =>
      intro p h
      exact markerDecisionOracle_sound p bound rayLimit macroLimit entryLimit h
  | succ depth ih =>
      intro p h
      by_cases hleaf :
          markerDecisionOracle p bound rayLimit macroLimit entryLimit = true
      · exact markerDecisionOracle_sound p bound rayLimit macroLimit entryLimit hleaf
      · cases hslot : findUnassigned p allSlots with
        | none =>
            simp [markerCoverSearch, hleaf, hslot] at h
        | some slot =>
            have hchildren : choices.all
                (fun t => markerCoverSearch (refine p slot t)
                  bound rayLimit macroLimit entryLimit depth) = true := by
              simpa [markerCoverSearch, hleaf, hslot] using h
            have hs : p slot = none :=
              findUnassigned_sound p allSlots slot hslot
            apply Cover.branch p slot hs
            intro t ht
            exact ih (refine p slot t)
              ((List.all_eq_true.mp hchildren) t ht)

/-- The marker oracle certifies the sparse moving-marker example as a genuine
    universal leaf even if its unspecified transitions are arbitrary. -/
theorem marked_search_check :
    markerCoverSearch markedTailPump 2 0 3 3 0 = true := by
  change markerDecisionOracle markedTailPump 2 0 3 3 = true
  simp [markerDecisionOracle, marked_entry_oracle_accept]

theorem marked_search_leaf :
    Cover (DecidedBelow 2) markedTailPump :=
  markerCoverSearch_sound 2 0 3 3 0 markedTailPump marked_search_check

#print axioms markerDecisionOracle_sound
#print axioms markerCoverSearch_sound
#print axioms marked_search_leaf

end BB6Coverage
