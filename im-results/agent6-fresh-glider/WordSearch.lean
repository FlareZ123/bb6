import MarkerSearch
import WordMirror

namespace BB6Coverage

/-- Fully executable finite-word and earlier marker/fresh/halting rules.
    A true result is a concrete all-completions Cover leaf. -/
def wordDecisionOracle (p : PartialMachine)
    (bound rayLimit macroLimit entryLimit : Nat) : Bool :=
  markerDecisionOracle p bound rayLimit macroLimit entryLimit ||
    finiteWordBiOracle p entryLimit macroLimit

theorem wordDecisionOracle_sound (p : PartialMachine)
    (bound rayLimit macroLimit entryLimit : Nat)
    (h : wordDecisionOracle p bound rayLimit macroLimit entryLimit = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hm | hw
  · exact markerDecisionOracle_sound p bound rayLimit macroLimit entryLimit hm
  · exact finiteWordBiOracle_sound p entryLimit macroLimit bound hw

/-- Proof-carrying 25-way exhaustive branching. No unproved exclusions,
    and any false result means the corresponding subtree remains open. -/
def wordCoverSearch (p : PartialMachine)
    (bound rayLimit macroLimit entryLimit : Nat) : Nat → Bool
  | 0 => wordDecisionOracle p bound rayLimit macroLimit entryLimit
  | depth+1 =>
      if wordDecisionOracle p bound rayLimit macroLimit entryLimit = true
      then true
      else match findUnassigned p allSlots with
        | none => false
        | some slot =>
            choices.all (fun t => wordCoverSearch (refine p slot t)
              bound rayLimit macroLimit entryLimit depth)

theorem wordCoverSearch_sound
    (bound rayLimit macroLimit entryLimit depth : Nat) :
    ∀ p : PartialMachine,
      wordCoverSearch p bound rayLimit macroLimit entryLimit depth = true →
      Cover (DecidedBelow bound) p := by
  induction depth with
  | zero =>
      intro p h
      exact wordDecisionOracle_sound p bound rayLimit macroLimit entryLimit h
  | succ depth ih =>
      intro p h
      by_cases hleaf :
          wordDecisionOracle p bound rayLimit macroLimit entryLimit = true
      · exact wordDecisionOracle_sound p bound rayLimit macroLimit entryLimit hleaf
      · cases hslot : findUnassigned p allSlots with
        | none =>
            simp [wordCoverSearch, hleaf, hslot] at h
        | some slot =>
            have hchildren : choices.all
                (fun t => wordCoverSearch (refine p slot t)
                  bound rayLimit macroLimit entryLimit depth) = true := by
              simpa [wordCoverSearch, hleaf, hslot] using h
            have hs : p slot = none :=
              findUnassigned_sound p allSlots slot hslot
            apply Cover.branch p slot hs
            intro t ht
            exact ih (refine p slot t)
              ((List.all_eq_true.mp hchildren) t ht)

theorem twoMark_word_search_check :
    wordCoverSearch twoMarkWordPump 2 0 3 3 0 = true := by
  change wordDecisionOracle twoMarkWordPump 2 0 3 3 = true
  simp [wordDecisionOracle, finiteWordBiOracle, twoMark_word_oracle_accept]

theorem twoMark_word_search_leaf :
    Cover (DecidedBelow 2) twoMarkWordPump :=
  wordCoverSearch_sound 2 0 3 3 0 twoMarkWordPump
    twoMark_word_search_check

#print axioms wordDecisionOracle_sound
#print axioms wordCoverSearch_sound
#print axioms twoMark_word_search_leaf
end BB6Coverage
