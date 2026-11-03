import WordOracle
import MarkerMirror

namespace BB6Coverage

/-- Source-authentic reflection of a finite-word ray certificate supplies
    the symmetric left-moving word pump, retaining actual blank-root state. -/
def finiteWordBiOracle (p : PartialMachine)
    (entryLimit macroLimit : Nat) : Bool :=
  finiteWordEntryOracle p entryLimit macroLimit ||
    finiteWordEntryOracle (reflectPartialMarker p) entryLimit macroLimit

theorem finiteWordBiOracle_sound (p : PartialMachine)
    (entryLimit macroLimit bound : Nat)
    (h : finiteWordBiOracle p entryLimit macroLimit = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hr | hl
  · exact finiteWordEntryOracle_sound p entryLimit macroLimit bound hr
  · exact reflectPartialMarker_cover p bound
      (finiteWordEntryOracle_sound (reflectPartialMarker p)
        entryLimit macroLimit bound hl)

theorem twoMark_word_bi_accept :
    finiteWordBiOracle twoMarkWordPump 3 3 = true := by
  simp [finiteWordBiOracle, twoMark_word_oracle_accept]

theorem twoMark_word_bi_leaf (bound : Nat) :
    Cover (DecidedBelow bound) twoMarkWordPump :=
  finiteWordBiOracle_sound twoMarkWordPump 3 3 bound
    twoMark_word_bi_accept

theorem twoMark_word_mirror_accept :
    finiteWordBiOracle (reflectPartialMarker twoMarkWordPump) 3 3 = true := by
  simp [finiteWordBiOracle, reflectPartialMarker_involution,
    twoMark_word_oracle_accept]

theorem twoMark_word_mirror_leaf (bound : Nat) :
    Cover (DecidedBelow bound) (reflectPartialMarker twoMarkWordPump) :=
  finiteWordBiOracle_sound (reflectPartialMarker twoMarkWordPump) 3 3 bound
    twoMark_word_mirror_accept

#print axioms finiteWordBiOracle_sound
#print axioms twoMark_word_mirror_leaf
end BB6Coverage
