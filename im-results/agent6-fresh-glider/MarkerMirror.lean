import MarkerOracle
import Lean.Elab.Tactic.Omega

namespace BB6Coverage

/-- Reflect every assigned move of a sparse table while retaining all
    genuinely unassigned slots and explicitly assigned halts. -/
def reflectPartialMarker (p : PartialMachine) : PartialMachine :=
  fun s => (p s).map (Option.map reflectMove)

theorem reflectPartialMarker_involution (p : PartialMachine) :
    reflectPartialMarker (reflectPartialMarker p) = p := by
  funext s
  cases hs : p s with
  | none => simp [reflectPartialMarker, hs]
  | some t =>
      cases t with
      | none => simp [reflectPartialMarker, hs]
      | some mv => simp [reflectPartialMarker, hs, reflectMove_involution]

theorem compatible_reflectPartialMarker (p : PartialMachine) (m : Machine)
    (h : compatible p m) :
    compatible (reflectPartialMarker p) (reflectTable m) := by
  intro s t hs
  cases hp : p s with
  | none =>
      simp [reflectPartialMarker, hp] at hs
  | some v =>
      have hm : m s = v := h s v hp
      have ht : Option.map reflectMove v = t := by
        simpa [reflectPartialMarker, hp] using hs
      simp [reflectTable, hm, ht]

theorem decidedBelow_of_reflected (m : Machine) (bound : Nat)
    (h : DecidedBelow bound (reflectTable m)) : DecidedBelow bound m := by
  rcases h with hnever | ⟨n, hb, hh⟩
  · left
    intro t
    have heq : run (reflectTable m) t blank =
        (run m t blank).map mirrorConfig := by
      simpa only [mirror_blank] using mirror_run m blank t
    have hsome := hnever t
    rw [heq] at hsome
    cases hm : run m t blank with
    | none => simp [hm] at hsome
    | some c => simp [hm]
  · right
    exact ⟨n, hb, (reflect_halts_iff m n).mp hh⟩

/-- Source-authentic reflection transports an all-completion certificate
    for a reflected partial table back to the original partial table. -/
theorem reflectPartialMarker_cover (p : PartialMachine) (bound : Nat)
    (h : Cover (DecidedBelow bound) (reflectPartialMarker p)) :
    Cover (DecidedBelow bound) p := by
  apply Cover.leaf
  intro m hm
  exact decidedBelow_of_reflected m bound
    (h.sound (reflectTable m) (compatible_reflectPartialMarker p m hm))

/-- Both right- and left-facing travelling marker fronts are accepted
    by the same finite checker, using literal left/right symmetry. -/
def finiteMarkerBiOracle (p : PartialMachine)
    (entryLimit macroLimit : Nat) : Bool :=
  finiteMarkerEntryOracle p entryLimit macroLimit ||
    finiteMarkerEntryOracle (reflectPartialMarker p) entryLimit macroLimit

theorem finiteMarkerBiOracle_sound (p : PartialMachine)
    (entryLimit macroLimit bound : Nat)
    (h : finiteMarkerBiOracle p entryLimit macroLimit = true) :
    Cover (DecidedBelow bound) p := by
  rcases (Bool.or_eq_true _ _).mp h with hr | hl
  · exact finiteMarkerEntryOracle_sound p entryLimit macroLimit bound hr
  · exact reflectPartialMarker_cover p bound
      (finiteMarkerEntryOracle_sound (reflectPartialMarker p)
        entryLimit macroLimit bound hl)

theorem reflected_marker_accept :
    finiteMarkerBiOracle (reflectPartialMarker markedTailPump) 3 3 = true := by
  simp [finiteMarkerBiOracle, reflectPartialMarker_involution,
    marked_entry_oracle_accept]

theorem reflected_marker_cover (bound : Nat) :
    Cover (DecidedBelow bound) (reflectPartialMarker markedTailPump) :=
  finiteMarkerBiOracle_sound (reflectPartialMarker markedTailPump) 3 3 bound
    reflected_marker_accept

#print axioms reflectPartialMarker_involution
#print axioms compatible_reflectPartialMarker
#print axioms decidedBelow_of_reflected
#print axioms finiteMarkerBiOracle_sound
#print axioms reflected_marker_cover
end BB6Coverage
