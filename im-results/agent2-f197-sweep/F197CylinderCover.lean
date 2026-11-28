import SelfTheorem
import CoverBridge

namespace F197.CoverBridge
open BB6Coverage (Machine compatible)

/-- The source-certified F197 self-embedding lifts to **every** completed
    original six-state Turing machine compatible with the literal table,
    even if its unassigned C1 row is an arbitrary halting or moving action.
    Initial head position is unrestricted as long as the full tape is related
    to the aligned positive cylinder. -/
theorem original_cylinder_live (m : Machine) (hm : compatible table m)
    (c : BB6Coverage.Config) (l : F197.Tape)
    (hl : l 0 = true)
    (hc : Related c (F197.Agent2Self.state 72 F197.Agent2Self.START l)) :
    ∀ t : Nat, BB6Coverage.run m t c ≠ none := by
  intro t
  have hn := F197.Agent2Self.self_nonhalt l hl t
  cases hs : F197.run t (F197.Agent2Self.state 72 F197.Agent2Self.START l) with
  | none => exact False.elim (hn hs)
  | some v =>
    obtain ⟨d,hd,_⟩ := run_related m hm t c _ v hc hs
    simp [hd]

#print axioms original_cylinder_live
end F197.CoverBridge
