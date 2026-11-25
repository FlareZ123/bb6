import Combined109Roster
import CrossRouteHeldLeaf

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13CrossRouteHeldLeaf109

open BB6Coverage
open BB6.Agent50TNFPilot
open BB6.Agent31FourHoleRoster
open BB6.Agent47Combined109

/-- The depth-one first-one residual at B0=1LC:
    A0 is fixed by firstOneCylinder and this refines B0 to 1LC. -/
def firstOneB0_1LC : PartialMachine :=
  BB6Coverage.refine BB6.Agent50TNFPilot.root
    (⟨1, by decide⟩, false)
    (some ⟨true, false, ⟨2, by decide⟩⟩)

/-- This parent is not one of the fifteen already accepted whole-cylinder
    cuts (raw 66/70/80 and raw 86/87/88/91/92/93/97/98/100/101/102/104). -/
theorem firstOneB0_1LC_not_covered :
    BB6.Agent47Combined109.covered firstOneB0_1LC = false := by decide

/-- The B0=1LC parent is an actual member of the 109 residual roster,
    not an unrelated first-one branch. -/
theorem firstOneB0_1LC_in_reducedRoster :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster,
      BB6.Agent31FourHoleRoster.sameTable e.2 firstOneB0_1LC = true := by decide

/-- The roster entry is exactly this parent table, not merely a compatible
    intersection with it. -/
theorem firstOneB0_1LC_exact_member :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster,
      e.2 = firstOneB0_1LC := by
  obtain ⟨e, he, hsame⟩ := firstOneB0_1LC_in_reducedRoster
  exact ⟨e, he, BB6.Agent31FourHoleRoster.sameTable_sound hsame⟩

/-- Decode the compact 0..23 transition code used in CrossRouteHeldLeaf
    into the standard Lean move record: 4*state + 2*write + direction. -/
def decodeMove (mv : BB6CrossRouteHeldLeaf.Move) : BB6Coverage.Move :=
  { write := decide ((mv.val / 2) % 2 = 1)
    right := decide (mv.val % 2 = 1)
    next := ⟨mv.val / 4, by omega⟩ }

/-- Translate the twelve-slot table used by the standalone partition proof
    into the same PartialMachine type as the 109 residual roster. -/
def toPartialMachine (p : BB6CrossRouteHeldLeaf.PartialTable) :
    BB6Coverage.PartialMachine :=
  fun slot =>
    match p ⟨2 * slot.1.val + (if slot.2 then 1 else 0), by omega⟩ with
    | none => none
    | some none => some none
    | some (some mv) => some (some (decodeMove mv))

def refinesMachine (child parent : BB6Coverage.PartialMachine) : Prop :=
  ∀ slot, parent slot = none ∨ child slot = parent slot

def refinesMachineB (child parent : BB6Coverage.PartialMachine) : Bool :=
  (List.finRange 6).all fun q =>
    [false, true].all fun b =>
      decide (parent (q,b) = none ∨ child (q,b) = parent (q,b))

theorem refinesMachineB_sound {child parent : BB6Coverage.PartialMachine}
    (h : refinesMachineB child parent = true) : refinesMachine child parent := by
  intro slot
  rcases slot with ⟨q,b⟩
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  have hb : b ∈ [false, true] := by cases b <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp hq b hb)

/-- The parent table in the 109 roster is exactly the parent used by the
    source-held leaf's finite-slot partition proof. -/
theorem rootResidual_matches_109_parent :
    BB6.Agent31FourHoleRoster.sameTable
      (toPartialMachine BB6CrossRouteHeldLeaf.rootResidual)
      firstOneB0_1LC = true := by decide

/-- The source-held leaf is a strict refinement of the actual 109 parent,
    in the roster's own PartialMachine encoding. -/
theorem heldTable_refines_109_parent :
    refinesMachine
      (toPartialMachine BB6CrossRouteHeldLeaf.heldTable)
      firstOneB0_1LC := by
  apply refinesMachineB_sound
  decide

/-- The parent identified by the source proof is the exact table in the
    109 roster; no text-only or hash-only matching is used. -/
theorem sourceHeldParent_is_exact_109_member :
    ∃ e ∈ BB6.Agent47Combined109.reducedRoster,
      BB6.Agent31FourHoleRoster.sameTable
        e.2 (toPartialMachine BB6CrossRouteHeldLeaf.rootResidual) = true := by
  obtain ⟨e, he, hsame⟩ := firstOneB0_1LC_in_reducedRoster
  have hparent :
      toPartialMachine BB6CrossRouteHeldLeaf.rootResidual = firstOneB0_1LC :=
    BB6.Agent31FourHoleRoster.sameTable_sound rootResidual_matches_109_parent
  refine ⟨e, he, ?_⟩
  rw [hparent]
  exact hsame

#print axioms firstOneB0_1LC_not_covered
#print axioms firstOneB0_1LC_in_reducedRoster
#print axioms firstOneB0_1LC_exact_member
#print axioms rootResidual_matches_109_parent
#print axioms heldTable_refines_109_parent
#print axioms sourceHeldParent_is_exact_109_member

end BB6.Agent13CrossRouteHeldLeaf109
