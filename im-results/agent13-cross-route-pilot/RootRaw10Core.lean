import CrossRouteHeldLeaf
import SideWitnessCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent13CrossRouteHeldLeaf109

open BB6Coverage
open BB6.Agent50TNFPilot

/-- The depth-one first-one residual at B0=1LC:
    A0 is fixed by firstOneCylinder and this refines B0 to 1LC. -/
def firstOneB0_1LC : PartialMachine :=
  BB6Coverage.refine BB6.Agent50TNFPilot.root
    (⟨1, by decide⟩, false)
    (some ⟨true, false, ⟨2, by decide⟩⟩)

/-- Decode the compact 0..23 transition code used in CrossRouteHeldLeaf
    into the standard Lean move record: 4*state + 2*write + direction. -/
def decodeMove (mv : BB6CrossRouteHeldLeaf.Move) : BB6Coverage.Move := by
  have hlt : mv.val < 24 := mv.isLt
  exact ⟨decide ((mv.val / 2) % 2 = 1),
    decide (mv.val % 2 = 1),
    ⟨mv.val / 4, by omega⟩⟩

/-- Translate the twelve-slot table used by the standalone partition proof
    into the same PartialMachine type as the 109 residual roster. -/
def toPartialMachine (p : BB6CrossRouteHeldLeaf.PartialTable) :
    BB6Coverage.PartialMachine :=
  fun slot =>
    match p ⟨2 * slot.1.val + (if slot.2 then 1 else 0), by
      have hq := slot.1.isLt
      cases slot.2 <;> simp <;> omega⟩ with
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

/-- Existing Agent 47 side-cycle certificates that refine this same 109
    parent. Each is a complete cylinder proof at weighted bound 7014. -/
def b0_1lcSideWitnesses : List BB6.Agent47SevenSideWitnesses.SideWitness :=
  BB6.Agent47SevenSideWitnesses.witnesses.filter fun w =>
    refinesMachineB (BB6.Agent50RootFrontier.unpackTable w.table) firstOneB0_1LC

theorem b0_1lcSideWitnesses_count : b0_1lcSideWitnesses.length = 65 := by decide

theorem b0_1lcSideWitnesses_safe :
    ∀ w ∈ b0_1lcSideWitnesses, ∀ m,
      BB6Coverage.compatible (BB6.Agent50RootFrontier.unpackTable w.table) m →
      BB6.Agent13BlankDelay.WeightedBound 7014 m := by
  intro w hw m hm
  have hmem : w ∈ BB6.Agent47SevenSideWitnesses.witnesses :=
    (List.mem_filter.mp hw).1
  have hcheck : BB6.Agent47SevenSideWitnesses.SideWitness.check w = true :=
    List.all_eq_true.mp BB6.Agent47SevenSideWitnesses.witnesses_checked w hmem
  exact w.sound hcheck m hm


end BB6.Agent13CrossRouteHeldLeaf109
