import Raw120Late
import FrontierMass

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent3Raw120EasyCycles
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent3Raw120

abbrev hole : Slot := (4,false)

theorem parent_nohalt : weightedTNFNoAssignedHalt p120 :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (pathEnd_nohalt root 2 (path.take 4) firstOneCylinder_no_assigned_halt)

/-- The cycle checker certifies every completion of the indicated child,
    independently of its five still-unassigned transition slots. -/
theorem cycleBound (mv : Move) (e k : Nat) (r : Bool) (b : Int)
    (h : zipCheck 0 (refine p120 hole (some mv)) (.cycle e k r b) = true) :
    ∀ m, compatible (refine p120 hole (some mv)) m → WeightedBound 0 m :=
  (certifiedZip 0 (refine p120 hole (some mv)) (.cycle e k r b)
    (refine_preserves_firstOne p120 hole (some mv) (by decide) (by decide))
    (weightedTNFNoAssignedHalt_refine p120 hole mv parent_nohalt) h).sound

def cycleChoices : List Transition :=
  [some ⟨false,false,2⟩, some ⟨false,false,3⟩, some ⟨false,false,4⟩, some ⟨false,true,3⟩, some ⟨false,true,4⟩, some ⟨true,false,2⟩, some ⟨true,false,3⟩, some ⟨true,false,4⟩, some ⟨true,true,3⟩, some ⟨true,true,4⟩]

theorem cycleChoices_length : cycleChoices.length = 10 := by decide

theorem cycleChoices_nodup : cycleChoices.Nodup := by decide

theorem cycleChoices_mass :
    ((cycleChoices.map (fun t => cylinderMass (refine p120 hole t))).sum) =
      10 * 25^5 := by decide

/-- All ten translated-cycle cylinders have weighted bound zero.
    Each application checks the complete finite trace and the half-line
    relation that permits unlimited repetition. -/
theorem cycles_sound (t : Transition) (ht : t ∈ cycleChoices) :
    ∀ m, compatible (refine p120 hole t) m → WeightedBound 0 m := by
  simp only [cycleChoices, List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9
  all_goals subst t
  · exact cycleBound ⟨false,false,2⟩ 11 1 false (-1) (by decide)
  · exact cycleBound ⟨false,false,3⟩ 10 1 false (-2) (by decide)
  · exact cycleBound ⟨false,false,4⟩ 9 1 false (-1) (by decide)
  · exact cycleBound ⟨false,true,3⟩ 7 4 true (-1) (by decide)
  · exact cycleBound ⟨false,true,4⟩ 8 2 true (-1) (by decide)
  · exact cycleBound ⟨true,false,2⟩ 7 5 false (1) (by decide)
  · exact cycleBound ⟨true,false,3⟩ 10 1 false (-2) (by decide)
  · exact cycleBound ⟨true,false,4⟩ 9 1 false (-1) (by decide)
  · exact cycleBound ⟨true,true,3⟩ 5 5 false (2) (by decide)
  · exact cycleBound ⟨true,true,4⟩ 7 3 false (1) (by decide)

#print axioms cycles_sound
#print axioms cycleChoices_mass
end BB6.Agent3Raw120EasyCycles
