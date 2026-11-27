import HardRootParents

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent20NeedleRaw10
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath
open BB6.Agent19HardRoot

/-- The literal original Space Needle RLE
    1RB1LA_1LC0RE_1LF1LD_0RB0LA_1RC1RE_HHH0LD.
    F0 is the only halt. This is a source-identification/routing lemma;
    no nonhalting result is assumed. -/
def spaceNeedle : Machine :=
  literal [
    some ⟨true,true,1⟩, some ⟨true,false,0⟩,
    some ⟨true,false,2⟩, some ⟨false,true,4⟩,
    some ⟨true,false,5⟩, some ⟨true,false,3⟩,
    some ⟨false,true,1⟩, some ⟨false,false,0⟩,
    some ⟨true,true,2⟩, some ⟨true,true,4⟩,
    none, some ⟨false,false,3⟩
  ]

/-- Original blank-tape first-use trace through all eleven ordinary rows.
    The last ordinary row A1 is encountered at step 19. F0 remains open. -/
def schedule : List (Nat × Slot) := [
  (1,(1,false)), (2,(2,true)), (3,(3,false)),
  (4,(1,true)), (5,(4,true)), (6,(4,false)),
  (7,(2,false)), (8,(5,true)), (9,(3,true)),
  (19,(0,true))
]

theorem first_hole_path :
    FirstHolePath (forgetHaltRows spaceNeedle) 6 :=
  checked_from_root _ schedule (by decide)

/-- Space Needle lies in the authentic canonical Raw10 parent cylinder. -/
theorem parent : compatible p10 spaceNeedle :=
  (parentCheck_iff _ _).mp (by decide)

/-- All 25 ways of filling F0 stay inside Raw10. -/
theorem leaf_parent :
    ∀ m, compatible (forgetHaltRows spaceNeedle) m → compatible p10 m :=
  leaf_extends_parent _ _ (ordinaryParentCheck_sound _ (by decide)) parent

/-- The single unresolved source-level weighted obligation for the
    25-completion leaf; 24 ordinary replacements are nonhalting. -/
theorem cover_iff (B : Nat) :
    Cover (WeightedBound B) (forgetHaltRows spaceNeedle) ↔
      ∀ k, HaltsAfter spaceNeedle k → k + 1 ≤ B :=
  cover_iff_of_checks spaceNeedle (5,false) [0] 0 B
    (by decide) (by decide) (by decide) (by simp)

#print axioms first_hole_path
#print axioms parent
#print axioms leaf_parent
#print axioms cover_iff

end BB6.Agent20NeedleRaw10
