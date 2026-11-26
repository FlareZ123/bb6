import FirstHolePath
import Nov26Pair10

namespace BB6.Agent10Nov26
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent47WeightedHalt BB6.Agent8TNFPath
set_option maxHeartbeats 0
set_option maxRecDepth 100000

theorem leaf_eq_forget (m : Machine) : leaf m = forgetHaltRows m := rfl

/-- Canonical Raw140 parent (canonical-124 entry 103): A0=1RB, B0=1RC,
    C0=1RD, with the other nine rows unassigned. -/
def raw140Parent : PartialMachine := fun s =>
  if s = (0, false) then some (some ⟨true, true, 1⟩)
  else if s = (1, false) then some (some ⟨true, true, 2⟩)
  else if s = (2, false) then some (some ⟨true, true, 3⟩)
  else none

/-- Apply a finite list of ordinary transition refinements in order. -/
def refineMany (p : PartialMachine) : List (Slot × Transition) → PartialMachine
  | [] => p
  | (s, t) :: rest => refineMany (refine p s t) rest

/-- The eight ordinary assignments after Raw140's three-row prefix, in
    first-use order for the F262 source machine. -/
def n19_refinements : List (Slot × Transition) := [
  ((3, false), some ⟨false, false, 4⟩),
  ((4, true), some ⟨true, false, 0⟩),
  ((0, true), some ⟨false, false, 2⟩),
  ((2, true), some ⟨false, true, 5⟩),
  ((5, false), some ⟨true, false, 3⟩),
  ((4, false), some ⟨true, false, 1⟩),
  ((1, true), some ⟨false, true, 0⟩),
  ((5, true), some ⟨true, true, 0⟩)]

theorem n19_refinement : refineMany raw140Parent n19_refinements = leaf n19 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;>
    simp [refineMany, raw140Parent, n19_refinements, leaf, n19, literal]

/-- The eight ordinary assignments after Raw140's three-row prefix, in
    first-use order for the F068 source machine. -/
def n20_refinements : List (Slot × Transition) := [
  ((3, false), some ⟨false, false, 0⟩),
  ((0, true), some ⟨true, false, 0⟩),
  ((1, true), some ⟨false, false, 4⟩),
  ((4, true), some ⟨false, false, 4⟩),
  ((4, false), some ⟨true, false, 2⟩),
  ((3, true), some ⟨false, true, 3⟩),
  ((2, true), some ⟨false, false, 5⟩),
  ((5, true), some ⟨false, true, 4⟩)]

theorem n20_refinement : refineMany raw140Parent n20_refinements = leaf n20 := by
  funext slot
  rcases slot with ⟨q,b⟩
  fin_cases q <;> cases b <;>
    simp [refineMany, raw140Parent, n20_refinements, leaf, n20, literal]

/-- Exact first-hole schedule from the bulk manifest; times are ordinary
    moves from the blank start, with A0 at time zero omitted. -/
def n19_path : List (Nat × Slot) :=
  [(1, (1, false)), (2, (2, false)), (3, (3, false)),
   (4, (4, true)), (5, (0, true)), (6, (2, true)),
   (7, (5, false)), (9, (4, false)), (16, (1, true)),
   (59, (5, true))]

theorem n19_reachable : FirstHolePath (leaf n19) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n19 n19_path (by decide +kernel)

def n19_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n19) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n19 (by rfl) n19_never

theorem n19_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n19) :=
  (n19_weighted_cert B).toCover

#print axioms n19_refinement
#print axioms n19_reachable
#print axioms n19_weighted_cover

/-- Exact first-hole schedule from the bulk manifest; times are ordinary
    moves from the blank start, with A0 at time zero omitted. -/
def n20_path : List (Nat × Slot) :=
  [(1, (1, false)), (2, (2, false)), (3, (3, false)),
   (4, (0, true)), (8, (1, true)), (9, (4, true)),
   (10, (4, false)), (12, (3, true)), (71, (2, true)),
   (72, (5, true))]

theorem n20_reachable : FirstHolePath (leaf n20) 6 := by
  rw [leaf_eq_forget]
  exact checked_from_root n20 n20_path (by decide +kernel)

def n20_weighted_cert (B : Nat) : WeightedTNFCertificate B (leaf n20) 6 := by
  rw [leaf_eq_forget]
  exact forgetHaltRows_nonhaltCertificate B n20 (by rfl) n20_never

theorem n20_weighted_cover (B : Nat) : Cover (WeightedBound B) (leaf n20) :=
  (n20_weighted_cert B).toCover

#print axioms n20_refinement
#print axioms n20_reachable
#print axioms n20_weighted_cover

end BB6.Agent10Nov26
