import Raw120EasyCycles
import Raw120Late1341

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent13Raw120Composition
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent3Raw120
open BB6.Agent3Raw120EasyCycles

abbrev pLB : PartialMachine := refine p120 hole (some ⟨true,false,1⟩)

/-- The four remaining fixed rows of leaf 1341, extending the 1LB cylinder. -/
abbrev pLB1 : PartialMachine := refine pLB (1,true) (some ⟨false,false,5⟩)
abbrev pLB2 : PartialMachine := refine pLB1 (2,true) (some ⟨false,true,5⟩)
abbrev pLB3 : PartialMachine := refine pLB2 (5,false) (some ⟨false,true,0⟩)
abbrev pLB4 : PartialMachine := refine pLB3 (5,true) (some ⟨false,false,4⟩)

theorem leaf_eq : pLB4 = BB6.Agent13Raw120Late1341.table :=
  tableOK_sound _ _ (by decide)

theorem leaf_compatible_LB (m : Machine)
    (hm : compatible BB6.Agent13Raw120Late1341.table m) : compatible pLB m := by
  have h4 : compatible pLB4 m := by simpa only [leaf_eq] using hm
  have h3 : compatible pLB3 m := refine_preserves_compat _ _ _ _ (by decide) h4
  have h2 : compatible pLB2 m := refine_preserves_compat _ _ _ _ (by decide) h3
  have h1 : compatible pLB1 m := refine_preserves_compat _ _ _ _ (by decide) h2
  exact refine_preserves_compat _ _ _ _ (by decide) h1

theorem lb_lower (B : Nat)
    (h : ∀ m, compatible pLB m → WeightedBound B m) : 224707 ≤ B :=
  (BB6.Agent13Raw120Late1341.exact_weighted B).mp
    (fun m hm => h m (leaf_compatible_LB m hm))

theorem parent_lower (B : Nat)
    (h : ∀ m, compatible p120 m → WeightedBound B m) : 224707 ≤ B :=
  lb_lower B (fun m hm => h m (refine_preserves_compat _ _ _ _ (by decide) hm))

/-- Exactly fourteen ordinary children survive the translated-cycle cut. -/
def residualChoices : List Transition :=
  choices.filter (fun t => decide (t ≠ none ∧ t ∉ cycleChoices))

theorem residual_count : residualChoices.length = 14 := by decide
theorem residual_mass :
    ((residualChoices.map (fun t => cylinderMass (refine p120 hole t))).sum) =
      14 * 25^5 := by decide

theorem immediate_halt_checked : zipQueryOK 15 p120 9 hole = true := by decide

theorem immediate_halt_bound :
    ∀ m, compatible (refine p120 hole none) m → WeightedBound 15 m := by
  obtain ⟨hr,hh,hw⟩ := zipQueryOK_sound immediate_halt_checked
  cases hrun : knownRun p120 9 with
  | none => simp [hrun] at hr
  | some c =>
    have hs : readSlot c = hole := by simpa [hrun] using hr
    have h := first_hole_weighted_halt 15 p120 9 c (by decide) hrun
      (by simpa [hs] using hh)
      (by simpa [hs] using weightOK_sound p120 hole 9 15 hw)
    simpa [hs] using h

theorem lift_bound {A B : Nat} (hAB : A ≤ B) {m : Machine}
    (h : WeightedBound A m) : WeightedBound B m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hAB

/-- A single sound interface to consume the 14 nontrivial child covers.
    The ten cycles and immediate-halt cylinder are already discharged here. -/
theorem parent_cover (B : Nat) (hB : 15 ≤ B)
    (hLeaves : ∀ t ∈ residualChoices, Cover (WeightedBound B) (refine p120 hole t)) :
    Cover (WeightedBound B) p120 := by
  apply Cover.branch p120 hole (by decide)
  intro t ht
  by_cases hh : t = none
  · subst t
    exact Cover.leaf _ (fun m hm => lift_bound hB (immediate_halt_bound m hm))
  by_cases hc : t ∈ cycleChoices
  · exact Cover.leaf _ (fun m hm => lift_bound (Nat.zero_le B) (cycles_sound t hc m hm))
  · exact hLeaves t (List.mem_filter.mpr ⟨ht, by simp [hh,hc]⟩)

/-- Four nontrivial branches already have original-source accepted proofs.
    These are kept as explicit theorem inputs so no unrelated proof replay is
    needed to compile this composition interface. -/
def acceptedChoices : List Transition :=
  [some ⟨false,true,5⟩, some ⟨false,true,1⟩, some ⟨false,true,2⟩,
   some ⟨true,true,1⟩]

def remainingChoices : List Transition :=
  residualChoices.filter (fun t => decide (t ∉ acceptedChoices))

theorem accepted_count : acceptedChoices.length = 4 := by decide
theorem remaining_count : remainingChoices.length = 10 := by decide
theorem remaining_explicit : remainingChoices =
  [some ⟨false,false,0⟩, some ⟨false,true,0⟩, some ⟨true,false,0⟩,
   some ⟨true,true,0⟩, some ⟨false,false,1⟩, some ⟨true,false,1⟩,
   some ⟨true,true,2⟩, some ⟨false,false,5⟩, some ⟨true,false,5⟩,
   some ⟨true,true,5⟩] := by decide
theorem remaining_mass :
    ((remainingChoices.map (fun t => cylinderMass (refine p120 hole t))).sum) =
      10 * 25^5 := by decide

/-- Interface for the four accepted source certificates and all remaining
    ten ordinary children. Every accepted bound is lifted, never truncated. -/
theorem cover_from_ten (B : Nat) (hB : 14416 ≤ B)
    (hRF : ∀ m, compatible (refine p120 hole (some ⟨false,true,5⟩)) m → WeightedBound 14416 m)
    (hRB : ∀ m, compatible (refine p120 hole (some ⟨false,true,1⟩)) m → WeightedBound 223 m)
    (hRC : ∀ m, compatible (refine p120 hole (some ⟨false,true,2⟩)) m → WeightedBound 716 m)
    (hOneRB : ∀ m, compatible (refine p120 hole (some ⟨true,true,1⟩)) m → WeightedBound 749 m)
    (hLeaves : ∀ t ∈ remainingChoices, Cover (WeightedBound B) (refine p120 hole t)) :
    Cover (WeightedBound B) p120 := by
  apply parent_cover B (by omega)
  intro t ht
  by_cases hc : t ∈ acceptedChoices
  · simp only [acceptedChoices, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h <;> subst t
    · exact Cover.leaf _ (fun m hm => lift_bound hB (hRF m hm))
    · exact Cover.leaf _ (fun m hm => lift_bound (by omega) (hRB m hm))
    · exact Cover.leaf _ (fun m hm => lift_bound (by omega) (hRC m hm))
    · exact Cover.leaf _ (fun m hm => lift_bound (by omega) (hOneRB m hm))
  · exact hLeaves t (List.mem_filter.mpr ⟨ht, by simp [hc]⟩)

/-- If all fourteen nontrivial children close at 224707, this is the exact
    weighted maximum for the parent, with a kernel-checked attaining leaf. -/
theorem exact_if_children
    (hLeaves : ∀ t ∈ residualChoices, Cover (WeightedBound 224707) (refine p120 hole t))
    (B : Nat) : (∀ m, compatible p120 m → WeightedBound B m) ↔ 224707 ≤ B := by
  constructor
  · exact parent_lower B
  · intro hB m hm
    exact lift_bound hB ((parent_cover 224707 (by decide) hLeaves).sound m hm)

#print axioms leaf_eq
#print axioms parent_lower
#print axioms residual_count
#print axioms residual_mass
#print axioms parent_cover
#print axioms remaining_count
#print axioms remaining_explicit
#print axioms remaining_mass
#print axioms cover_from_ten
#print axioms exact_if_children
end BB6.Agent13Raw120Composition
