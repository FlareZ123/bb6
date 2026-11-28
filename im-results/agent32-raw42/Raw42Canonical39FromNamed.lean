import Raw42GlobalBridge
import Raw42Canonical39Conditional

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent17Raw42Canonical39FromNamed
open BB6Coverage
open BB6.Agent32Raw42

abbrev p42 : PartialMachine := BB6.Agent17Raw42Canonical39Conditional.p42
noncomputable abbrev roster38 :=
  BB6.Agent17Raw42Canonical39Conditional.roster38

theorem literal_eq_p42 :
    BB6.Agent17Raw42GlobalBridge.literal = p42 := by
  apply tableOK_sound
  decide

theorem cover_from_named_at_global
    (h0LA : Cover (WeightedBound 100006) (child ⟨false,false,0⟩))
    (h0RA : Cover (WeightedBound 1006)   (child ⟨false,true,0⟩))
    (h1LA : Cover (WeightedBound 100006) (child ⟨true,false,0⟩))
    (h1RA : Cover (WeightedBound 100006) (child ⟨true,true,0⟩))
    (h0RB : Cover (WeightedBound 1006)   (child ⟨false,true,1⟩))
    (h1LB : Cover (WeightedBound 100006) (child ⟨true,false,1⟩))
    (h1RB : Cover (WeightedBound 100006) (child ⟨true,true,1⟩))
    (h1LC : Cover (WeightedBound 100006) (child ⟨true,false,2⟩))
    (h0LE : Cover (WeightedBound 100006) (child ⟨false,false,4⟩))
    (h0RE : Cover (WeightedBound 100006) (child ⟨false,true,4⟩))
    (h1LE : Cover (WeightedBound 100006) (child ⟨true,false,4⟩))
    (h1RE : Cover (WeightedBound 100006) (child ⟨true,true,4⟩)) :
    Cover (WeightedBound 6766859) p42 := by
  rw [← literal_eq_p42]
  exact BB6.Agent17Raw42GlobalBridge.global_cover_from_named
    h0LA h0RA h1LA h1RA h0RB h1LB h1RB h1LC h0LE h0RE h1LE h1RE

theorem sound_from_named
    (h0LA : Cover (WeightedBound 100006) (child ⟨false,false,0⟩))
    (h0RA : Cover (WeightedBound 1006)   (child ⟨false,true,0⟩))
    (h1LA : Cover (WeightedBound 100006) (child ⟨true,false,0⟩))
    (h1RA : Cover (WeightedBound 100006) (child ⟨true,true,0⟩))
    (h0RB : Cover (WeightedBound 1006)   (child ⟨false,true,1⟩))
    (h1LB : Cover (WeightedBound 100006) (child ⟨true,false,1⟩))
    (h1RB : Cover (WeightedBound 100006) (child ⟨true,true,1⟩))
    (h1LC : Cover (WeightedBound 100006) (child ⟨true,false,2⟩))
    (h0LE : Cover (WeightedBound 100006) (child ⟨false,false,4⟩))
    (h0RE : Cover (WeightedBound 100006) (child ⟨false,true,4⟩))
    (h1LE : Cover (WeightedBound 100006) (child ⟨true,false,4⟩))
    (h1RE : Cover (WeightedBound 100006) (child ⟨true,true,4⟩)) :
    ∀ m, compatible BB6.Agent31FourHoleFrontier.root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster38,
          BB6.Agent31FourHoleRoster.TNFQuotientCompatible e.2 m := by
  exact BB6.Agent17Raw42Canonical39Conditional.conditional_sound
    (cover_from_named_at_global
      h0LA h0RA h1LA h1RA h0RB h1LB h1RB h1LC h0LE h0RE h1LE h1RE)

#print axioms literal_eq_p42
#print axioms cover_from_named_at_global
#print axioms sound_from_named
end BB6.Agent17Raw42Canonical39FromNamed
