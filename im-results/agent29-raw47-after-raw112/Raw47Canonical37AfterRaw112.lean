import Raw47Canonical37ConditionalAfterRaw112
import Raw47KernelBridge

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-!
Unconditional Raw47 removal after the already source-accepted Raw39+Raw112
Canonical38 successor. The Raw47 Cover is imported from the separately
source-accepted Raw47 parent through an authenticated, source-kernel-checked
relocation bridge. The only remaining assumptions are the exact 37 leaf Covers.
-/

namespace BB6.Agent29Raw47AfterRaw112

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent50TNFPilot
open BB6.Agent47CanonicalFrontier

abbrev p47 := BB6.Agent29Raw47AfterRaw112Conditional.p47
noncomputable abbrev roster37 :=
  BB6.Agent29Raw47AfterRaw112Conditional.roster37

theorem literal_eq_accepted_parent :
    p47 = BB6.Agent50Raw47Bridge.parent := by
  rfl

theorem p47_source_cover :
    Cover (WeightedBound 6766859) p47 := by
  have h := BB6.Agent50Raw47Bridge.cover_at 6766859 (by decide)
  simpa only [literal_eq_accepted_parent] using h

theorem sound_integrated :
    ∀ m, compatible root m →
      WeightedBound 6766859 m ∨
        ∃ e ∈ roster37, TNFQuotientCompatible e.2 m :=
  BB6.Agent29Raw47AfterRaw112Conditional.conditional_sound p47_source_cover

theorem count37 : roster37.length = 37 :=
  BB6.Agent29Raw47AfterRaw112Conditional.count37

theorem exact_at_champion_score
    (hLeaves : ∀ e ∈ roster37,
      Cover (WeightedBound (BB6ChampionArithmetic.proposedTM63Moves + 7)) e.2) :
    BB6.Coverage.ExactBB6
      (BB6ChampionArithmetic.proposedTM63Moves + 7) :=
  BB6.Agent29Raw47AfterRaw112Conditional.conditional_exact_at_champion
    p47_source_cover hLeaves

#print axioms literal_eq_accepted_parent
#print axioms p47_source_cover
#print axioms sound_integrated
#print axioms count37
#print axioms exact_at_champion_score

end BB6.Agent29Raw47AfterRaw112
