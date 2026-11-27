import Raw56E1RCCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw56E1RC
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

/-- Literal C1 refinement of the authentic E1=0RC child. -/
def child (v : Move) : PartialMachine := refine p (2,true) (some v)

/-- All ordinary canonical residual choices, with branch-specific bounds.
    The late 0LF terminal query requires the larger bound. -/
def c0LA : PartialMachine := child ⟨false, false, 0⟩
def c0LB : PartialMachine := child ⟨false, false, 1⟩
def c0LE : PartialMachine := child ⟨false, false, 4⟩
def c0LF : PartialMachine := child ⟨false, false, 5⟩
def c0RA : PartialMachine := child ⟨false, true, 0⟩
def c0RB : PartialMachine := child ⟨false, true, 1⟩
def c0RD : PartialMachine := child ⟨false, true, 3⟩
def c0RE : PartialMachine := child ⟨false, true, 4⟩
def c0RF : PartialMachine := child ⟨false, true, 5⟩
def c1LA : PartialMachine := child ⟨true, false, 0⟩
def c1LB : PartialMachine := child ⟨true, false, 1⟩
def c1LC : PartialMachine := child ⟨true, false, 2⟩
def c1LE : PartialMachine := child ⟨true, false, 4⟩
def c1LF : PartialMachine := child ⟨true, false, 5⟩
def c1RA : PartialMachine := child ⟨true, true, 0⟩
def c1RB : PartialMachine := child ⟨true, true, 1⟩
def c1RD : PartialMachine := child ⟨true, true, 3⟩
def c1RE : PartialMachine := child ⟨true, true, 4⟩
def c1RF : PartialMachine := child ⟨true, true, 5⟩

def children : List (PartialMachine × Nat) := [
  (c0LA, 7014),
  (c0LB, 7014),
  (c0LE, 7014),
  (c0LF, 10000),
  (c0RA, 7014),
  (c0RB, 7014),
  (c0RD, 7014),
  (c0RE, 7014),
  (c0RF, 7014),
  (c1LA, 7014),
  (c1LB, 7014),
  (c1LC, 7014),
  (c1LE, 7014),
  (c1LF, 7014),
  (c1RA, 7014),
  (c1RB, 7014),
  (c1RD, 7014),
  (c1RE, 7014),
  (c1RF, 7014)]

/-- The exact original residual tables are covered by the literal child list. -/
theorem children_match : remaining19.all (fun e => children.any (fun c => sameTable e.2 c.1)) = true := by decide

theorem children_count : children.length = 19 := by decide
theorem children_bound : children.all (fun c => decide (c.2 ≤ 10000)) = true := by decide

/-- Explicit branch obligations; each is a quotient-compatible weighted bound. -/
structure BranchCovers : Prop where
  h0LA : ∀ m, TNFQuotientCompatible c0LA m → WeightedBound 7014 m
  h0LB : ∀ m, TNFQuotientCompatible c0LB m → WeightedBound 7014 m
  h0LE : ∀ m, TNFQuotientCompatible c0LE m → WeightedBound 7014 m
  h0LF : ∀ m, TNFQuotientCompatible c0LF m → WeightedBound 10000 m
  h0RA : ∀ m, TNFQuotientCompatible c0RA m → WeightedBound 7014 m
  h0RB : ∀ m, TNFQuotientCompatible c0RB m → WeightedBound 7014 m
  h0RD : ∀ m, TNFQuotientCompatible c0RD m → WeightedBound 7014 m
  h0RE : ∀ m, TNFQuotientCompatible c0RE m → WeightedBound 7014 m
  h0RF : ∀ m, TNFQuotientCompatible c0RF m → WeightedBound 7014 m
  h1LA : ∀ m, TNFQuotientCompatible c1LA m → WeightedBound 7014 m
  h1LB : ∀ m, TNFQuotientCompatible c1LB m → WeightedBound 7014 m
  h1LC : ∀ m, TNFQuotientCompatible c1LC m → WeightedBound 7014 m
  h1LE : ∀ m, TNFQuotientCompatible c1LE m → WeightedBound 7014 m
  h1LF : ∀ m, TNFQuotientCompatible c1LF m → WeightedBound 7014 m
  h1RA : ∀ m, TNFQuotientCompatible c1RA m → WeightedBound 7014 m
  h1RB : ∀ m, TNFQuotientCompatible c1RB m → WeightedBound 7014 m
  h1RD : ∀ m, TNFQuotientCompatible c1RD m → WeightedBound 7014 m
  h1RE : ∀ m, TNFQuotientCompatible c1RE m → WeightedBound 7014 m
  h1RF : ∀ m, TNFQuotientCompatible c1RF m → WeightedBound 7014 m

private theorem branch_cover (h : BranchCovers) (c : PartialMachine × Nat) (hc : c ∈ children) :
    ∀ m, TNFQuotientCompatible c.1 m → WeightedBound c.2 m := by
  simp only [children, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact h.h0LA
  · exact h.h0LB
  · exact h.h0LE
  · exact h.h0LF
  · exact h.h0RA
  · exact h.h0RB
  · exact h.h0RD
  · exact h.h0RE
  · exact h.h0RF
  · exact h.h1LA
  · exact h.h1LB
  · exact h.h1LC
  · exact h.h1LE
  · exact h.h1LF
  · exact h.h1RA
  · exact h.h1RB
  · exact h.h1RD
  · exact h.h1RE
  · exact h.h1RF

/-- Exact mixed-bound composition, conditional on the nineteen named Covers. -/
theorem all_quotient_from_branches (h : BranchCovers) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound 10000 m := by
  intro m hm
  rcases sound19 m hm with hb | ⟨e,he,hq⟩
  · intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) (by decide)
  · obtain ⟨c,hc,hmatch⟩ := List.any_eq_true.mp (List.all_eq_true.mp children_match e he)
    have heq : e.2 = c.1 := sameTable_sound hmatch
    have hb := branch_cover h c hc m (heq ▸ hq)
    have hbound : c.2 ≤ 10000 := of_decide_eq_true (List.all_eq_true.mp children_bound c hc)
    intro k d hk hd
    exact Nat.le_trans (hb k d hk hd) hbound

theorem all_from_branches (h : BranchCovers) :
    ∀ m, compatible p m → WeightedBound 10000 m := by
  intro m hm
  exact all_quotient_from_branches h m (compatible_quotient hm)

#print axioms children_match
#print axioms children_count
#print axioms children_bound
#print axioms all_quotient_from_branches
#print axioms all_from_branches
end BB6.Agent1Raw56E1RC

namespace BB6.Agent1Raw56Root
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent19CanonicalPartial
open BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot BB6.Agent31FourHoleRoster

def remaining18RC := remaining19.filter (fun e => !sameTable e.2 BB6.Agent1Raw56E1RC.p)
theorem count18RC : remaining18RC.length = 18 := by decide

/-- Consume the complete E1=0RC child at its larger bound, retaining exactly
    the other eighteen representatives of the already accepted root cut. -/
theorem sound18RC (hRC : ∀ m, TNFQuotientCompatible BB6.Agent1Raw56E1RC.p m → WeightedBound 10000 m) :
    ∀ m, TNFQuotientCompatible parent m →
      WeightedBound 10000 m ∨ ∃ e ∈ remaining18RC, TNFQuotientCompatible e.2 m := by
  intro m hm
  rcases sound19_closed m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · by_cases hmatch : sameTable e.2 BB6.Agent1Raw56E1RC.p = true
    · exact Or.inl (hRC m ((sameTable_sound hmatch) ▸ hq))
    · exact Or.inr ⟨e,List.mem_filter.mpr ⟨he,by simp [hmatch]⟩,hq⟩

theorem sound18RC_from_branches (h : BB6.Agent1Raw56E1RC.BranchCovers) :
    ∀ m, TNFQuotientCompatible parent m →
      WeightedBound 10000 m ∨ ∃ e ∈ remaining18RC, TNFQuotientCompatible e.2 m :=
  sound18RC (BB6.Agent1Raw56E1RC.all_quotient_from_branches h)

#print axioms count18RC
#print axioms sound18RC
#print axioms sound18RC_from_branches
end BB6.Agent1Raw56Root
