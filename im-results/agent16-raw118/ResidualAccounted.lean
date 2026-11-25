import ResidualKeyed

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent16ResidualCover
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent47PartialAudit
open BB6.Agent50TNFPilot BB6.Agent8TNFPath BB6.Agent10ZipAudit

/-- Verify each unresolved leaf in place. Closed subtrees are skipped;
    their separate partialCheck proof is still required by the consumer. -/
def accountedCheck (t : AcceptedTree B) (holdout p : PartialMachine) : PartialAudit → Bool
  | .unresolved => lookup p (tableKey p) t || sameTable p holdout
  | .closed _ => true
  | .split _ s kids => allMoves (fun mv =>
      accountedCheck t holdout (refine p s (some mv)) (kids mv))
termination_by structural a => a

theorem accountedResidual {B : Nat} (t : AcceptedTree B) (holdout p : PartialMachine)
    (a : PartialAudit) (h : accountedCheck t holdout p a = true) :
    ∀ e ∈ partialResiduals p a,
      lookup e.2 (tableKey e.2) t = true ∨ sameTable e.2 holdout = true := by
  induction a generalizing p with
  | unresolved =>
    intro e he
    simp only [partialResiduals, List.mem_singleton] at he
    subst e
    simpa only [accountedCheck, Bool.or_eq_true] using h
  | closed _ => simp [partialResiduals]
  | split n s kids ih =>
    intro e he
    have ha : allMoves (fun mv =>
        accountedCheck t holdout (refine p s (some mv)) (kids mv)) = true := by
      simpa only [accountedCheck] using h
    obtain ⟨mv, _, hmem⟩ := List.mem_flatMap.mp (by simpa only [partialResiduals] using he)
    obtain ⟨r, hr, heq⟩ := List.mem_map.mp hmem
    subst e
    exact ih mv (refine p s (some mv)) (allMoves_sound _ ha mv) r hr

/-- Consume a partial audit without materializing the global residual list.
    Keys merely accelerate exact table comparison. -/
theorem accountedSound {B : Nat} (t : AcceptedTree B) (holdout p : PartialMachine)
    (a : PartialAudit)
    (h : ∀ m, compatible p m → WeightedBound B m ∨
      ∃ e ∈ partialResiduals p a, compatible e.2 m)
    (ha : accountedCheck t holdout p a = true) :
    ∀ m, compatible p m → WeightedBound B m ∨ compatible holdout m := by
  intro m hm
  rcases h m hm with hb | ⟨e, he, hc⟩
  · exact Or.inl hb
  · rcases accountedResidual t holdout p a ha e he with hlook | htable
    · exact Or.inl (lookup_sound hlook m hc)
    · exact Or.inr (sameTable_sound htable ▸ hc)

/-- A local conditional cover, with the first-one and no-assigned-halt
    hypotheses made explicit for compositional reuse. -/
def ConditionalCover (B : Nat) (p holdout : PartialMachine) : Prop :=
  p initialSlot = some (some ⟨true,true,1⟩) →
  weightedTNFNoAssignedHalt p →
  ∀ m, compatible p m → WeightedBound B m ∨ compatible holdout m

theorem leafConditional {B : Nat} (holdout p : PartialMachine) (a : PartialAudit)
    (t : AcceptedTree B) (hc : partialCheck B p a = true)
    (ha : accountedCheck t holdout p a = true) :
    ConditionalCover B p holdout := by
  intro hf hn
  exact accountedSound t holdout p a (partialSound B p a hf hn hc) ha

/-- A split requires the exact first-hole query and all 24 ordinary children.
    The halt child is covered by the original weighted first-hole theorem. -/
theorem splitConditional {B : Nat} (holdout p : PartialMachine) (n : Nat) (s : Slot)
    (h : zipQueryOK B p n s = true)
    (children : ∀ mv, ConditionalCover B (refine p s (some mv)) holdout) :
    ConditionalCover B p holdout := by
  intro hf hno m hm
  obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound h
  cases ht : m s with
  | none =>
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = s := by simpa [hr] using hread
      have hc : compatible (refine p s none) m := by
        simpa [ht] using compatible_refine p m s hm
      exact Or.inl (first_hole_weighted_halt B p n c hf hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using weightOK_sound p s n B hw) m
        (by simpa [hs] using hc))
  | some mv =>
    have hc : compatible (refine p s (some mv)) m := by
      simpa [ht] using compatible_refine p m s hm
    exact children mv (refine_preserves_firstOne p s (some mv) hhole hf)
      (weightedTNFNoAssignedHalt_refine p s mv hno) m hc

/-- Exact extension check between physical transition tables. -/
def subtable (p q : PartialMachine) : Bool :=
  (List.finRange 6).all fun state => [false,true].all fun symbol =>
    match p (state,symbol) with
    | none => true
    | some t => decide (q (state,symbol) = some t)

theorem subtable_sound {p q : PartialMachine} {m : Machine}
    (h : subtable p q = true) (hm : compatible q m) : compatible p m := by
  intro s t hs
  rcases s with ⟨state,b⟩
  have h1 := List.all_eq_true.mp h state (List.mem_finRange state)
  have h2 := List.all_eq_true.mp h1 b (by cases b <;> simp)
  exact hm (state,b) t (of_decide_eq_true (by simpa only [hs] using h2))

#print axioms accountedResidual
#print axioms accountedSound
#print axioms leafConditional
#print axioms splitConditional
#print axioms subtable_sound
end BB6.Agent16ResidualCover
