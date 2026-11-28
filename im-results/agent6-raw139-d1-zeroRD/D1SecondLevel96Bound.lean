import D1SecondLevel96
set_option maxHeartbeats 0

namespace BB6.Agent6D1SecondLevel96Bound
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent6D1SecondLevel96

/-- A source-level proof-transport fact: weakening the weighted bound preserves
    every explicit branch of an existing completion Cover. -/
theorem cover_mono {A B : Nat} (hAB : A ≤ B) {p : PartialMachine}
    (hp : Cover (WeightedBound A) p) : Cover (WeightedBound B) p := by
  induction hp with
  | leaf p hbound =>
      refine Cover.leaf p ?_
      intro m hm k d hk hd
      exact Nat.le_trans (hbound m hm k d hk hd) hAB
  | branch p s hu kids ih =>
      exact Cover.branch p s hu (fun t ht => ih t ht)

/-- Unlike the fixed-3000 specialization, this 96-child conditional interface
    can be discharged at any larger score, as required by slower sibling roots. -/
theorem cover_of_frontier (B : Nat) (hB : 3000 ≤ B)
    (h : ∀ p ∈ F.frontier, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) BB6.Agent6D1ZeroRD.p := by
  apply BB6.Agent6D1ZeroRD.cover B (by omega)
  intro n hn
  simp [BB6.Agent6D1ZeroRD.hard] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply BB6.Agent6D1TwoReduce.cover B (by omega)
    intro k hk
    exact h _ (F.mem2 hk)
  · apply BB6.Agent6D1SixReduce.cover B (by omega)
    intro k hk
    exact h _ (F.mem6 hk)
  · apply BB6.Agent6D1EightReduce.cover B (by omega)
    intro k hk
    simp [BB6.Agent6D1EightReduce.hard] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cover_mono hB BB6.Agent6D1EightFive.c1
    · exact h _ (F.mem8 (by decide))
    · exact cover_mono hB BB6.Agent6D1EightFive.c3
    · exact cover_mono hB BB6.Agent6D1EightFive.c6
    · exact h _ (F.mem8 (by decide))
    · exact cover_mono hB BB6.Agent6D1EightFour.c17
    · exact h _ (F.mem8 (by decide))
    · exact h _ (F.mem8 (by decide))
  · apply BB6.Agent6D1NineReduce.cover B (by omega)
    intro k hk
    simp [BB6.Agent6D1NineReduce.hard] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact cover_mono hB BB6.Agent6D1NineFour.c2
    · exact cover_mono hB BB6.Agent6D1NineFour.c6
    · exact h _ (F.mem9 (by decide))
    · exact h _ (F.mem9 (by decide))
    · exact h _ (F.mem9 (by decide))
    · exact h _ (F.mem9 (by decide))
  · apply BB6.Agent6D1TenReduce.cover B (by omega)
    intro k hk
    exact h _ (F.mem10 hk)
  · apply BB6.Agent6D1SixteenReduce.cover B (by omega)
    intro k hk
    exact h _ (F.mem16 hk)
  · apply BB6.Agent6D1SeventeenReduce.cover B (by omega)
    intro k hk
    exact h _ (F.mem17 hk)
  · apply BB6.Agent6D1EighteenReduce.cover B (by omega)
    intro k hk
    exact h _ (F.mem18 hk)
  · apply BB6.Agent6D1NineteenReduce.cover B (by omega)
    intro k hk
    exact h _ (F.mem19 hk)

#print axioms cover_mono
#print axioms cover_of_frontier
end BB6.Agent6D1SecondLevel96Bound
