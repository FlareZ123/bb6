import D1SecondLevelFrontier
set_option maxHeartbeats 0
namespace BB6.Agent6D1SecondLevel89OfParents
open BB6Coverage BB6.Agent13BlankDelay
namespace F
open BB6.Agent6D1SecondLevelFrontier
def f9 : List PartialMachine :=
  [17].map (fun n => BB6.Agent6D1NineReduce.sub (BB6.Agent6D1NineReduce.move n))
def frontier : List PartialMachine := f2 ++ (f6 ++ (f9 ++ (f10 ++ (f16 ++ (f17 ++ (f18 ++ (f19)))))))
theorem frontier_length : frontier.length = 89 := by decide

theorem mem2 {n : Nat} (hn : n ∈ BB6.Agent6D1TwoReduce.hard) :
    BB6.Agent6D1TwoReduce.sub (BB6.Agent6D1TwoReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩)

theorem mem6 {n : Nat} (hn : n ∈ BB6.Agent6D1SixReduce.hard) :
    BB6.Agent6D1SixReduce.sub (BB6.Agent6D1SixReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩))

theorem mem9 {n : Nat} (hn : n ∈ [17]) :
    BB6.Agent6D1NineReduce.sub (BB6.Agent6D1NineReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩)))

theorem mem10 {n : Nat} (hn : n ∈ BB6.Agent6D1TenReduce.hard) :
    BB6.Agent6D1TenReduce.sub (BB6.Agent6D1TenReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩))))

theorem mem16 {n : Nat} (hn : n ∈ BB6.Agent6D1SixteenReduce.hard) :
    BB6.Agent6D1SixteenReduce.sub (BB6.Agent6D1SixteenReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩)))))

theorem mem17 {n : Nat} (hn : n ∈ BB6.Agent6D1SeventeenReduce.hard) :
    BB6.Agent6D1SeventeenReduce.sub (BB6.Agent6D1SeventeenReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩))))))

theorem mem18 {n : Nat} (hn : n ∈ BB6.Agent6D1EighteenReduce.hard) :
    BB6.Agent6D1EighteenReduce.sub (BB6.Agent6D1EighteenReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩)))))))

theorem mem19 {n : Nat} (hn : n ∈ BB6.Agent6D1NineteenReduce.hard) :
    BB6.Agent6D1NineteenReduce.sub (BB6.Agent6D1NineteenReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (List.mem_map.mpr ⟨n, hn, rfl⟩)))))))

end F

theorem cover_mono {A B : Nat} (hAB : A ≤ B) {p : PartialMachine}
    (hp : Cover (WeightedBound A) p) : Cover (WeightedBound B) p := by
  induction hp with
  | leaf p hbound =>
      refine Cover.leaf p ?_
      intro m hm k d hk hd
      exact Nat.le_trans (hbound m hm k d hk hd) hAB
  | branch p s hu kids ih =>
      exact Cover.branch p s hu (fun t ht => ih t ht)

theorem cover_of_frontier (B : Nat) (hB : 3000 ≤ B)
    (h8 : Cover (WeightedBound 3000) BB6.Agent6D1EightReduce.p)
    (h92 : Cover (WeightedBound 3000) (BB6.Agent6D1NineReduce.sub (BB6.Agent6D1NineReduce.move 2)))
    (h96 : Cover (WeightedBound 3000) (BB6.Agent6D1NineReduce.sub (BB6.Agent6D1NineReduce.move 6)))
    (h916 : Cover (WeightedBound 3000) (BB6.Agent6D1NineReduce.sub (BB6.Agent6D1NineReduce.move 16)))
    (h918 : Cover (WeightedBound 3000) (BB6.Agent6D1NineReduce.sub (BB6.Agent6D1NineReduce.move 18)))
    (h919 : Cover (WeightedBound 3000) (BB6.Agent6D1NineReduce.sub (BB6.Agent6D1NineReduce.move 19)))
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
  · exact cover_mono hB h8
  · apply BB6.Agent6D1NineReduce.cover B (by omega)
    intro k hk
    simp [BB6.Agent6D1NineReduce.hard] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
    · exact cover_mono hB h92
    · exact cover_mono hB h96
    · exact cover_mono hB h916
    · exact h _ (F.mem9 (by decide))
    · exact cover_mono hB h918
    · exact cover_mono hB h919
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

#print axioms cover_of_frontier
end BB6.Agent6D1SecondLevel89OfParents
