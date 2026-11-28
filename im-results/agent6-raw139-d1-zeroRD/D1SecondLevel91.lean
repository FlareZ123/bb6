import D1SecondLevelFrontier
import D1EightFour
import D1EightTwo
import D1NineOne
import D1NineFour
set_option maxHeartbeats 0

namespace BB6.Agent6D1SecondLevel91
open BB6Coverage BB6.Agent13BlankDelay

namespace F
open BB6.Agent6D1SecondLevelFrontier

def f8 : List PartialMachine :=
  [18,19].map
    (fun n => BB6.Agent6D1EightReduce.sub (BB6.Agent6D1EightReduce.move n))

def f9 : List PartialMachine :=
  [17].map
    (fun n => BB6.Agent6D1NineReduce.sub (BB6.Agent6D1NineReduce.move n))

def frontier : List PartialMachine :=
  f2 ++ (f6 ++ (f8 ++ (f9 ++ (f10 ++ (f16 ++ (f17 ++ (f18 ++ f19)))))))

theorem frontier_length : frontier.length = 91 := by decide

theorem mem2 {n : Nat} (hn : n ∈ BB6.Agent6D1TwoReduce.hard) :
    BB6.Agent6D1TwoReduce.sub (BB6.Agent6D1TwoReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩)

theorem mem6 {n : Nat} (hn : n ∈ BB6.Agent6D1SixReduce.hard) :
    BB6.Agent6D1SixReduce.sub (BB6.Agent6D1SixReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩))

theorem mem8 {n : Nat} (hn : n ∈ [18,19]) :
    BB6.Agent6D1EightReduce.sub (BB6.Agent6D1EightReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩)))

theorem mem9 {n : Nat} (hn : n ∈ [17]) :
    BB6.Agent6D1NineReduce.sub (BB6.Agent6D1NineReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩))))

theorem mem10 {n : Nat} (hn : n ∈ BB6.Agent6D1TenReduce.hard) :
    BB6.Agent6D1TenReduce.sub (BB6.Agent6D1TenReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩)))))

theorem mem16 {n : Nat} (hn : n ∈ BB6.Agent6D1SixteenReduce.hard) :
    BB6.Agent6D1SixteenReduce.sub (BB6.Agent6D1SixteenReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩))))))

theorem mem17 {n : Nat} (hn : n ∈ BB6.Agent6D1SeventeenReduce.hard) :
    BB6.Agent6D1SeventeenReduce.sub (BB6.Agent6D1SeventeenReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩)))))))

theorem mem18 {n : Nat} (hn : n ∈ BB6.Agent6D1EighteenReduce.hard) :
    BB6.Agent6D1EighteenReduce.sub (BB6.Agent6D1EighteenReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩))))))))

theorem mem19 {n : Nat} (hn : n ∈ BB6.Agent6D1NineteenReduce.hard) :
    BB6.Agent6D1NineteenReduce.sub (BB6.Agent6D1NineteenReduce.move n) ∈ frontier := by
  simp only [frontier, List.mem_append]
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
    (List.mem_map.mpr ⟨n, hn, rfl⟩))))))))
end F

theorem cover_of_frontier
    (h : ∀ p ∈ F.frontier, Cover (WeightedBound 3000) p) :
    Cover (WeightedBound 3000) BB6.Agent6D1ZeroRD.p := by
  apply BB6.Agent6D1ZeroRD.cover 3000 (by omega)
  intro n hn
  simp [BB6.Agent6D1ZeroRD.hard] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · apply BB6.Agent6D1TwoReduce.cover 3000 (by omega)
    intro k hk
    exact h _ (F.mem2 hk)
  · apply BB6.Agent6D1SixReduce.cover 3000 (by omega)
    intro k hk
    exact h _ (F.mem6 hk)
  · exact BB6.Agent6D1EightTwo.cover
      (h _ (F.mem8 (by decide)))
      (h _ (F.mem8 (by decide)))
  · exact BB6.Agent6D1NineOne.cover
      (h _ (F.mem9 (by decide)))
  · apply BB6.Agent6D1TenReduce.cover 3000 (by omega)
    intro k hk
    exact h _ (F.mem10 hk)
  · apply BB6.Agent6D1SixteenReduce.cover 3000 (by omega)
    intro k hk
    exact h _ (F.mem16 hk)
  · apply BB6.Agent6D1SeventeenReduce.cover 3000 (by omega)
    intro k hk
    exact h _ (F.mem17 hk)
  · apply BB6.Agent6D1EighteenReduce.cover 3000 (by omega)
    intro k hk
    exact h _ (F.mem18 hk)
  · apply BB6.Agent6D1NineteenReduce.cover 3000 (by omega)
    intro k hk
    exact h _ (F.mem19 hk)

#print axioms cover_of_frontier
end BB6.Agent6D1SecondLevel91
