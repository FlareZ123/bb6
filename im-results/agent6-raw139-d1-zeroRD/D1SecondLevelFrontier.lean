import D1SecondLevel
set_option maxHeartbeats 0

namespace BB6.Agent6D1SecondLevelFrontier
open BB6Coverage BB6.Agent13BlankDelay

def f2 : List PartialMachine :=
  BB6.Agent6D1TwoReduce.hard.map
    (fun n => BB6.Agent6D1TwoReduce.sub (BB6.Agent6D1TwoReduce.move n))
def f6 : List PartialMachine :=
  BB6.Agent6D1SixReduce.hard.map
    (fun n => BB6.Agent6D1SixReduce.sub (BB6.Agent6D1SixReduce.move n))
def f8 : List PartialMachine :=
  BB6.Agent6D1EightReduce.hard.map
    (fun n => BB6.Agent6D1EightReduce.sub (BB6.Agent6D1EightReduce.move n))
def f9 : List PartialMachine :=
  BB6.Agent6D1NineReduce.hard.map
    (fun n => BB6.Agent6D1NineReduce.sub (BB6.Agent6D1NineReduce.move n))
def f10 : List PartialMachine :=
  BB6.Agent6D1TenReduce.hard.map
    (fun n => BB6.Agent6D1TenReduce.sub (BB6.Agent6D1TenReduce.move n))
def f16 : List PartialMachine :=
  BB6.Agent6D1SixteenReduce.hard.map
    (fun n => BB6.Agent6D1SixteenReduce.sub (BB6.Agent6D1SixteenReduce.move n))
def f17 : List PartialMachine :=
  BB6.Agent6D1SeventeenReduce.hard.map
    (fun n => BB6.Agent6D1SeventeenReduce.sub (BB6.Agent6D1SeventeenReduce.move n))
def f18 : List PartialMachine :=
  BB6.Agent6D1EighteenReduce.hard.map
    (fun n => BB6.Agent6D1EighteenReduce.sub (BB6.Agent6D1EighteenReduce.move n))
def f19 : List PartialMachine :=
  BB6.Agent6D1NineteenReduce.hard.map
    (fun n => BB6.Agent6D1NineteenReduce.sub (BB6.Agent6D1NineteenReduce.move n))

/-- Exact explicit second-level residual frontier under Raw139 D1=0RD. -/
def frontier : List PartialMachine :=
  f2 ++ (f6 ++ (f8 ++ (f9 ++ (f10 ++ (f16 ++ (f17 ++ (f18 ++ f19)))))))

theorem frontier_length : frontier.length = 102 := by decide

theorem cover_of_frontier (B : Nat) (hB : 14 ≤ B)
    (h : ∀ p ∈ frontier, Cover (WeightedBound B) p) :
    Cover (WeightedBound B) BB6.Agent6D1ZeroRD.p := by
  apply BB6.Agent6D1SecondLevel.cover B hB
  · intro n hn
    apply h
    simp only [frontier, List.mem_append]
    exact Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩)
  · intro n hn
    apply h
    simp only [frontier, List.mem_append]
    exact Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩))
  · intro n hn
    apply h
    simp only [frontier, List.mem_append]
    exact Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩)))
  · intro n hn
    apply h
    simp only [frontier, List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩))))
  · intro n hn
    apply h
    simp only [frontier, List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩)))))
  · intro n hn
    apply h
    simp only [frontier, List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩))))))
  · intro n hn
    apply h
    simp only [frontier, List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩)))))))
  · intro n hn
    apply h
    simp only [frontier, List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Or.inl (List.mem_map.mpr ⟨n, hn, rfl⟩))))))))
  · intro n hn
    apply h
    simp only [frontier, List.mem_append]
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (List.mem_map.mpr ⟨n, hn, rfl⟩))))))))

#print axioms cover_of_frontier
end BB6.Agent6D1SecondLevelFrontier
