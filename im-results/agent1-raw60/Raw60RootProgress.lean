import Raw60RootCut

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent1Raw60Root
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent50RootFrontier
open BB6.Agent50RecursiveResidual

def remaining5 : List Move := [⟨false,false,2⟩, ⟨false,false,3⟩, ⟨false,false,5⟩, ⟨true,false,5⟩, ⟨true,true,4⟩]

theorem remaining5_count : remaining5.length = 5 := by decide

theorem parent_reduced
    (h0RC : ∀ m, compatible (child ⟨false,true,2⟩) m → WeightedBound 376 m)
    (h0RE : ∀ m, compatible (child ⟨false,true,4⟩) m → WeightedBound 719 m)
    (h0LB : ∀ m, compatible (child ⟨false,false,1⟩) m → WeightedBound 258 m)
    (h0RF : ∀ m, compatible (child ⟨false,true,5⟩) m → WeightedBound 1175 m)
    (h1LA : ∀ m, compatible (child ⟨true,false,0⟩) m → WeightedBound 178 m)
    (h1LB : ∀ m, compatible (child ⟨true,false,1⟩) m → WeightedBound 620 m)
    (h1LC : ∀ m, compatible (child ⟨true,false,2⟩) m → WeightedBound 253 m)
    (h1RF : ∀ m, compatible (child ⟨true,true,5⟩) m → WeightedBound 276 m)
    (m : Machine) (hm : compatible parent m) :
    WeightedBound 1175 m ∨ ∃ mv ∈ remaining5, compatible (child mv) m := by
  rcases parent_dichotomy h0RC h0RE m hm with hb | ⟨mv,hr,hc⟩
  · exact Or.inl hb
  · simp only [remaining,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact Or.inl (lift (by decide : 258 ≤ 1175) (h0LB m hc))
    · exact Or.inr ⟨_, by decide, hc⟩
    · exact Or.inr ⟨_, by decide, hc⟩
    · exact Or.inr ⟨_, by decide, hc⟩
    · exact Or.inl (lift (by decide : 1175 ≤ 1175) (h0RF m hc))
    · exact Or.inl (lift (by decide : 178 ≤ 1175) (h1LA m hc))
    · exact Or.inl (lift (by decide : 620 ≤ 1175) (h1LB m hc))
    · exact Or.inl (lift (by decide : 253 ≤ 1175) (h1LC m hc))
    · exact Or.inr ⟨_, by decide, hc⟩
    · exact Or.inr ⟨_, by decide, hc⟩
    · exact Or.inl (lift (by decide : 276 ≤ 1175) (h1RF m hc))

theorem scoreB_parent_reduced
    (h0RC : ∀ m, compatible (child ⟨false,true,2⟩) m → WeightedBound 376 m)
    (h0RE : ∀ m, compatible (child ⟨false,true,4⟩) m → WeightedBound 719 m)
    (h0LB : ∀ m, compatible (child ⟨false,false,1⟩) m → WeightedBound 258 m)
    (h0RF : ∀ m, compatible (child ⟨false,true,5⟩) m → WeightedBound 1175 m)
    (h1LA : ∀ m, compatible (child ⟨true,false,0⟩) m → WeightedBound 178 m)
    (h1LB : ∀ m, compatible (child ⟨true,false,1⟩) m → WeightedBound 620 m)
    (h1LC : ∀ m, compatible (child ⟨true,false,2⟩) m → WeightedBound 253 m)
    (h1RF : ∀ m, compatible (child ⟨true,true,5⟩) m → WeightedBound 276 m)
    (B : Nat) (hB : 1175 ≤ B)
    (tail : ∀ mv ∈ remaining5, ∀ m, compatible (child mv) m → WeightedBound B m)
    (m : Machine) (hm : compatible parent m) : WeightedBound B m := by
  rcases parent_reduced h0RC h0RE h0LB h0RF h1LA h1LB h1LC h1RF m hm with hb | ⟨mv,hr,hc⟩
  · exact lift hB hb
  · exact tail mv hr m hc

#print axioms parent_reduced
#print axioms scoreB_parent_reduced
end BB6.Agent1Raw60Root
