import Raw59Base

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent32Raw59Partition
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent32Raw59

def moves : List Move :=
  (List.finRange 6).flatMap fun q => [false,true].flatMap fun w =>
    [false,true].map fun r => ⟨w,r,q⟩

theorem moves_complete (mv : Move) : mv ∈ moves := by
  rcases mv with ⟨w,r,q⟩
  unfold moves
  apply List.mem_flatMap.mpr
  refine ⟨q,List.mem_finRange q,?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨w,by cases w <;> simp,?_⟩
  exact List.mem_map.mpr ⟨r,by cases r <;> simp,rfl⟩

def retained (closed : Move → Bool) : List Move :=
  moves.filter fun mv => !(closed mv)

theorem compatible_child {m : Machine} (hm : compatible p59 m) (v : Transition)
    (hv : m (0,true) = v) : compatible (refine p59 (0,true) v) m := by
  intro s t ht
  by_cases he : s = (0,true)
  · subst s; simp [refine] at ht; subst t; exact hv
  · exact hm s t (by simpa [refine,he] using ht)

theorem partition (closed : Move → Bool)
    (hs : ∀ mv, closed mv = true → ∀ m, compatible (child mv) m → WeightedBound 395 m)
    (m : Machine) (hm : compatible p59 m) :
    WeightedBound 395 m ∨ ∃ mv ∈ retained closed, compatible (child mv) m := by
  cases h : m (0,true) with
  | none => exact Or.inl (halt_branch m (compatible_child hm none h))
  | some mv =>
    have hc := compatible_child hm (some mv) h
    cases hd : closed mv with
    | true => exact Or.inl (hs mv hd m hc)
    | false =>
      exact Or.inr ⟨mv,List.mem_filter.mpr ⟨moves_complete mv,by simp [hd]⟩,hc⟩

theorem cover_raw59 (B : Nat) (hB : 395 ≤ B) (closed : Move → Bool)
    (hs : ∀ mv, closed mv = true → ∀ m, compatible (child mv) m → WeightedBound 395 m)
    (hr : ∀ mv ∈ retained closed, Cover (WeightedBound B) (child mv)) :
    Cover (WeightedBound B) p59 := by
  refine Cover.leaf p59 ?_
  intro m hm
  rcases partition closed hs m hm with h | ⟨mv,hmem,hc⟩
  · intro k d hk hd
    exact Nat.le_trans (h k d hk hd) hB
  · exact (hr mv hmem).sound m hc

#print axioms partition
#print axioms cover_raw59
end BB6.Agent32Raw59Partition
