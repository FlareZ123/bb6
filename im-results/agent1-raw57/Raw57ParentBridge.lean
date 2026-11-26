import RecursiveResidual
import Raw57Easy

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent1Raw57Parent
open BB6Coverage BB6.Agent13BlankDelay
open BB6.Agent50RecursiveResidual

abbrev parent : PartialMachine := BB6.Agent6Raw57Easy.p57
abbrev child (mv : Move) : PartialMachine := BB6.Agent6Raw57Easy.child mv

-- The three lists plus the five immediate-cycle choices exhaust all
-- ordinary A1 transitions. The halt choice is proved separately.
def early : List Move :=
  [⟨false,true,0⟩, ⟨false,true,1⟩, ⟨false,true,2⟩,
   ⟨true,true,1⟩, ⟨true,true,2⟩, ⟨true,true,4⟩,
   ⟨false,true,4⟩, ⟨false,true,5⟩]
def middle : List Move :=
  [⟨false,false,1⟩, ⟨false,false,2⟩, ⟨false,false,3⟩,
   ⟨true,true,0⟩, ⟨true,true,5⟩, ⟨true,false,2⟩]
def residual : List Move :=
  [⟨true,false,0⟩, ⟨true,false,1⟩, ⟨true,false,4⟩,
   ⟨false,false,5⟩, ⟨true,false,5⟩]
def cycles : List Move :=
  [⟨false,false,0⟩, ⟨false,true,3⟩, ⟨false,false,4⟩,
   ⟨true,false,3⟩, ⟨true,true,3⟩]

theorem counts : early.length = 8 ∧ middle.length = 6 ∧
    residual.length = 5 ∧ cycles.length = 5 := by decide
theorem distinct : (early ++ middle ++ residual ++ cycles).Nodup := by decide

theorem partition (mv : Move) :
    mv ∈ early ∨ mv ∈ middle ∨ mv ∈ residual ∨ mv ∈ cycles := by
  rcases mv with ⟨w,r,q⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r <;> decide

theorem lift {B C : Nat} {m : Machine} (h : B ≤ C)
    (hb : WeightedBound B m) : WeightedBound C m := by
  intro k d hk hd
  exact Nat.le_trans (hb k d hk hd) h

theorem cycle_bound (mv : Move) (h : mv ∈ cycles)
    (m : Machine) (hm : compatible (child mv) m) : WeightedBound 273 m := by
  simp only [cycles, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  · exact BB6.Agent6Raw57Easy.la.sound m hm
  · exact BB6.Agent6Raw57Easy.rd.sound m hm
  · exact BB6.Agent6Raw57Easy.le.sound m hm
  · exact BB6.Agent6Raw57Easy.ld1.sound m hm
  · exact BB6.Agent6Raw57Easy.rd1.sound m hm

theorem first_query : queryOK 273 parent 7 (0,true) = true := by decide

/-- Exact five-choice conditional reduction, independent of generated
child audit modules or quotient roster revisions. No supplied branch
bound is asserted here. -/
theorem parent_dichotomy629
    (hEarly : ∀ mv ∈ early, ∀ m, compatible (child mv) m → WeightedBound 273 m)
    (hMiddle : ∀ mv ∈ middle, ∀ m, compatible (child mv) m → WeightedBound 629 m)
    (m : Machine) (hm : compatible parent m) :
    WeightedBound 629 m ∨ ∃ mv ∈ residual, compatible (child mv) m := by
  cases hs : m (0,true) with
  | none =>
    exact Or.inl (lift (by decide : 273 ≤ 629)
      (queryOK_sound 273 parent 7 (0,true) first_query m
        (compatible_refine hm (0,true) none hs)))
  | some mv =>
    have hc : compatible (child mv) m := compatible_refine hm (0,true) (some mv) hs
    rcases partition mv with he | hn | hr | hy
    · exact Or.inl (lift (by decide : 273 ≤ 629) (hEarly mv he m hc))
    · exact Or.inl (hMiddle mv hn m hc)
    · exact Or.inr ⟨mv,hr,hc⟩
    · exact Or.inl (lift (by decide : 273 ≤ 629) (cycle_bound mv hy m hc))

/-- A stable score-target parent Cover. Every ordinary transition and the
authentic halt choice is consumed; there is no simulation cutoff. -/
theorem cover_at_target (B : Nat) (hB : 629 ≤ B)
    (hEarly : ∀ mv ∈ early, ∀ m, compatible (child mv) m → WeightedBound 273 m)
    (hMiddle : ∀ mv ∈ middle, ∀ m, compatible (child mv) m → WeightedBound 629 m)
    (hTail : ∀ mv ∈ residual, Cover (WeightedBound B) (child mv)) :
    Cover (WeightedBound B) parent := by
  apply Cover.leaf
  intro m hm
  rcases parent_dichotomy629 hEarly hMiddle m hm with hb | ⟨mv,hr,hc⟩
  · exact lift hB hb
  · exact (hTail mv hr).sound m hc

#print axioms partition
#print axioms parent_dichotomy629
#print axioms cover_at_target
end BB6.Agent1Raw57Parent
