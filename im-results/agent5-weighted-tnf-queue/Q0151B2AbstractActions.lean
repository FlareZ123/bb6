import Q0151B2TailFamilies

set_option maxHeartbeats 0

/-!
Exact finite-interpreter action witnesses for all B2 nested second-run
families. These are parameterized by arbitrary current segment summaries,
not by sampled reachable states. The outer B2 cut and the physically
actual inner cut are both proven members of the executable delta list.
The 4n+4 family requires two abstract choices (j=1 at n=0 and j=2 at
n>0); the 4n+5 family uses the first admitted choice j=1 for every n.
Arbitrarily long concrete outputs are related by the separate positive
alternation saturation lemmas.
-/

namespace BB6.Agent5Q0151B2AbstractActions
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151NestedRightCut
open BB6.Agent5Q0151B2TailFamilies
open BB6.Agent5Q0151Category

theorem second_four_action (s : SegmentSummary) (rest : List Nat)
    (h : rightType (rightSig (1::3::rest)) ≠ 0) :
    Action.stay (mkControl true (rightSig rest)
      (segAppend s ([true,true,true,false] ++ altWord 1 ++ [true,true]))) ∈
      delta (mkControl true (rightSig (1::3::rest)) s) := by
  have hh := b_two_nested 3 rest h
  have hfirst : (2,rightSig (3::rest)) ∈
      cut (rightSig (1::3::rest)) := hh.1
  have hsecond : (4,rightSig rest) ∈ cut (rightSig (3::rest)) := by
    simpa [actualNext,cat] using hh.2
  unfold delta
  apply List.mem_flatMap.mpr
  refine ⟨(2,rightSig (3::rest)),
    by simpa [mkControl] using hfirst, ?_⟩
  simp [actionsFor,choicesA,mkControl]
  exact ⟨4,rightSig rest,hsecond,by simp⟩

theorem second_eight_action (s : SegmentSummary) (n : Nat)
    (hn : 0 < n) (rest : List Nat)
    (h : rightType (rightSig (1::(4*n+3)::rest)) ≠ 0) :
    Action.stay (mkControl true (rightSig rest)
      (segAppend s ([true,true,true,false] ++ altWord 3 ++ [true,true]))) ∈
      delta (mkControl true (rightSig (1::(4*n+3)::rest)) s) := by
  have hh := b_two_nested (4*n+3) rest h
  have hfirst : (2,rightSig ((4*n+3)::rest)) ∈
      cut (rightSig (1::(4*n+3)::rest)) := hh.1
  have hcat : cat ((4*n+3)+1) = 8 := by
    rw [show 4*n+3+1=4*n+4 by omega,cat_four]
    simp [Nat.ne_of_gt hn]
  have hsecond : (8,rightSig rest) ∈
      cut (rightSig ((4*n+3)::rest)) := by
    simpa [actualNext,hcat] using hh.2
  unfold delta
  apply List.mem_flatMap.mpr
  refine ⟨(2,rightSig ((4*n+3)::rest)),
    by simpa [mkControl] using hfirst, ?_⟩
  simp [actionsFor,choicesA,mkControl]
  exact ⟨8,rightSig rest,hsecond,by simp⟩

theorem second_five_action (s : SegmentSummary) (n : Nat)
    (rest : List Nat)
    (h : rightType (rightSig (1::(4*n+4)::rest)) ≠ 0) :
    Action.pop (segConcat
      (segAppend s ([true,true,true,false] ++ altWord 1 ++ [true]))
        (rightSig rest)) ∈
      delta (mkControl true (rightSig (1::(4*n+4)::rest)) s) := by
  have hh := b_two_nested (4*n+4) rest h
  have hfirst : (2,rightSig ((4*n+4)::rest)) ∈
      cut (rightSig (1::(4*n+4)::rest)) := hh.1
  have hcat : cat ((4*n+4)+1) = 5 := by
    rw [show 4*n+4+1=4*n+5 by omega,cat_five]
  have hsecond : (5,rightSig rest) ∈
      cut (rightSig ((4*n+4)::rest)) := by
    simpa [actualNext,hcat] using hh.2
  unfold delta
  apply List.mem_flatMap.mpr
  refine ⟨(2,rightSig ((4*n+4)::rest)),
    by simpa [mkControl] using hfirst, ?_⟩
  simp [actionsFor,choicesA,mkControl]
  exact ⟨5,rightSig rest,hsecond,by simp⟩

#print axioms second_four_action
#print axioms second_eight_action
#print axioms second_five_action
end BB6.Agent5Q0151B2AbstractActions
