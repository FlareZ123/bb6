import Q0151B2TailFamilies
import Q0151ParamSaturation
import Q0151StackSaturation

set_option maxHeartbeats 0

/-!
Complete, all-length FINITE INTERPRETER witnesses for the six genuine
outer macro families B/C × (4k+4,4k+5,4k+6). These theorems quantify over
every Nat k and arbitrary source-compatible segment summary. They prove
membership of the required action in the exact executable delta list;
positive-mode hypotheses are the same invariant proven for Good by
the 814-control certificate. With the separate authentic positive-length
source macros, this supplies the finite half of ALL nonexceptional
unbounded source-to-abstract transition branches.
-/

namespace BB6.Agent5Q0151OuterAbstractActions
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151ParamSaturation
open BB6.Agent5Q0151B2TailFamilies
open BB6.Agent5Q0151Category

theorem b_four_push (s : SegmentSummary) (n : Nat) (rest : List Nat)
    (h : rightType (rightSig ((4*n+3)::rest)) ≠ 0) :
    Action.push (mkControl false (rightSig rest)
      (segAppend emptySegment (altWord (2*n) ++ [true,true,true]))) s ∈
      delta (mkControl true (rightSig ((4*n+3)::rest)) s) := by
  have hh : (cat (4*n+4),rightSig rest) ∈
      cut (rightSig ((4*n+3)::rest)) := by
    simpa [actualNext,show 4*n+3+1=4*n+4 by omega] using
      cut_real_next ((4*n+3)::rest) h
  unfold delta
  apply List.mem_flatMap.mpr
  refine ⟨(cat (4*n+4),rightSig rest),
    by simpa [mkControl] using hh, ?_⟩
  cases n with
  | zero =>
      simp [actionsFor, choicesA, cat, mkControl]
  | succ k =>
      have hc : cat (4*(k+1)+4) = 8 := by
        rw [cat_four]
        simp
      have hsat := big_zero_new_segment (k+2) (by omega)
      have he : segAppend emptySegment
          (altWord (2*(k+1)) ++ [true,true,true]) =
          segAppend emptySegment (altWord 2 ++ [true,true,true]) := by
        have hk : 2*(k+2)-2=2*(k+1) := by omega
        rw [hk] at hsat
        exact hsat
      rw [he]
      simp [actionsFor,choicesA,hc,mkControl]

theorem c_four_stay (s : SegmentSummary)
    (hN : -1 ≤ s.imageN) (hP : -1 ≤ s.imageP)
    (n : Nat) (rest : List Nat)
    (h : rightType (rightSig ((4*n+3)::rest)) ≠ 0) :
    Action.stay (mkControl false (rightSig rest)
      (segAppend s (altWord (2*n+1) ++ [true,true,true]))) ∈
      delta (mkControl false (rightSig ((4*n+3)::rest)) s) := by
  have hh : (cat (4*n+4),rightSig rest) ∈
      cut (rightSig ((4*n+3)::rest)) := by
    simpa [actualNext,show 4*n+3+1=4*n+4 by omega] using
      cut_real_next ((4*n+3)::rest) h
  unfold delta
  apply List.mem_flatMap.mpr
  refine ⟨(cat (4*n+4),rightSig rest),
    by simpa [mkControl] using hh, ?_⟩
  cases n with
  | zero =>
      simp [actionsFor,choicesA,cat,mkControl]
  | succ k =>
      have hc : cat (4*(k+1)+4) = 8 := by
        rw [cat_four]
        simp
      have he := alt_positive_both s (2*(k+1)+1) 3
        (by omega) (by decide) [true,true,true] hN hP
      rw [he]
      simp [actionsFor,choicesA,hc,mkControl]

theorem b_five_push (s : SegmentSummary) (n : Nat) (rest : List Nat)
    (h : rightType (rightSig ((4*n+4)::rest)) ≠ 0) :
    Action.push (mkControl true (rightSig rest)
      (segAppend emptySegment (altWord (2*n+1) ++ [true,true]))) s ∈
      delta (mkControl true (rightSig ((4*n+4)::rest)) s) := by
  have hh : (5,rightSig rest) ∈ cut (rightSig ((4*n+4)::rest)) := by
    have hc : cat ((4*n+4)+1)=5 := by
      rw [show 4*n+4+1=4*n+5 by omega,cat_five]
    simpa [actualNext,hc] using cut_real_next ((4*n+4)::rest) h
  unfold delta
  apply List.mem_flatMap.mpr
  refine ⟨(5,rightSig rest), by simpa [mkControl] using hh, ?_⟩
  have hsat := big_odd_new_segment (n+1) (by omega)
  have hlen : 2*(n+1)-1 = 2*n+1 := by omega
  rw [hlen] at hsat
  rw [hsat]
  simp [actionsFor,choicesA,mkControl]

theorem c_five_stay (s : SegmentSummary)
    (hN : -1 ≤ s.imageN) (hP : -1 ≤ s.imageP)
    (n : Nat) (rest : List Nat)
    (h : rightType (rightSig ((4*n+4)::rest)) ≠ 0) :
    Action.stay (mkControl true (rightSig rest)
      (segAppend s (altWord (2*n+2) ++ [true,true]))) ∈
      delta (mkControl false (rightSig ((4*n+4)::rest)) s) := by
  have hh : (5,rightSig rest) ∈ cut (rightSig ((4*n+4)::rest)) := by
    have hc : cat ((4*n+4)+1)=5 := by
      rw [show 4*n+4+1=4*n+5 by omega,cat_five]
    simpa [actualNext,hc] using cut_real_next ((4*n+4)::rest) h
  unfold delta
  apply List.mem_flatMap.mpr
  refine ⟨(5,rightSig rest), by simpa [mkControl] using hh, ?_⟩
  have hsat := big_odd_current s (n+1) (by omega)
    [true,true] hN hP
  have hlen : 2*(n+1)=2*n+2 := by omega
  rw [hlen] at hsat
  rw [hsat]
  simp [actionsFor,choicesA,mkControl]

theorem cat_six (n : Nat) : cat (4*n+6)=6 := by
  have h : ¬ 4*n+6≤4 := by omega
  simp only [cat,if_neg h]
  omega

theorem b_six_stay (s : SegmentSummary) (n : Nat) (rest : List Nat)
    (h : rightType (rightSig ((4*n+5)::rest)) ≠ 0) :
    Action.stay (mkControl true
      (prepend (altWord (2*n+1) ++ [true]) (rightSig rest))
      (segAppend s [true,true,true,true])) ∈
      delta (mkControl true (rightSig ((4*n+5)::rest)) s) := by
  have hh : (6,rightSig rest) ∈ cut (rightSig ((4*n+5)::rest)) := by
    have hc : cat ((4*n+5)+1)=6 := by
      rw [show 4*n+5+1=4*n+6 by omega,cat_six]
    simpa [actualNext,hc] using cut_real_next ((4*n+5)::rest) h
  unfold delta
  apply List.mem_flatMap.mpr
  refine ⟨(6,rightSig rest), by simpa [mkControl] using hh, ?_⟩
  have hsat := prepend_positive (n+1) (by omega) (rightSig rest)
  have hlen : 2*(n+1)-1 = 2*n+1 := by omega
  rw [hlen] at hsat
  rw [hsat]
  simp [actionsFor,choicesA,mkControl]

theorem c_six_pop (s : SegmentSummary)
    (hN : -1 ≤ s.imageN) (hP : -1 ≤ s.imageP)
    (n : Nat) (rest : List Nat)
    (h : rightType (rightSig ((4*n+5)::rest)) ≠ 0) :
    Action.pop (segConcat
      (segAppend s (altWord (2*n+2) ++ [true]))
        (rightSig rest)) ∈
      delta (mkControl false (rightSig ((4*n+5)::rest)) s) := by
  have hh : (6,rightSig rest) ∈ cut (rightSig ((4*n+5)::rest)) := by
    have hc : cat ((4*n+5)+1)=6 := by
      rw [show 4*n+5+1=4*n+6 by omega,cat_six]
    simpa [actualNext,hc] using cut_real_next ((4*n+5)::rest) h
  unfold delta
  apply List.mem_flatMap.mpr
  refine ⟨(6,rightSig rest), by simpa [mkControl] using hh, ?_⟩
  have hsat := big_odd_current s (n+1) (by omega) [true] hN hP
  have hlen : 2*(n+1)=2*n+2 := by omega
  rw [hlen] at hsat
  rw [hsat]
  simp [actionsFor,choicesA,mkControl]

#print axioms b_four_push
#print axioms c_four_stay
#print axioms b_five_push
#print axioms c_five_stay
#print axioms b_six_stay
#print axioms c_six_pop
end BB6.Agent5Q0151OuterAbstractActions
