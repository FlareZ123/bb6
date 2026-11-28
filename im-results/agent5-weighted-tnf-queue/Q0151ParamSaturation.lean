import Q0151UnitRunSaturation

set_option maxHeartbeats 0

/-!
Parametric macro saturation for the q0-151 physical-source abstraction.
After at least one 10 pair, adding further complete 10 pairs cannot change
the two-mode segment summary. Consequently all arbitrarily large macro
multipliers in q0-151's source cases are represented by the small finite
interpreter choices: a=1 for positive alternation and a=2 when the source
branch has an exceptional zero-alternation case at a=1.
These are equalities of executable finite-summary functions, without any
finiteness/trust assumptions about a sampled source trajectory.
-/

namespace BB6.Agent5Q0151ParamSaturation
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151UnitRunSaturation

theorem alt_positive (s : SegmentSummary) (n : Nat)
    (hn : 0 < n) (suffix : List Bool)
    (hN : -1 ≤ s.imageN) (hP : -1 ≤ s.imageP) :
    segAppend s (altWord n ++ suffix) =
      segAppend s (altWord 1 ++ suffix) := by
  have he : n = (n-1)+1 := by omega
  rw [he,segAppend_append,segAppend_append]
  have h := segment_alt_saturation s hN hP (n-1)
  have hc := congrArg (fun v : SegmentSummary => segAppend v suffix) h
  simpa [altWord,List.replicate_one] using hc

theorem alt_positive_both (s : SegmentSummary) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) (suffix : List Bool)
    (hN : -1 ≤ s.imageN) (hP : -1 ≤ s.imageP) :
    segAppend s (altWord m ++ suffix) =
      segAppend s (altWord n ++ suffix) := by
  calc
    _ = segAppend s (altWord 1 ++ suffix) :=
      alt_positive s m hm suffix hN hP
    _ = _ := (alt_positive s n hn suffix hN hP).symm

theorem big_odd_new_segment (a : Nat) (ha : 1 ≤ a) :
    segAppend emptySegment (altWord (2*a-1) ++ [true,true]) =
      segAppend emptySegment (altWord 1 ++ [true,true]) := by
  exact alt_positive emptySegment (2*a-1) (by omega)
    [true,true] (by decide) (by decide)

theorem big_zero_new_segment (a : Nat) (ha : 2 ≤ a) :
    segAppend emptySegment
      (altWord (2*a-2) ++ [true,true,true]) =
      segAppend emptySegment
        (altWord 2 ++ [true,true,true]) := by
  exact alt_positive_both emptySegment (2*a-2) 2
    (by omega) (by decide) [true,true,true]
    (by decide) (by decide)

theorem big_odd_current (s : SegmentSummary) (a : Nat)
    (ha : 1 ≤ a) (tail : List Bool)
    (hN : -1 ≤ s.imageN) (hP : -1 ≤ s.imageP) :
    segAppend s (altWord (2*a) ++ tail) =
      segAppend s (altWord 2 ++ tail) := by
  exact alt_positive_both s (2*a) 2 (by omega) (by decide)
    tail hN hP

theorem big_zero_current (s : SegmentSummary) (a : Nat)
    (ha : 1 ≤ a) (tail : List Bool)
    (hN : -1 ≤ s.imageN) (hP : -1 ≤ s.imageP) :
    segAppend s (altWord (2*a-1) ++ tail) =
      segAppend s (altWord 1 ++ tail) := by
  exact alt_positive s (2*a-1) (by omega) tail hN hP

theorem prepend_positive (a : Nat) (ha : 1 ≤ a)
    (r : RightSummary) :
    prepend (altWord (2*a-1) ++ [true]) r =
      prepend (altWord 1 ++ [true]) r := by
  unfold prepend
  rw [alt_positive emptySegment (2*a-1) (by omega)
    [true] (by decide) (by decide)]

theorem two_zero_repair_positive (s : SegmentSummary)
    (a : Nat) (ha : 1 ≤ a) (tail : List Bool)
    (hN : -1 ≤ s.imageN) (hP : -1 ≤ s.imageP) :
    segAppend s ([true,true,true,false] ++
        altWord (2*a-1) ++ tail) =
      segAppend s ([true,true,true,false] ++
        altWord 1 ++ tail) := by
  have hstart : -1 ≤ (segAppend s [true,true,true,false]).imageN ∧
      -1 ≤ (segAppend s [true,true,true,false]).imageP := by
    have h0 : segAppend s [true,true,true,false] =
        segClosed {s with last :=
          plus (plus (plus s.last 1) 1) 1} := by
      rfl
    rw [h0]
    -- Every nonnegative or rejected mode is mapped to a mode >= -1.
    unfold segClosed
    split
    · exact ⟨by simpa using hN, by simpa using hP⟩
    · split
      · exact ⟨by decide,by decide⟩
      · exact ⟨dnext_lower s.imageN _ hN,
          dnext_lower s.imageP _ hP⟩
  simp only [List.append_assoc]
  rw [segAppend_append,segAppend_append]
  exact alt_positive (segAppend s [true,true,true,false])
    (2*a-1) (by omega) tail hstart.1 hstart.2

#print axioms alt_positive
#print axioms alt_positive_both
#print axioms big_odd_new_segment
#print axioms big_zero_new_segment
#print axioms big_odd_current
#print axioms big_zero_current
#print axioms prepend_positive
#print axioms two_zero_repair_positive
end BB6.Agent5Q0151ParamSaturation
