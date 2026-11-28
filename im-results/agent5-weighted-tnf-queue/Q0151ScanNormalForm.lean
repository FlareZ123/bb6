import Q0151SegmentRunSound
import Q0151SegmentGrammar

set_option maxHeartbeats 0

/-!
Complete normal form of actual q0-151 left segments. Scan (s.reverse)
from the authenticated source macro is not merely an abstract
regular-language assumption: it exactly ensures a finite sequence of
positive runs followed by a possibly empty final run. For SegGood, the
final run is positive. Combined with Q0151SegmentRunSound this gives
a concrete witness for the abstract segment parser for EVERY admissible
physical stack segment, not a finite set of sampled words.
-/

namespace BB6.Agent5Q0151ScanNormalForm
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151SegmentRunSound
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151ConcatSound

theorem bitRuns_append (a b : List Nat) :
    bitRuns (a++b) = bitRuns a ++ bitRuns b := by
  induction a with
  | nil => rfl
  | cons n ns ih =>
      simp [bitRuns,ih,List.append_assoc]

theorem scan_normal (S : List Bool) (h : Scan S) :
    ∃ (closed : List Nat) (openCount : Nat),
      S.reverse = bitRuns closed ++ List.replicate openCount true := by
  induction h with
  | nil =>
      exact ⟨[],0,rfl⟩
  | @one xs _ ih =>
      obtain ⟨cl,k,hcl⟩ := ih
      refine ⟨cl,k+1,?_⟩
      calc
        (true::xs).reverse = xs.reverse ++ [true] := by simp
        _ = bitRuns cl ++ (List.replicate k true ++ [true]) := by
          rw [hcl]; simp [List.append_assoc]
        _ = bitRuns cl ++ List.replicate (k+1) true := by
          simp [List.replicate_succ',List.append_assoc]
  | @pair xs _ ih =>
      obtain ⟨cl,k,hcl⟩ := ih
      refine ⟨cl++[k],0,?_⟩
      calc
        (false::true::xs).reverse = xs.reverse ++ [true,false] := by simp
        _ = bitRuns cl ++ (List.replicate k true ++ [true,false]) := by
          rw [hcl]; simp [List.append_assoc]
        _ = bitRuns (cl++[k]) ++ List.replicate 0 true := by
          simp [bitRuns_append,bitRuns,List.replicate_succ',List.append_assoc]

theorem bitRuns_end (xs : List Nat) :
    xs = [] ∨ ∃ pref, bitRuns xs = pref ++ [false] := by
  induction xs with
  | nil => exact Or.inl rfl
  | cons n ns ih =>
      rcases ih with he | ⟨pref,hpref⟩
      · subst ns
        exact Or.inr ⟨List.replicate (n+1) true, by simp [bitRuns]⟩
      · exact Or.inr
          ⟨List.replicate (n+1) true ++ [false] ++ pref,
            by simp [bitRuns,hpref,List.append_assoc]⟩

theorem open_count_pos (cl : List Nat) (k : Nat) (u : List Bool)
    (he : bitRuns cl ++ List.replicate k true = u ++ [true]) :
    0 < k := by
  cases k with
  | zero =>
      simp at he
      rcases bitRuns_end cl with hnil | ⟨pref,hpref⟩
      · subst cl
        simp [bitRuns] at he
      · rw [hpref] at he
        have hrev := congrArg List.reverse he
        simp at hrev
  | succ n => omega

theorem segGood_normal (s : List Bool) (hs : SegGood s) :
    ∃ (closed : List Nat) (last : Nat),
      s = bitRuns closed ++ List.replicate (last+1) true := by
  obtain ⟨cl,k,hcl⟩ := scan_normal s.reverse hs.1
  have he : s = bitRuns cl ++ List.replicate k true := by
    simpa using hcl
  obtain ⟨u,hu⟩ := hs.2
  have hk : 0 < k := open_count_pos cl k u (by rw [← he,hu])
  refine ⟨cl,k-1,?_⟩
  have hsum : k-1+1 = k := by omega
  simpa [hsum] using he

theorem segGood_summary (s : List Bool) (hs : SegGood s) :
    ∃ (closed : List Nat) (last : Nat),
      s = bitRuns closed ++ List.replicate (last+1) true ∧
      segAppend emptySegment s = segmentOfRuns closed last := by
  obtain ⟨closed,last,h⟩ := segGood_normal s hs
  exact ⟨closed,last,h,by rw [h]; exact segmentBits_sound closed last⟩

#print axioms scan_normal
#print axioms bitRuns_end
#print axioms open_count_pos
#print axioms segGood_normal
#print axioms segGood_summary
end BB6.Agent5Q0151ScanNormalForm
