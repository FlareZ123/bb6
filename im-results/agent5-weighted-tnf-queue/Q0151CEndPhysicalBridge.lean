import Q0151ScanNormalForm

set_option maxHeartbeats 0

/-!
Exact C-end source bridge. The finite C-mode interpreter allows an
empty-right pop only when the current segment's final run category is 3.
To use the original-machine C-end macro this numeric condition must imply
that the *actual physical segment* ends in precisely three one bits, with
a source-scannable prefix. The theorem below supplies that unbounded
converse (for any number of earlier closed runs) and shows that physically
removing one final one is exactly the interpreter's last:=2 update.
Not an experimental or bounded-segment claim.
-/

namespace BB6.Agent5Q0151CEndPhysicalBridge
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151SegmentRunSound
open BB6.Agent5Q0151ScanNormalForm
open BB6.Agent5Q0151ConcatSound
open BB6.Agent5Q0151Category
open BB6.Agent5Q0151FiniteModel

theorem scan_true_replicate (n : Nat) : Scan (List.replicate n true) := by
  induction n with
  | zero => exact Scan.nil
  | succ n ih => exact Scan.one ih

theorem scan_closed_bits (closed : List Nat) :
    Scan (bitRuns closed).reverse := by
  induction closed with
  | nil => exact Scan.nil
  | cons n ns ih =>
      have hrun : Scan (false :: List.replicate (n+1) true) := by
        simpa only [List.replicate_succ] using
          (Scan.pair (scan_true_replicate n))
      change Scan ((List.replicate (n+1) true ++ false::bitRuns ns).reverse)
      simpa [List.reverse_append,List.reverse_cons,List.reverse_replicate,
        List.append_assoc] using (Scan.append ih hrun)

theorem cat_three_exact (n : Nat) (h : cat (n+1) = 3) : n = 2 := by
  by_cases hs : n+1 ≤ 4
  · have hc : cat (n+1) = n+1 := by simp [cat,hs]
    omega
  · have hl : 5 ≤ cat (n+1) := by simp [cat,hs]
    omega

theorem c_end_trim_exact (s : List Bool) (hs : SegGood s)
    (hend : (segAppend emptySegment s).last = 3) :
    ∃ pref : List Bool,
      s = pref ++ [true] ∧ Scan pref.reverse ∧
      segAppend emptySegment pref =
        {segAppend emptySegment s with last := 2} := by
  obtain ⟨closed,last,hbits,hsummary⟩ := segGood_summary s hs
  have hlast : cat (last+1) = 3 := by
    rw [hsummary] at hend
    cases closed <;> simpa [segmentOfRuns,runCat] using hend
  have he : last = 2 := cat_three_exact last hlast
  subst last
  let pref := bitRuns closed ++ [true,true]
  have hpref : s = pref ++ [true] := by
    rw [hbits]
    simp [pref,List.append_assoc]
  have hscan : Scan pref.reverse := by
    have h := Scan.append (Scan.one (Scan.one Scan.nil))
      (scan_closed_bits closed)
    simpa [pref,List.reverse_append,List.append_assoc] using h
  refine ⟨pref,hpref,hscan,?_⟩
  have hp : segAppend emptySegment pref = segmentOfRuns closed 1 := by
    simpa [pref] using segmentBits_sound closed 1
  have hnow : segAppend emptySegment s = segmentOfRuns closed 2 := by
    rw [hbits]
    simpa using segmentBits_sound closed 2
  rw [hp,hnow]
  cases closed <;> rfl

#print axioms scan_closed_bits
#print axioms cat_three_exact
#print axioms c_end_trim_exact
end BB6.Agent5Q0151CEndPhysicalBridge
