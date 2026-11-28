import Q0151ScanNormalForm
import Q0151ConcatSound

set_option maxHeartbeats 0

/-!
Complete physical-word / finite-summary reconciliation for q0-151 stack
transfer. Every source-scannable segment ending in 1, appended to ANY
right-hand run word, has a canonical run-list representation. Its packed
tape bits are identical to the real transferred bits (including the
blank right exterior), and segConcat computes exactly that canonical
right-list signature. This is the exact all-length pop word bridge,
independent of experimental closure of the finite automaton.
-/

namespace BB6.Agent5Q0151TransferredWord
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151SegmentGrammar
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151SegmentRunSound
open BB6.Agent5Q0151ScanNormalForm
open BB6.Agent5Q0151ConcatSound
open BB6.Agent5Q0151FiniteModel
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper
open BB6.Agent5PackedSweep

theorem runBits_eq (xs : List Nat) : runBits xs = bitRuns xs := by
  induction xs with
  | nil => rfl
  | cons n ns ih =>
      simp [runBits,bitRuns,rr,ones,ih]

theorem merged_run (last first : Nat) (rest : List Nat) :
    List.replicate (last+1) true ++ runBits (first::rest) =
      runBits ((last+first+1)::rest) := by
  change List.replicate (last+1) true ++
        (List.replicate (first+1) true ++ false::runBits rest) =
      List.replicate (last+first+1+1) true ++ false::runBits rest
  rw [show last+first+1+1=(last+1)+(first+1) by omega]
  simp only [List.replicate_add,List.append_assoc]

theorem transfer_word (s : List Bool) (hs : SegGood s)
    (right : List Nat) :
    ∃ decoded : List Nat,
      pack (s ++ runBits right) = pack (runBits decoded) ∧
      segConcat (segAppend emptySegment s) (rightSig right) =
        rightSig decoded := by
  obtain ⟨closed,last,hseg,hsummary⟩ := segGood_summary s hs
  cases right with
  | nil =>
      refine ⟨closed++[last], ?_, ?_⟩
      · have he : runBits (closed++[last]) = s ++ [false] := by
          calc
            runBits (closed++[last]) =
                bitRuns closed ++ bitRuns [last] := by
              simp [runBits_eq,bitRuns_append]
            _ = bitRuns closed ++
                (List.replicate (last+1) true ++ [false]) := rfl
            _ = s ++ [false] := by
              rw [hseg]
              simp [List.append_assoc]
        change pack s = pack (runBits (closed++[last]))
        rw [he,pack_zero]
      · rw [hsummary,concat_run_summary]
        rfl
  | cons first rest =>
      refine ⟨closed++((last+first+1)::rest), ?_, ?_⟩
      · have he : s ++ runBits (first::rest) =
            runBits (closed++((last+first+1)::rest)) := by
          calc
            s ++ runBits (first::rest) =
                bitRuns closed ++
                  (List.replicate (last+1) true ++
                    runBits (first::rest)) := by
              rw [hseg]
              simp [List.append_assoc]
            _ = bitRuns closed ++
                runBits ((last+first+1)::rest) := by
              rw [merged_run]
            _ = runBits (closed++((last+first+1)::rest)) := by
              simp [runBits_eq,bitRuns_append]
        rw [he]
      · rw [hsummary,concat_run_summary]
        rfl

#print axioms runBits_eq
#print axioms merged_run
#print axioms transfer_word
end BB6.Agent5Q0151TransferredWord
