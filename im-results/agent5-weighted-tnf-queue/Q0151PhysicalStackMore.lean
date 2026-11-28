import Q0151PhysicalStack

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151SourceMacro
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper
open BB6.Agent5PackedSweep

/-- Actual blank-root A0→B macro entry; F0 is not encountered. -/
theorem blank_seed :
    runP p 1 startP = some (boundary 1 [true] [] []) := by
  decide +kernel

theorem frame_left_zero (q : Fin 6) (L R : List Bool) :
    frame q (L ++ [false]) R = frame q L R := by
  unfold frame encode0
  simp [pack_zero,List.cons_append,List.append_assoc]

theorem frame_left_two_zero (q : Fin 6) (L R : List Bool) :
    frame q (L ++ marker) R = frame q L R := by
  simp [marker,List.append_assoc,frame_left_zero]

theorem empty_pop_left :
    boundary 1 [true,true,true,true] [] [] =
      frame 1 [true,true,true,true] [] := by
  simpa [boundary,leftOf,savedLeft,List.reverse_cons,marker]
    using frame_left_two_zero 1 [true,true,true,true] []

theorem b_two_zero (n : Nat) (s : List Bool) (ss : List (List Bool))
    (R : List Bool) :
    Goes (boundary 1 s ss (rr 2 (rr (4*n+4) R)))
      (boundary 1 (s ++ [true,true,true,false] ++ alt (2*n+1) ++ [true,true])
        ss R) := by
  have h := bTwoZero n s.reverse (savedLeft ss) R
  simpa [boundary,leftOf,List.reverse_append,alt_reverse,List.append_assoc]
    using h

theorem b_two_end_pop (s saved : List Bool) (ss : List (List Bool))
    (hs : Scan s.reverse) :
    Goes (boundary 1 s (saved::ss) (rr 2 []))
      (boundary 1 (saved ++ [true,true,true,true]) ss
        (s ++ [true,true,true,true])) := by
  have h := bTwoEnd s.reverse (savedLeft (saved::ss)) hs
  simpa [boundary,leftOf,saved_pop_left,List.reverse_reverse,List.append_assoc]
    using h

theorem b_two_one_pop (s saved : List Bool) (ss : List (List Bool))
    (R : List Bool) (hs : Scan s.reverse) :
    Goes (boundary 1 s (saved::ss) (rr 2 (rr 1 R)))
      (boundary 1 (saved ++ [true,true,true,true]) ss
        (s ++ [true,true,true] ++ R)) := by
  have h := bTwoOdd1 s.reverse (savedLeft (saved::ss)) R hs
  simpa [boundary,leftOf,saved_pop_left,List.reverse_reverse,List.append_assoc]
    using h

theorem b_two_big_one_pop (n : Nat) (s saved : List Bool)
    (ss : List (List Bool)) (R : List Bool)
    (hs : Scan s.reverse) :
    Goes (boundary 1 s (saved::ss) (rr 2 (rr (4*n+5) R)))
      (boundary 1 (saved ++ [true,true,true,true]) ss
        (s ++ [true,true,true,false] ++ alt (2*n+1) ++ true::R)) := by
  have h := bTwoOddBig n s.reverse (savedLeft (saved::ss)) R hs
  simpa [boundary,leftOf,saved_pop_left,List.reverse_reverse,List.append_assoc]
    using h

theorem c_end_pop (s saved : List Bool) (ss : List (List Bool))
    (hs : Scan s.reverse) :
    Goes (boundary 2 (s ++ [true]) (saved::ss) [])
      (boundary 1 (saved ++ [true,true,true,true]) ss s) := by
  have h := cEnd s.reverse (savedLeft (saved::ss)) hs
  simpa [boundary,leftOf,saved_pop_left,List.reverse_append,
    List.reverse_reverse,List.append_assoc] using h

theorem b_end_pop_empty (s : List Bool) (hs : Scan s.reverse) :
    Goes (boundary 1 s [] [])
      (boundary 1 [true,true,true,true] [] s) := by
  have h := bEnd s.reverse [] hs
  have ht : frame 1 [true,true,true,true] s =
      boundary 1 [true,true,true,true] [] s := by
    simpa [boundary,leftOf,savedLeft,List.reverse_append,marker]
      using (frame_left_two_zero 1 [true,true,true,true] s).symm
  simpa [boundary,leftOf,savedLeft,marker,List.reverse_reverse,
    List.append_assoc,ht] using h

#print axioms blank_seed
#print axioms b_two_zero
#print axioms b_two_end_pop
#print axioms b_two_one_pop
#print axioms b_two_big_one_pop
#print axioms c_end_pop
#print axioms b_end_pop_empty

end BB6.Agent5Q0151PhysicalStack
