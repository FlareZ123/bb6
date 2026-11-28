import Q0151BlankStack
import Q0151PhysicalStackMore

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
The packed original tape has an inexhaustible zero tail.  Thus an empty
logical marker stack is physically indistinguishable from a stack with
one empty saved segment.  Reuse every authenticated nonempty-stack pop
macro at the empty-stack boundary instead of proving six more raw traces.
This concerns exact original-machine positive-length paths, not the
still-unproved finite abstraction refinement.
-/

namespace BB6.Agent5Q0151BlankStackMore
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151BlankStack
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper

theorem empty_as_virtual_saved (q : Fin 6) (s R : List Bool) :
    boundary q s [] R = boundary q s ([] :: []) R := by
  calc
    boundary q s [] R =
        frame q (s.reverse ++ [false,false]) R := by
          simp [boundary,leftOf,savedLeft,BB6.Agent5Q0151PhysicalStack.marker]
    _ = frame q ((s.reverse ++ [false,false]) ++ [false,false]) R :=
          (frame_trailing_marker q (s.reverse ++ [false,false]) R).symm
    _ = boundary q s ([] :: []) R := by
          simp [boundary,leftOf,savedLeft,BB6.Agent5Q0151PhysicalStack.marker,List.append_assoc]

theorem c_even_empty (n : Nat) (s R : List Bool)
    (hs : Scan s.reverse) :
    Goes (boundary 2 s [] (rr (4*n+2) R))
      (boundary 1 [true,true,true,true] [] (s ++ alt (2*n) ++ true::R)) := by
  rw [empty_as_virtual_saved 2 s (rr (4*n+2) R)]
  simpa only [List.nil_append] using (c_even_pop n s [] [] R hs)

theorem b_end_empty (s : List Bool) (hs : Scan s.reverse) :
    Goes (boundary 1 s [] [])
      (boundary 1 [true,true,true,true] [] s) := by
  rw [empty_as_virtual_saved 1 s []]
  simpa only [List.nil_append] using (b_end_pop s [] [] hs)

theorem c_end_empty (s : List Bool) (hs : Scan s.reverse) :
    Goes (boundary 2 (s ++ [true]) [] [])
      (boundary 1 [true,true,true,true] [] s) := by
  rw [empty_as_virtual_saved 2 (s ++ [true]) []]
  simpa only [List.nil_append] using (c_end_pop s [] [] hs)

theorem b_two_end_empty (s : List Bool) (hs : Scan s.reverse) :
    Goes (boundary 1 s [] (rr 2 []))
      (boundary 1 [true,true,true,true] []
        (s ++ [true,true,true,true])) := by
  rw [empty_as_virtual_saved 1 s (rr 2 [])]
  simpa only [List.nil_append] using (b_two_end_pop s [] [] hs)

theorem b_two_one_empty (s R : List Bool) (hs : Scan s.reverse) :
    Goes (boundary 1 s [] (rr 2 (rr 1 R)))
      (boundary 1 [true,true,true,true] [] (s ++ [true,true,true] ++ R)) := by
  rw [empty_as_virtual_saved 1 s (rr 2 (rr 1 R))]
  simpa only [List.nil_append] using (b_two_one_pop s [] [] R hs)

theorem b_two_big_one_empty (n : Nat) (s R : List Bool)
    (hs : Scan s.reverse) :
    Goes (boundary 1 s [] (rr 2 (rr (4*n+5) R)))
      (boundary 1 [true,true,true,true] []
        (s ++ [true,true,true,false] ++ alt (2*n+1) ++ true::R)) := by
  rw [empty_as_virtual_saved 1 s (rr 2 (rr (4*n+5) R))]
  simpa only [List.nil_append] using (b_two_big_one_pop n s [] [] R hs)

#print axioms empty_as_virtual_saved
#print axioms c_even_empty
#print axioms b_end_empty
#print axioms c_end_empty
#print axioms b_two_end_empty
#print axioms b_two_one_empty
#print axioms b_two_big_one_empty
end BB6.Agent5Q0151BlankStackMore
