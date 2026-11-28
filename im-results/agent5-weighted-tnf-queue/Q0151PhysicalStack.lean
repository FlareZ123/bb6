import Q0151MacroSteps

set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-!
Authentic-source bridge for q0-151's segment/marker stack. The abstract
segment word is stored in forward order. Its physical left tape is nearest
first, so the exact source embedding reverses the current segment and uses
two zero markers to delimit saved segments.

Theorems below transport the original BB6.Agent5Q0151SourceMacro.Goes
proofs, which are positive-length actual primitive-machine executions.
They are independent of the untrusted finite abstract certificate and
do not assert that every root trajectory has this form.
-/

namespace BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151SourceMacro
open BB6Coverage BB6Coverage.Agent31Pump BB6Coverage.Agent13PackedZipper
open BB6.Agent5PackedSweep

def marker : List Bool := [false,false]

def savedLeft : List (List Bool) → List Bool
  | [] => []
  | s :: ss => s.reverse ++ marker ++ savedLeft ss

def leftOf (s : List Bool) (ss : List (List Bool)) : List Bool :=
  s.reverse ++ marker ++ savedLeft ss

def boundary (q : Fin 6) (s : List Bool) (ss : List (List Bool))
    (right : List Bool) : P :=
  frame q (leftOf s ss) right

def tailWord (a : Nat) := alt a

theorem push_left (s newS : List Bool) (ss : List (List Bool)) :
    leftOf newS (s :: ss) = newS.reverse ++ marker ++ leftOf s ss := by
  simp [leftOf,savedLeft,List.append_assoc]

theorem add_suffix_left (s ext : List Bool) (ss : List (List Bool)) :
    leftOf (s ++ ext) ss = ext.reverse ++ leftOf s ss := by
  simp [leftOf,List.reverse_append,List.append_assoc]

theorem b_one (s : List Bool) (ss : List (List Bool)) (R : List Bool) :
    Goes (boundary 1 s ss (rr 1 R))
      (boundary 1 (s ++ [false,true]) ss R) := by
  simpa [boundary,add_suffix_left] using bOdd1 (leftOf s ss) R

theorem c_one (s : List Bool) (ss : List (List Bool)) (R : List Bool) :
    Goes (boundary 2 s ss (rr 1 R))
      (boundary 1 (s ++ [true,true]) ss R) := by
  simpa [boundary,add_suffix_left] using cOdd1 (leftOf s ss) R

theorem b_big_one (n : Nat) (s : List Bool) (ss : List (List Bool))
    (R : List Bool) :
    Goes (boundary 1 s ss (rr (4*n+5) R))
      (boundary 1 (alt (2*n+1) ++ [true,true]) (s :: ss) R) := by
  have h := bOddBig n (leftOf s ss) R
  simpa [boundary,push_left,marker,List.reverse_append,alt_reverse,
    List.append_assoc] using h

theorem c_big_one (n : Nat) (s : List Bool) (ss : List (List Bool))
    (R : List Bool) :
    Goes (boundary 2 s ss (rr (4*n+5) R))
      (boundary 1 (s ++ alt (2*n+2) ++ [true,true]) ss R) := by
  have h := cOddBig n (leftOf s ss) R
  simpa [boundary,leftOf,List.reverse_append,alt_reverse,List.append_assoc]
    using h

theorem b_zero (n : Nat) (s : List Bool) (ss : List (List Bool))
    (R : List Bool) :
    Goes (boundary 1 s ss (rr (4*n+4) R))
      (boundary 2 (alt (2*n) ++ [true,true,true]) (s :: ss) R) := by
  have h := bZero n (leftOf s ss) R
  simpa [boundary,push_left,marker,List.reverse_append,alt_reverse,
    List.append_assoc] using h

theorem c_zero (n : Nat) (s : List Bool) (ss : List (List Bool))
    (R : List Bool) :
    Goes (boundary 2 s ss (rr (4*n+4) R))
      (boundary 2 (s ++ alt (2*n+1) ++ [true,true,true]) ss R) := by
  have h := cZero n (leftOf s ss) R
  simpa [boundary,leftOf,List.reverse_append,alt_reverse,List.append_assoc]
    using h

theorem b_even_big (n : Nat) (s : List Bool)
    (ss : List (List Bool)) (R : List Bool) :
    Goes (boundary 1 s ss (rr (4*(n+1)+2) R))
      (boundary 1 (s ++ [true,true,true,true]) ss
        (alt (2*n+1) ++ true::R)) := by
  have h := bEvenBig n (leftOf s ss) R
  simpa [boundary,leftOf,List.reverse_append,List.append_assoc] using h

theorem saved_pop_left (s : List Bool) (ss : List (List Bool)) :
    leftOf (s ++ [true,true,true,true]) ss =
    [true,true,true,true] ++ savedLeft (s::ss) := by
  simp [leftOf,savedLeft,List.reverse_append,List.append_assoc]

theorem c_even_pop (n : Nat) (s saved : List Bool)
    (ss : List (List Bool)) (R : List Bool)
    (hs : Scan s.reverse) :
    Goes (boundary 2 s (saved::ss) (rr (4*n+2) R))
      (boundary 1 (saved ++ [true,true,true,true]) ss
        (s ++ alt (2*n) ++ true::R)) := by
  have h := cEven n s.reverse (savedLeft (saved::ss)) R hs
  simpa [boundary,leftOf,saved_pop_left,List.reverse_reverse,
    List.append_assoc] using h

theorem b_end_pop (s saved : List Bool) (ss : List (List Bool))
    (hs : Scan s.reverse) :
    Goes (boundary 1 s (saved::ss) [])
      (boundary 1 (saved ++ [true,true,true,true]) ss s) := by
  have h := bEnd s.reverse (savedLeft (saved::ss)) hs
  simpa [boundary,leftOf,saved_pop_left,List.reverse_reverse,
    List.append_assoc] using h

#print axioms b_one
#print axioms c_one
#print axioms b_big_one
#print axioms c_big_one
#print axioms b_zero
#print axioms c_zero
#print axioms b_even_big
#print axioms c_even_pop
#print axioms b_end_pop

end BB6.Agent5Q0151PhysicalStack
