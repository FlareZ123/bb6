import Q0151RightWordsComplete
import Q0151PhysicalStack
import Q0151SegmentRunSound

set_option maxHeartbeats 0

/-!
Original-machine to finite-interpreter transition refinement for the six
small non-repair q0-151 source branches: B/C reading first-run lengths
1,4,5. Each statement joins a genuine positive-length source execution
with membership of the matching action in the separately defined finite
delta interpreter. Unlike a global invariant, this does not assume the
symbolic state is reachable or that a finite abstract closure holds.
The only extra hypothesis is live right-suffix membership needed for an
honest finite cut. The unbounded parameter classes and B2/C2 repairs
are handled by separate all-length source/transfer lemmas.
-/

namespace BB6.Agent5Q0151SourceActions1
open BB6.Agent5Q0151SourceMacro
open BB6.Agent5Q0151PhysicalStack
open BB6.Agent5Q0151RightWords
open BB6.Agent5Q0151RightWordsComplete
open BB6.Agent5Q0151FiniteModel
open BB6.Agent5Q0151StackSaturation
open BB6.Agent5Q0151SegmentRunSound
open BB6.Agent5Q0151Category

def co (b : Bool) (s : List Bool) (runs : List Nat) : Control :=
  ⟨b,rightSig runs,segAppend emptySegment s⟩

theorem co_extend (b : Bool) (s ext : List Bool) (runs : List Nat) :
    co b (s++ext) runs =
      ⟨b,rightSig runs,segAppend (segAppend emptySegment s) ext⟩ := by
  simp [co,segAppend_append]

theorem action_of_cut (st : Control) (c : Nat) (r : RightSummary)
    (a : Action Control SegmentSummary RightSummary)
    (hcut : (c,r) ∈ cut st.right)
    (ha : a ∈ actionsFor st c r) : a ∈ delta st := by
  unfold delta
  exact List.mem_flatMap.mpr ⟨(c,r),hcut,ha⟩

theorem cut_n1 (rest : List Nat)
    (h : rightType (rightSig (0::rest)) ≠ 0) :
    (1,rightSig rest) ∈ cut (rightSig (0::rest)) := by
  simpa [cat,actualNext] using cut_real_next (0::rest) h

theorem cut_n4 (rest : List Nat)
    (h : rightType (rightSig (3::rest)) ≠ 0) :
    (4,rightSig rest) ∈ cut (rightSig (3::rest)) := by
  simpa [cat,actualNext] using cut_real_next (3::rest) h

theorem cut_n5 (rest : List Nat)
    (h : rightType (rightSig (4::rest)) ≠ 0) :
    (5,rightSig rest) ∈ cut (rightSig (4::rest)) := by
  simpa [cat,actualNext] using cut_real_next (4::rest) h

theorem alt_one : alt 1 = altWord 1 := by decide +kernel
theorem alt_two : alt 2 = altWord 2 := by decide +kernel

theorem b_one_refines (s : List Bool) (stack : List (List Bool))
    (rest : List Nat) (hlive : rightType (rightSig (0::rest)) ≠ 0) :
    Action.stay (co true (s++[false,true]) rest) ∈
      delta (co true s (0::rest)) ∧
    Goes (boundary 1 s stack (runBits (0::rest)))
      (boundary 1 (s++[false,true]) stack (runBits rest)) := by
  constructor
  · apply action_of_cut _ 1 (rightSig rest) _
      (by simpa [co] using cut_n1 rest hlive)
    rw [co_extend]
    simp [actionsFor,choicesA,co]
  · change Goes (boundary 1 s stack (rr 1 (runBits rest))) _
    exact b_one s stack (runBits rest)

theorem c_one_refines (s : List Bool) (stack : List (List Bool))
    (rest : List Nat) (hlive : rightType (rightSig (0::rest)) ≠ 0) :
    Action.stay (co true (s++[true,true]) rest) ∈
      delta (co false s (0::rest)) ∧
    Goes (boundary 2 s stack (runBits (0::rest)))
      (boundary 1 (s++[true,true]) stack (runBits rest)) := by
  constructor
  · apply action_of_cut _ 1 (rightSig rest) _
      (by simpa [co] using cut_n1 rest hlive)
    rw [co_extend]
    simp [actionsFor,choicesA,co]
  · change Goes (boundary 2 s stack (rr 1 (runBits rest))) _
    exact c_one s stack (runBits rest)

theorem b_four_refines (s : List Bool) (stack : List (List Bool))
    (rest : List Nat) (hlive : rightType (rightSig (3::rest)) ≠ 0) :
    Action.push (co false [true,true,true] rest)
      (segAppend emptySegment s) ∈ delta (co true s (3::rest)) ∧
    Goes (boundary 1 s stack (runBits (3::rest)))
      (boundary 2 [true,true,true] (s::stack) (runBits rest)) := by
  constructor
  · apply action_of_cut _ 4 (rightSig rest) _
      (by simpa [co] using cut_n4 rest hlive)
    simp [actionsFor,choicesA,co,altWord,segAppend]
  · change Goes (boundary 1 s stack (rr 4 (runBits rest))) _
    simpa [alt] using b_zero 0 s stack (runBits rest)

theorem c_four_refines (s : List Bool) (stack : List (List Bool))
    (rest : List Nat) (hlive : rightType (rightSig (3::rest)) ≠ 0) :
    Action.stay (co false
      (s++altWord 1++[true,true,true]) rest) ∈
      delta (co false s (3::rest)) ∧
    Goes (boundary 2 s stack (runBits (3::rest)))
      (boundary 2 (s++altWord 1++[true,true,true])
        stack (runBits rest)) := by
  constructor
  · apply action_of_cut _ 4 (rightSig rest) _
      (by simpa [co] using cut_n4 rest hlive)
    rw [co_extend]
    simp [actionsFor,choicesA,co,List.append_assoc]
  · change Goes (boundary 2 s stack (rr 4 (runBits rest))) _
    simpa only [alt_one] using c_zero 0 s stack (runBits rest)

theorem b_five_refines (s : List Bool) (stack : List (List Bool))
    (rest : List Nat) (hlive : rightType (rightSig (4::rest)) ≠ 0) :
    Action.push (co true (altWord 1++[true,true]) rest)
      (segAppend emptySegment s) ∈ delta (co true s (4::rest)) ∧
    Goes (boundary 1 s stack (runBits (4::rest)))
      (boundary 1 (altWord 1++[true,true])
        (s::stack) (runBits rest)) := by
  constructor
  · apply action_of_cut _ 5 (rightSig rest) _
      (by simpa [co] using cut_n5 rest hlive)
    simp [actionsFor,choicesA,co]
  · change Goes (boundary 1 s stack (rr 5 (runBits rest))) _
    simpa only [alt_one] using b_big_one 0 s stack (runBits rest)

theorem c_five_refines (s : List Bool) (stack : List (List Bool))
    (rest : List Nat) (hlive : rightType (rightSig (4::rest)) ≠ 0) :
    Action.stay (co true (s++altWord 2++[true,true]) rest) ∈
      delta (co false s (4::rest)) ∧
    Goes (boundary 2 s stack (runBits (4::rest)))
      (boundary 1 (s++altWord 2++[true,true])
        stack (runBits rest)) := by
  constructor
  · apply action_of_cut _ 5 (rightSig rest) _
      (by simpa [co] using cut_n5 rest hlive)
    rw [co_extend]
    simp [actionsFor,choicesA,co,List.append_assoc]
  · change Goes (boundary 2 s stack (rr 5 (runBits rest))) _
    simpa only [alt_two] using c_big_one 0 s stack (runBits rest)

#print axioms action_of_cut
#print axioms b_one_refines
#print axioms c_one_refines
#print axioms b_four_refines
#print axioms c_four_refines
#print axioms b_five_refines
#print axioms c_five_refines
end BB6.Agent5Q0151SourceActions1
