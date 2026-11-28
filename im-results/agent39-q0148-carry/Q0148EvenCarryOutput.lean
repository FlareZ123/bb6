import Q0148BoundarySweep

/-!
# Exact all-length even-gap transducer normal form for Raw11 q0-148

These are purely algebraic theorems about the ORIGINAL source-certified
three-carry transducer in Q0148BoundarySweep. In particular the block
normalization applies to any finite number of odd tape gaps. It does not
by itself prove the missing original-machine boundary-return theorem.
-/

namespace BB6.Agent39Q0148Carry
open BB6.Agent5Q0148BoundarySweep

def aRun : Nat → List LeftChunk
  | 0 => []
  | n+1 => .alternating :: aRun n

/-- In carry U, a run of As passes through unchanged; its final marker
    contributes two extra As and resets the carry to S. -/
theorem one_run_output (n : Nat) :
    carryFold .one (aRun n ++ [.separatedMarker]) =
      (aRun (n+2), .eleven) := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simpa [aRun, carryFold, carryStep, Nat.succ_add] using ih

/-- An even number of As followed by a marker passes through the
    S-state carry, moving the marker to the front without losing any As. -/
theorem even_run_output (n : Nat) :
    carryFold .eleven (aRun (2*n) ++ [.separatedMarker]) =
      (.separatedMarker :: aRun (2*n), .eleven) := by
  cases n with
  | zero => rfl
  | succ n =>
      have h := congrArg
        (fun z : List LeftChunk × Carry => (.separatedMarker :: z.1, z.2))
        (one_run_output (2*n))
      simpa [Nat.mul_succ, aRun, carryFold, carryStep] using h

/-- Universal concatenation law of the source three-carry transducer. -/
theorem fold_append (carry : Carry) (xs ys : List LeftChunk) :
    carryFold carry (xs ++ ys) =
      let first := carryFold carry xs
      let rest := carryFold first.2 ys
      (first.1 ++ rest.1, rest.2) := by
  induction xs generalizing carry with
  | nil => rfl
  | cons x xs ih =>
      cases carry <;> cases x <;>
        simp [carryFold, carryStep, ih, List.append_assoc]

/-- Alternating runs of even length, with one separator marker each. -/
def evenBlocks : List Nat → List LeftChunk
  | [] => []
  | n::ns => (aRun (2*n) ++ [.separatedMarker]) ++ evenBlocks ns

/-- Normal form of the same list, with each marker moved left across
    its adjoining even alternating run. -/
def normalizedBlocks : List Nat → List LeftChunk
  | [] => []
  | n::ns => (.separatedMarker :: aRun (2*n)) ++ normalizedBlocks ns

/-- Arbitrarily many even-gap marker blocks factor EXACTLY under
    carryFold: the returned carry is S and the emitted chunk list is
    explicitly normalized. No finite simulation limit or TM hypothesis. -/
theorem block_normalization_output (ns : List Nat) :
    carryFold .eleven (evenBlocks ns) =
      (normalizedBlocks ns, .eleven) := by
  induction ns with
  | nil => rfl
  | cons n ns ih =>
      simp [evenBlocks, normalizedBlocks, fold_append,
        even_run_output, ih]

/-- A trailing A^0 leaves carry S, corresponding to the a=1 branch. -/
theorem terminal_zero_output (ns : List Nat) :
    carryFold .eleven (evenBlocks ns ++ aRun 0) =
      (normalizedBlocks ns, .eleven) := by
  simpa [aRun] using block_normalization_output ns

/-- A trailing A^2 emits exactly one more marker and leaves carry U,
    corresponding to the a=3 branch of the proposed boundary return. -/
theorem terminal_two_output (ns : List Nat) :
    carryFold .eleven (evenBlocks ns ++ aRun 2) =
      (normalizedBlocks ns ++ [.separatedMarker], .one) := by
  rw [fold_append, block_normalization_output]
  rfl

#print axioms one_run_output
#print axioms even_run_output
#print axioms fold_append
#print axioms block_normalization_output
#print axioms terminal_zero_output
#print axioms terminal_two_output
end BB6.Agent39Q0148Carry
