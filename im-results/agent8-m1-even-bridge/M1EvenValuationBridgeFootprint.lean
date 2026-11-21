import M1EvenValuationBridge
import S1Encoder
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent8M1EvenValuationBridgeFootprint

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48M1EvenValuationBridge
open BB6Coverage.Agent48M1EvenValuationSweep
open BB6Coverage.Agent24M1EvenValuationBridge
open BB6Coverage.Agent8S1Encoder

private theorem d0pow_length (n : Nat) : (d0pow n).length = 3*n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [d0pow,d0,ih,Nat.mul_succ]

private theorem sideBit_append_after (xs ys : List Bool) (i : Nat)
    (hi : xs.length ≤ i) :
    sideBit (xs ++ ys) i = sideBit ys (i-xs.length) := by
  induction xs generalizing i with
  | nil => simp
  | cons x xs ih =>
      cases i with
      | zero => simp at hi
      | succ i =>
          simp only [List.cons_append, sideBit]
          have hi' : xs.length ≤ i := by simp at hi; omega
          simpa using ih i hi'

/-- The valuation macro leaves the entire tape strictly to the left of its
    three-cell setup window untouched. -/
theorem m1EvenValuationBridgeTape_preserves_far_left
    (v : Nat) (T : Int → Bool) (h x : Int)
    (hx : x < h - ((3*(v+1)+3 : Nat) : Int)) :
    m1EvenValuationBridgeTape v T h x = T x := by
  let N : Nat := 3*(v+1)
  let x0 : Int := h-(N:Int)
  let Tleft : Int → Bool := state1SweptLeft N T h
  let Tsetup : Int → Bool := valuationSetupTape Tleft x0
  let Tright : Int → Bool := state5SweptRight (v+1) Tsetup (x0+1)
  have hleft : Tleft x = T x := by
    dsimp [Tleft]
    apply state1SweptLeft_preserves_left N T h x
    dsimp [N,x0] at hx ⊢
    omega
  have hsetup : Tsetup x = Tleft x := by
    dsimp [Tsetup,valuationSetupTape]
    have hne0 : x ≠ x0 := by dsimp [x0,N]; omega
    have hne1 : x ≠ x0-1 := by dsimp [x0,N]; omega
    have hne2 : x ≠ x0-2 := by dsimp [x0,N]; omega
    have hne3 : x ≠ x0-3 := by dsimp [x0,N]; omega
    simp [hne0,hne1,hne2,hne3]
  have hright : Tright x = Tsetup x := by
    dsimp [Tright]
    apply state5SweptRight_preserves_left (v+1) Tsetup (x0+1) x
    dsimp [x0,N] at hx ⊢
    omega
  have hexit : valuationExit1Tape Tright (h+1) x = Tright x := by
    simp [valuationExit1Tape]
    dsimp [x0,N] at hx ⊢
    omega
  unfold m1EvenValuationBridgeTape
  change valuationExit1Tape Tright (h+1) x = T x
  rw [hexit,hright,hsetup,hleft]

/-- Index form used by the source's left-facing stream: every cell at
    distance at least N+4 to the left of the original head is untouched. -/
theorem m1EvenValuationBridgeTape_preserves_left_index
    (v : Nat) (T : Int → Bool) (h : Int) (i : Nat)
    (hi : 3*(v+1)+4 ≤ i) :
    m1EvenValuationBridgeTape v T h (h-(i:Int)) = T (h-(i:Int)) := by
  apply m1EvenValuationBridgeTape_preserves_far_left
  dsimp
  omega

def m1BridgeInputPrefix (v : Nat) : List Bool :=
  [false,true,true,true,true] ++ d1pow v ++ d0

def m1BridgeOutputPrefix (v : Nat) : List Bool :=
  [false,true] ++ d0 ++ d0pow v ++ d1

/-- The source and target left-facing streams agree from the last prefix
    cell onward: at distance N+4 both final prefix bits are true, and from
    N+5 onward both streams are the same untouched tail. -/
theorem m1BridgeStreams_agree_after_boundary
    (v : Nat) (tail : List Bool) (i : Nat)
    (hi : 3*(v+1)+4 ≤ i) :
    sideBit (m1BridgeInputPrefix v ++ tail) i =
      sideBit (m1BridgeOutputPrefix v ++ tail) i := by
  let N : Nat := 3*(v+1)
  have hInputHead : ([false,true,true,true,true] ++ d1pow v).length = N+2 := by
    simp [N,d1pow_length]
    omega
  have hOutputHead : ([false,true] ++ d0 ++ d0pow v).length = N+2 := by
    simp [N,d0,d0pow_length]
    omega
  have hInputLen : (m1BridgeInputPrefix v).length = N+5 := by
    simp [m1BridgeInputPrefix,d0,N,d1pow_length]
    omega
  have hOutputLen : (m1BridgeOutputPrefix v).length = N+5 := by
    simp [m1BridgeOutputPrefix,d0,d1,N,d0pow_length]
    omega
  by_cases hboundary : i=N+4
  · subst i
    have hInput := sideBit_append_after
      ([false,true,true,true,true] ++ d1pow v) (d0 ++ tail) (N+4)
      (by rw [hInputHead]; omega)
    have hOutput := sideBit_append_after
      ([false,true] ++ d0 ++ d0pow v) (d1 ++ tail) (N+4)
      (by rw [hOutputHead]; omega)
    rw [show m1BridgeInputPrefix v ++ tail =
      ([false,true,true,true,true] ++ d1pow v) ++ (d0 ++ tail) by
        simp [m1BridgeInputPrefix,List.append_assoc],
      show m1BridgeOutputPrefix v ++ tail =
      ([false,true] ++ d0 ++ d0pow v) ++ (d1 ++ tail) by
        simp [m1BridgeOutputPrefix,List.append_assoc]]
    rw [hInput,hOutput]
    have hidx1 : N+4 - ([false,true,true,true,true] ++ d1pow v).length = 2 := by
      rw [hInputHead]
      omega
    have hidx2 : N+4 - ([false,true] ++ d0 ++ d0pow v).length = 2 := by
      rw [hOutputHead]
      omega
    rw [hidx1,hidx2]
    simp [sideBit,d0,d1]
  · have htail : N+5 ≤ i := by omega
    have hInput := sideBit_append_after (m1BridgeInputPrefix v) tail i
      (by rw [hInputLen]; omega)
    have hOutput := sideBit_append_after (m1BridgeOutputPrefix v) tail i
      (by rw [hOutputLen]; omega)
    rw [hInput,hOutput,hInputLen,hOutputLen]

/-- The far-left tail case in the source's left-facing bridge theorem
    follows from footprint preservation plus equality of the two streams. -/
theorem m1EvenValuationBridgeLeftFacing_tail
    (v : Nat) (T : Int → Bool) (h : Int) (tail : List Bool) (i : Nat)
    (hleft : ∀ j : Nat,
      T (h-(j:Int)) = sideBit (m1BridgeInputPrefix v ++ tail) j)
    (hi : 3*(v+1)+4 ≤ i) :
    m1EvenValuationBridgeTape v T h (h-(i:Int)) =
      sideBit (m1BridgeOutputPrefix v ++ tail) i := by
  calc
    m1EvenValuationBridgeTape v T h (h-(i:Int)) = T (h-(i:Int)) :=
      m1EvenValuationBridgeTape_preserves_left_index v T h i hi
    _ = sideBit (m1BridgeInputPrefix v ++ tail) i := hleft i
    _ = sideBit (m1BridgeOutputPrefix v ++ tail) i :=
      m1BridgeStreams_agree_after_boundary v tail i hi


/-- This statement uses the literal input and output stream expressions
    from the current parent source file, confirming that the helper can be
    applied without changing its local stream hypothesis. -/
theorem m1EvenValuationBridgeLeftFacing_tail_exact_parent_type
    (v : Nat) (T : Int → Bool) (h : Int) (tail : List Bool) (i : Nat)
    (hleft : ∀ j : Nat,
      T (h-(j:Int)) =
        sideBit ([false,true,true,true,true] ++ d1pow v ++ d0 ++ tail) j)
    (hi : 3*(v+1)+4 ≤ i) :
    m1EvenValuationBridgeTape v T h (h-(i:Int)) =
      sideBit ([false,true] ++ d0 ++ d0pow v ++ d1 ++ tail) i := by
  exact m1EvenValuationBridgeLeftFacing_tail v T h tail i hleft hi

/-- The full macro footprint is contained in the half-open interval from
    three cells left of the left-sweep endpoint through the first two cells
    to the right of the original head. -/
theorem m1EvenValuationBridgeTape_outside_footprint
    (v : Nat) (T : Int → Bool) (h x : Int)
    (hx : x < h - ((3*(v+1)+3 : Nat) : Int) ∨ h+2 ≤ x) :
    m1EvenValuationBridgeTape v T h x = T x := by
  rcases hx with hleft | hright
  · exact m1EvenValuationBridgeTape_preserves_far_left v T h x hleft
  · exact m1EvenValuationBridgeTape_preserves_right v T h x hright

#print axioms m1EvenValuationBridgeTape_preserves_far_left
#print axioms m1EvenValuationBridgeTape_preserves_left_index
#print axioms m1BridgeStreams_agree_after_boundary
#print axioms m1EvenValuationBridgeLeftFacing_tail
#print axioms m1EvenValuationBridgeLeftFacing_tail_exact_parent_type
#print axioms m1EvenValuationBridgeTape_outside_footprint

end BB6Coverage.Agent8M1EvenValuationBridgeFootprint
