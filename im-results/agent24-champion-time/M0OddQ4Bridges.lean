import CountedQ4Prefix
import Lean.Elab.Tactic.Omega

/-!
# Finite bridges for the m=0 odd-n q4 prefix

The candidate m=0 odd-n prefix decomposes into a counted left sweep,
then finite bridges of lengths 3, 12, 9, and 3, followed by an E-state
scan of 3*(a-1) cells.  These are the four finite bridge kernels, stated
as exact original-TM63 runs and lifted to arbitrary tapes by bridgeAt.

The candidate cut is empirically:
  state 4 at h, left stream
    [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++ binDec L (n-1) ++ lh,
  right stream q4RightFacing b.
The complete prefix/suffix theorem is not asserted here.
-/

namespace BB6Coverage.Agent24M0OddQ4Bridges

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent6Q4Prefix

/-- First three-step bridge: state D at the end of the swept d1 block
moves left into the marker/d0 boundary. -/
def m0OddBridge3Inside (x : Int) : Bool := decide (-2 ≤ x ∧ x ≤ 0)
def m0OddBridge3Start : FConfig := ⟨3,0,[-1]⟩
def m0OddBridge3End : FConfig := ⟨2,-3,[]⟩

theorem m0OddBridge3_exact :
    fRun tm2 3 m0OddBridge3Start = some m0OddBridge3End := by decide

theorem m0OddBridge3_heads :
    (List.range 3).all (fun k =>
      match fRun tm2 k m0OddBridge3Start with
      | none => true
      | some f => m0OddBridge3Inside f.head) = true := by decide

theorem m0OddBridge3At (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, m0OddBridge3Inside x = true →
      T (h+x) = decide (x ∈ m0OddBridge3Start.marked)) :
    run tm2 3 ⟨3,h,T⟩ =
      some (frameAt T h m0OddBridge3Inside m0OddBridge3End) := by
  exact bridgeAt T h m0OddBridge3Inside
    m0OddBridge3Start m0OddBridge3End 3 rfl
    m0OddBridge3_exact m0OddBridge3_heads hmatch

/-- Twelve-step bridge from the state-C boundary to the state-B
right-facing phase. -/
def m0OddBridge12Inside (x : Int) : Bool := decide (-1 ≤ x ∧ x ≤ 3)
def m0OddBridge12Start : FConfig := ⟨2,0,[-1]⟩
def m0OddBridge12End : FConfig := ⟨1,0,[-1,1,2,3]⟩

theorem m0OddBridge12_exact :
    fRun tm2 12 m0OddBridge12Start = some m0OddBridge12End := by decide

theorem m0OddBridge12_heads :
    (List.range 12).all (fun k =>
      match fRun tm2 k m0OddBridge12Start with
      | none => true
      | some f => m0OddBridge12Inside f.head) = true := by decide

theorem m0OddBridge12At (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, m0OddBridge12Inside x = true →
      T (h+x) = decide (x ∈ m0OddBridge12Start.marked)) :
    run tm2 12 ⟨2,h,T⟩ =
      some (frameAt T h m0OddBridge12Inside m0OddBridge12End) := by
  exact bridgeAt T h m0OddBridge12Inside
    m0OddBridge12Start m0OddBridge12End 12 rfl
    m0OddBridge12_exact m0OddBridge12_heads hmatch

/-- Nine-step bridge shifts the state-B phase three cells right. -/
def m0OddBridge9Inside (x : Int) : Bool := decide (-3 ≤ x ∧ x ≤ 3)
def m0OddBridge9Start : FConfig := ⟨1,0,[-1,1,2,3]⟩
def m0OddBridge9End : FConfig := ⟨1,3,[-3,-2,-1,2,3]⟩

theorem m0OddBridge9_exact :
    fRun tm2 9 m0OddBridge9Start = some m0OddBridge9End := by decide

theorem m0OddBridge9_heads :
    (List.range 9).all (fun k =>
      match fRun tm2 k m0OddBridge9Start with
      | none => true
      | some f => m0OddBridge9Inside f.head) = true := by decide

theorem m0OddBridge9At (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, m0OddBridge9Inside x = true →
      T (h+x) = decide (x ∈ m0OddBridge9Start.marked)) :
    run tm2 9 ⟨1,h,T⟩ =
      some (frameAt T h m0OddBridge9Inside m0OddBridge9End) := by
  exact bridgeAt T h m0OddBridge9Inside
    m0OddBridge9Start m0OddBridge9End 9 rfl
    m0OddBridge9_exact m0OddBridge9_heads hmatch

/-- Final three-step bridge enters the E-state rightward scan. -/
def m0OddBridge3RightInside (x : Int) : Bool := decide (0 ≤ x ∧ x ≤ 2)
def m0OddBridge3RightStart : FConfig := ⟨1,0,[0,2]⟩
def m0OddBridge3RightEnd : FConfig := ⟨4,3,[1,2]⟩

theorem m0OddBridge3Right_exact :
    fRun tm2 3 m0OddBridge3RightStart =
      some m0OddBridge3RightEnd := by decide

theorem m0OddBridge3Right_heads :
    (List.range 3).all (fun k =>
      match fRun tm2 k m0OddBridge3RightStart with
      | none => true
      | some f => m0OddBridge3RightInside f.head) = true := by decide

theorem m0OddBridge3RightAt (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, m0OddBridge3RightInside x = true →
      T (h+x) = decide (x ∈ m0OddBridge3RightStart.marked)) :
    run tm2 3 ⟨1,h,T⟩ =
      some (frameAt T h m0OddBridge3RightInside m0OddBridge3RightEnd) := by
  exact bridgeAt T h m0OddBridge3RightInside
    m0OddBridge3RightStart m0OddBridge3RightEnd 3 rfl
    m0OddBridge3Right_exact m0OddBridge3Right_heads hmatch

#print axioms m0OddBridge3_exact
#print axioms m0OddBridge12_exact
#print axioms m0OddBridge9_exact
#print axioms m0OddBridge3Right_exact
#print axioms m0OddBridge3At
#print axioms m0OddBridge12At
#print axioms m0OddBridge9At
#print axioms m0OddBridge3RightAt

end BB6Coverage.Agent24M0OddQ4Bridges
