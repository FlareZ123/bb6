import CountedCarryBoundaryTraces
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48Champion

set_option maxHeartbeats 1000000

/-!
# Counted binary-carry prefix

This module strengthens the fixed carry-boundary traces in Agent 42's
module by leaving the final E-head cell outside the D-tail frame.  That
cell is the first cell of the source's right unary counter, so it must be
preserved rather than assumed blank.
-/

/-- The D-tail's last head is reached but is not queried.  The true read
window is therefore offsets 0 through 8, not 0 through 9. -/
def carryDTail15OpenArea (x : Int) : Bool := decide (0 ≤ x ∧ x ≤ 8)

theorem carryDTail15Open_trace (bg : Int → Bool) :
    run tm2 15
      (frame carryDTail15OpenArea bg (embed carryDTail15Base)) =
    some (frame carryDTail15OpenArea bg (embed carryDTail15Final)) := by
  have he : fRun tm2 15 carryDTail15Base = some carryDTail15Final := by decide
  have hc : (List.range 15).all (fun k =>
      match fRun tm2 k carryDTail15Base with
      | none => true
      | some z => carryDTail15OpenArea z.head) = true := by decide
  rw [run_frame tm2 carryDTail15OpenArea bg (embed carryDTail15Base) 15
    (finite_heads tm2 carryDTail15OpenArea carryDTail15Base 15 hc)]
  rw [← finite_run_source tm2 15 carryDTail15Base, he]
  rfl

/-- Exact D-tail15 trace with an arbitrary bit at the final E head. -/
theorem carryDTail15_openEnd (T : Int → Bool) (h : Int)
    (hlocal : ∀ x, carryDTail15OpenArea (x-h) = true →
      (embed carryDTail15Base).tape (x-h) = T x) :
    run tm2 15 ⟨3,h,T⟩ =
      some (frame (fun x => carryDTail15OpenArea (x-h)) T
        (shiftConfig h (embed carryDTail15Final))) := by
  have hmain := carryBridgeLift carryDTail15OpenArea
    (embed carryDTail15Base) (embed carryDTail15Final) 15
    carryDTail15Open_trace T h hlocal
  simpa [embed, carryDTail15Base, shiftConfig] using hmain

/-- Three final moves after the short rho=3 return: A/0, B/1, F/0,
ending at E on the next (unqueried) cell. -/
def carryA3Area (x : Int) : Bool := decide (0 ≤ x ∧ x ≤ 2)
def carryA3Base : FConfig := ⟨0, 0, [1]⟩
def carryA3Final : FConfig := ⟨4, 3, [2,0]⟩

theorem carryA3_trace (bg : Int → Bool) :
    run tm2 3 (frame carryA3Area bg (embed carryA3Base)) =
      some (frame carryA3Area bg (embed carryA3Final)) := by
  have he : fRun tm2 3 carryA3Base = some carryA3Final := by decide
  have hc : (List.range 3).all (fun k =>
      match fRun tm2 k carryA3Base with
      | none => true
      | some z => carryA3Area z.head) = true := by decide
  rw [run_frame tm2 carryA3Area bg (embed carryA3Base) 3
    (finite_heads tm2 carryA3Area carryA3Base 3 hc)]
  rw [← finite_run_source tm2 3 carryA3Base, he]
  rfl

theorem carryA3 (T : Int → Bool) (h : Int)
    (hlocal : ∀ x, carryA3Area (x-h) = true →
      (embed carryA3Base).tape (x-h) = T x) :
    run tm2 3 ⟨0,h,T⟩ =
      some (frame (fun x => carryA3Area (x-h)) T
        (shiftConfig h (embed carryA3Final))) := by
  have hmain := carryBridgeLift carryA3Area
    (embed carryA3Base) (embed carryA3Final) 3 carryA3_trace T h hlocal
  simpa [embed, carryA3Base, shiftConfig] using hmain

/-- A contiguous run of ones, expressed in one-cell coordinates. -/
def carrySegmentOnes (T : Int → Bool) (h : Int) (n : Nat) : Prop :=
  ∀ i : Nat, i<n → T (h+(i:Int)) = true

/-- A one-cell segment of length 3n supplies n complete three-cell blocks. -/
theorem rightOnes_of_segment (n : Nat) (T : Int → Bool) (h : Int)
    (hseg : carrySegmentOnes T h (3*n)) : rightOnes T h n := by
  intro i hi
  have h0 := hseg (3*i) (by omega)
  have h1 := hseg (3*i+1) (by omega)
  have h2 := hseg (3*i+2) (by omega)
  have e1 : h+(3*(i:Int)+1) = h+3*(i:Int)+1 := by omega
  have e2 : h+(3*(i:Int)+2) = h+3*(i:Int)+2 := by omega
  exact ⟨by simpa using h0, by simpa [e1] using h1, by simpa [e2] using h2⟩

/-- The right sweep changes only cells strictly before its final head. -/
theorem sweptRight_future (n : Nat) (T : Int → Bool) (h x : Int)
    (hx : h+3*(n:Int) ≤ x) :
    sweptRight n T h x = T x := by
  induction n generalizing T h with
  | zero =>
      simp [sweptRight]
  | succ n ih =>
      have hx' : h+3+3*(n:Int) ≤ x := by omega
      have hrec := ih (afterRight3 T h) (h+3) hx'
      have h1 : x ≠ h+1 := by omega
      have h2 : x ≠ h+2 := by omega
      simpa [sweptRight, afterRight3, h1, h2] using hrec

/-- Seven ones immediately after a counted right sweep survive unchanged. -/
theorem sweptRight_keeps_seven (n : Nat) (T : Int → Bool) (h : Int)
    (hseg : carrySegmentOnes T h (3*n+7)) :
    ∀ i : Nat, i<7 →
      sweptRight n T h (h+3*(n:Int)+(i:Int)) = true := by
  intro i hi
  have hx : h+3*(n:Int) ≤ h+3*(n:Int)+(i:Int) := by omega
  rw [sweptRight_future n T h _ hx]
  have hval := hseg (3*n+i) (by omega)
  have heq : h+3*(n:Int)+(i:Int) = h+((3*n+i:Int)) := by omega
  simpa [heq] using hval

/-- The first two cells after the seven-cell terminal run are untouched by
the counted right sweep. -/
theorem sweptRight_keeps_two_zeroes (n : Nat) (T : Int → Bool) (h : Int)
    (h0 : T (h+3*(n:Int)+7) = false)
    (h1 : T (h+3*(n:Int)+8) = false) :
    sweptRight n T h (h+3*(n:Int)+7) = false ∧
    sweptRight n T h (h+3*(n:Int)+8) = false := by
  have hx0 : h+3*(n:Int) ≤ h+3*(n:Int)+7 := by omega
  have hx1 : h+3*(n:Int) ≤ h+3*(n:Int)+8 := by omega
  rw [sweptRight_future n T h _ hx0, sweptRight_future n T h _ hx1]
  exact ⟨h0,h1⟩


/-- The exact source-facing tape window before the counted carry prefix. -/
def carryInputArea (r : Nat) (x : Int) : Bool :=
  decide (-(3*(r:Int))-2 ≤ x ∧ x ≤ 6)

def carryInputBit (r : Nat) (x : Int) : Bool :=
  decide (x = -(3*(r:Int))-2 ∨
    (-(3*(r:Int))+1 ≤ x ∧ x ≤ 0) ∨ x=2 ∨ x=3 ∨ x=4)

/-- A bit in the unary run or in the fixed 111 guard is one. -/
theorem carryInput_marked (r : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea r x = true → T x = carryInputBit r x)
    (x : Int)
    (hmarked : (-(3*(r:Int))+1 ≤ x ∧ x ≤ 0) ∨ x=2 ∨ x=3 ∨ x=4) :
    T x = true := by
  have harea : carryInputArea r x = true := by
    simp [carryInputArea]
    rcases hmarked with h | h | h | h <;> omega
  have hbit : carryInputBit r x = true := by
    simp [carryInputBit]
    rcases hmarked with h | h | h | h <;> omega
  rw [hmatch x harea, hbit]

/-- Any unmarked cell in the source input window is blank. -/
theorem carryInput_unmarked (r : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea r x = true → T x = carryInputBit r x)
    (x : Int) (hlo : -(3*(r:Int))-2 ≤ x) (hhi : x ≤ 6)
    (hnot : ¬ (x = -(3*(r:Int))-2 ∨
      (-(3*(r:Int))+1 ≤ x ∧ x ≤ 0) ∨ x=2 ∨ x=3 ∨ x=4)) :
    T x = false := by
  have harea : carryInputArea r x = true := by
    simp [carryInputArea]
    omega
  have hbit : carryInputBit r x = false := by
    simp [carryInputBit, hnot]
  rw [hmatch x harea, hbit]

/-- The left source word supplies exactly the cells required by the
first 4s left-sweep transitions. -/
theorem carryInput_leftOnes (r s : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea r x = true → T x = carryInputBit r x)
    (hbound : 4*s ≤ 3*r) : leftOnes T 0 (4*s) := by
  intro i hi
  have hmarked : (-(3*(r:Int))+1 ≤ -(i:Int) ∧ -(i:Int) ≤ 0) := by
    constructor <;> omega
  simpa using carryInput_marked r T hmatch (-(i:Int)) (Or.inl hmarked)

/-- Closed form for a nonempty left sweep over 4s cells. -/
theorem carryLeftSweep_closed (s : Nat) (T : Int → Bool)
    (hs : 0 < s) (hon : leftOnes T 0 (4*s)) (hzero : T 1 = false) :
    sweptLeft (4*s) T 0 =
      (fun x => if x = 1-4*(s:Int) then false else
        if x=1 then true else T x) := by
  have hn : (4*s-1)+1 = 4*s := by omega
  have hon' : leftOnes T 0 ((4*s-1)+1) := by simpa [hn] using hon
  have h := swept_closed (4*s-1) T 0 hon' hzero
  have hcoord : (0:Int)-((4*s-1:Int)) = 1-4*(s:Int) := by omega
  rw [hcoord] at h
  exact h

/-- Every cell from the post-sweep head+2 through coordinate 4 is one. -/
theorem carryLeftSweep_marked (r s : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea r x = true → T x = carryInputBit r x)
    (hs : 0 < s) (hbound : 4*s ≤ 3*r)
    (x : Int) (hlo : 2-4*(s:Int) ≤ x) (hhi : x ≤ 4) :
    sweptLeft (4*s) T 0 x = true := by
  have hon := carryInput_leftOnes r s T hmatch hbound
  have hzero : T 1 = false := by
    exact carryInput_unmarked r T hmatch 1 (by omega) (by omega) (by
      simp [carryInputBit]; omega)
  have hclosed := carryLeftSweep_closed s T hs hon hzero
  rw [hclosed]
  by_cases hx1 : x=1
  · have hxb : (1:Int) ≠ 1-4*(s:Int) := by omega
    simp [hx1,hxb]
  · have hxb : x ≠ 1-4*(s:Int) := by omega
    simp [hx1,hxb]
    by_cases hx0 : x ≤ 0
    · apply carryInput_marked r T hmatch
      exact Or.inl ⟨by omega,hx0⟩
    · have hcases : x=2 ∨ x=3 ∨ x=4 := by omega
      rcases hcases with h | h | h
      · exact carryInput_marked r T hmatch x (Or.inr (Or.inl h))
      · exact carryInput_marked r T hmatch x (Or.inr (Or.inr (Or.inl h)))
      · exact carryInput_marked r T hmatch x (Or.inr (Or.inr (Or.inr h)))

/-- A nonempty left sweep leaves every cell strictly right of 6 unchanged. -/
theorem carryLeftSweep_rightOutside (r s : Nat) (T : Int → Bool)
    (hmatch : ∀ x, carryInputArea r x = true → T x = carryInputBit r x)
    (hs : 0 < s) (hbound : 4*s ≤ 3*r)
    (x : Int) (hx : 6 < x) :
    sweptLeft (4*s) T 0 x = T x := by
  have hon := carryInput_leftOnes r s T hmatch hbound
  have hzero : T 1 = false := by
    apply carryInput_unmarked r T hmatch 1
    · omega
    · omega
    · simp [carryInputBit]; omega
  rw [carryLeftSweep_closed s T hs hon hzero]
  have h1 : x ≠ 1 := by omega
  have h2 : x ≠ 1-4*(s:Int) := by omega
  simp [h1,h2]

/-- A frame whose final head is marked and whose frame ends at that head
provides a counted one-run by adjoining the unchanged exterior segment. -/
theorem frame_head_segment (inside : Int → Bool) (T : Int → Bool)
    (c : Config) (h u : Int) (n : Nat)
    (hin : inside u = true) (hmark : c.tape u = true)
    (hout : ∀ i : Nat, 0<i → inside (u+(i:Int)) = false)
    (hbg : ∀ i : Nat, i<n → T (h+u+(i:Int)) = true) :
    carrySegmentOnes
      (frame (fun x => inside (x-h)) T (shiftConfig h c)).tape
      (h+u) n := by
  intro i hi
  by_cases hiz : i=0
  · subst i
    change (if inside ((h+u)-h) = true then c.tape ((h+u)-h)
      else T (h+u)) = true
    have hcoord : (h+u)-h = u := by omega
    simp [hcoord,hin,hmark]
  · have hnot := hout i (by omega)
    have hval := hbg i hi
    change (if inside ((h+u+(i:Int))-h) = true then
      c.tape ((h+u+(i:Int))-h) else T (h+u+(i:Int))) = true
    have hcoord : (h+u+(i:Int))-h = u+(i:Int) := by omega
    simp [hcoord,hnot,hval]

/-- Composition of exact source runs. -/
theorem run_compose (m : Machine) (n1 n2 : Nat)
    (c0 c1 c2 : Config)
    (h1 : run m n1 c0 = some c1)
    (h2 : run m n2 c1 = some c2) :
    run m (n1+n2) c0 = some c2 := by
  rw [run_append,h1]
  simpa using h2

#print axioms carryDTail15Open_trace
#print axioms carryDTail15_openEnd
#print axioms carryA3_trace
#print axioms carryA3
#print axioms rightOnes_of_segment
#print axioms sweptRight_future
#print axioms sweptRight_keeps_seven
#print axioms sweptRight_keeps_two_zeroes

end BB6Coverage.Agent48Champion
