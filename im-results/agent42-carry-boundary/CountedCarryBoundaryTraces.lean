import CountedCarryBridges
import Lean.Elab.Tactic.Omega

/-!
# Fixed source-exact boundary traces for the counted carry prefix

These three local traces close the fixed transitions at the exceptional
rho=3 boundary: A→D on a 12-one block, the r=1 A→A short branch, and the
common D-tail15.  Each is lifted to arbitrary exterior tape by the existing
finite-head/frame and shift machinery.  They are finite boundary lemmas,
not an arbitrary-r carry theorem.
-/

namespace BB6Coverage.Agent48Champion

/-- A at head 0, twelve consecutive ones to the right. -/
def carryAD12Area (x : Int) : Bool := decide (0 ≤ x ∧ x ≤ 12)
def carryAD12Base : FConfig := ⟨0, 0, [1,2,3,4,5,6,7,8,9,10,11,12]⟩
def carryAD12Final : FConfig := ⟨3, 12, [0,3,6,9,12]⟩

theorem carryAD12_trace (bg : Int → Bool) :
    run tm2 12 (frame carryAD12Area bg (embed carryAD12Base)) =
      some (frame carryAD12Area bg (embed carryAD12Final)) := by
  have he : fRun tm2 12 carryAD12Base = some carryAD12Final := by decide
  have hc : (List.range 12).all (fun k =>
      match fRun tm2 k carryAD12Base with
      | none => true
      | some z => carryAD12Area z.head) = true := by decide
  rw [run_frame tm2 carryAD12Area bg (embed carryAD12Base) 12
    (finite_heads tm2 carryAD12Area carryAD12Base 12 hc)]
  rw [← finite_run_source tm2 12 carryAD12Base, he]

theorem carryAD12 (T : Int → Bool) (h : Int)
    (hlocal : ∀ x, carryAD12Area (x-h) = true →
      (embed carryAD12Base).tape (x-h) = T x) :
    run tm2 12
      (frame (fun x => carryAD12Area (x-h)) T
        (shiftConfig h (embed carryAD12Base))) =
      some (frame (fun x => carryAD12Area (x-h)) T
        (shiftConfig h (embed carryAD12Final))) := by
  exact carryBridgeLift carryAD12Area
    (embed carryAD12Base) (embed carryAD12Final) 12
    carryAD12_trace T h hlocal

/-- D at head 0 with the seven-cell terminal input 1111111. -/
def carryDTail15Area (x : Int) : Bool := decide (0 ≤ x ∧ x ≤ 9)
def carryDTail15Base : FConfig := ⟨3, 0, [0,1,2,3,4,5,6]⟩
def carryDTail15Final : FConfig := ⟨4, 9, [0,3,4,5,6,8]⟩

theorem carryDTail15_trace (bg : Int → Bool) :
    run tm2 15 (frame carryDTail15Area bg (embed carryDTail15Base)) =
      some (frame carryDTail15Area bg (embed carryDTail15Final)) := by
  have he : fRun tm2 15 carryDTail15Base = some carryDTail15Final := by decide
  have hc : (List.range 15).all (fun k =>
      match fRun tm2 k carryDTail15Base with
      | none => true
      | some z => carryDTail15Area z.head) = true := by decide
  rw [run_frame tm2 carryDTail15Area bg (embed carryDTail15Base) 15
    (finite_heads tm2 carryDTail15Area carryDTail15Base 15 hc)]
  rw [← finite_run_source tm2 15 carryDTail15Base, he]

theorem carryDTail15 (T : Int → Bool) (h : Int)
    (hlocal : ∀ x, carryDTail15Area (x-h) = true →
      (embed carryDTail15Base).tape (x-h) = T x) :
    run tm2 15
      (frame (fun x => carryDTail15Area (x-h)) T
        (shiftConfig h (embed carryDTail15Base))) =
      some (frame (fun x => carryDTail15Area (x-h)) T
        (shiftConfig h (embed carryDTail15Final))) := by
  exact carryBridgeLift carryDTail15Area
    (embed carryDTail15Base) (embed carryDTail15Final) 15
    carryDTail15_trace T h hlocal

/-- The exceptional rho=3, t=1 branch: A returns to A after twelve
steps rather than entering the longer A→D scan. -/
def carryAReturn12Area (x : Int) : Bool := decide (-3 ≤ x ∧ x ≤ 7)
def carryAReturn12Base : FConfig :=
  ⟨0, 0, [-3,-2,-1,1,2,3,4,5,6]⟩
def carryAReturn12Final : FConfig :=
  ⟨0, 6, [-3,-2,-1,0,3,4,5,7]⟩

theorem carryAReturn12_trace (bg : Int → Bool) :
    run tm2 12 (frame carryAReturn12Area bg (embed carryAReturn12Base)) =
      some (frame carryAReturn12Area bg (embed carryAReturn12Final)) := by
  have he : fRun tm2 12 carryAReturn12Base = some carryAReturn12Final := by decide
  have hc : (List.range 12).all (fun k =>
      match fRun tm2 k carryAReturn12Base with
      | none => true
      | some z => carryAReturn12Area z.head) = true := by decide
  rw [run_frame tm2 carryAReturn12Area bg (embed carryAReturn12Base) 12
    (finite_heads tm2 carryAReturn12Area carryAReturn12Base 12 hc)]
  rw [← finite_run_source tm2 12 carryAReturn12Base, he]

theorem carryAReturn12 (T : Int → Bool) (h : Int)
    (hlocal : ∀ x, carryAReturn12Area (x-h) = true →
      (embed carryAReturn12Base).tape (x-h) = T x) :
    run tm2 12
      (frame (fun x => carryAReturn12Area (x-h)) T
        (shiftConfig h (embed carryAReturn12Base))) =
      some (frame (fun x => carryAReturn12Area (x-h)) T
        (shiftConfig h (embed carryAReturn12Final))) := by
  exact carryBridgeLift carryAReturn12Area
    (embed carryAReturn12Base) (embed carryAReturn12Final) 12
    carryAReturn12_trace T h hlocal

#print axioms carryAD12_trace
#print axioms carryDTail15_trace
#print axioms carryAReturn12_trace
#print axioms carryAD12
#print axioms carryDTail15
#print axioms carryAReturn12

end BB6Coverage.Agent48Champion
