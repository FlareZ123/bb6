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

set_option maxHeartbeats 1000000

/-- A at head 0, twelve consecutive ones to the right. -/
def carryAD12Area (x : Int) : Bool := decide (0 ≤ x ∧ x ≤ 12)
def carryAD12Base : FConfig := ⟨0, 0, [1,2,3,4,5,6,7,8,9,10,11,12]⟩
def carryAD12Final : FConfig := ⟨3, 12, [9,6,3,0,12]⟩

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
  rfl

theorem carryAD12 (T : Int → Bool) (h : Int)
    (hlocal : ∀ x, carryAD12Area (x-h) = true →
      (embed carryAD12Base).tape (x-h) = T x) :
    run tm2 12 ⟨0,h,T⟩ =
      some (frame (fun x => carryAD12Area (x-h)) T
        (shiftConfig h (embed carryAD12Final))) := by
  have hmain := carryBridgeLift carryAD12Area
    (embed carryAD12Base) (embed carryAD12Final) 12
    carryAD12_trace T h hlocal
  simpa [embed, carryAD12Base, shiftConfig] using hmain

/-- D at head 0 with the seven-cell terminal input 1111111. -/
def carryDTail15Area (x : Int) : Bool := decide (0 ≤ x ∧ x ≤ 9)
def carryDTail15Base : FConfig := ⟨3, 0, [0,1,2,3,4,5,6]⟩
def carryDTail15Final : FConfig := ⟨4, 9, [8,6,5,4,3,0]⟩

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
  rfl

theorem carryDTail15 (T : Int → Bool) (h : Int)
    (hlocal : ∀ x, carryDTail15Area (x-h) = true →
      (embed carryDTail15Base).tape (x-h) = T x) :
    run tm2 15 ⟨3,h,T⟩ =
      some (frame (fun x => carryDTail15Area (x-h)) T
        (shiftConfig h (embed carryDTail15Final))) := by
  have hmain := carryBridgeLift carryDTail15Area
    (embed carryDTail15Base) (embed carryDTail15Final) 15
    carryDTail15_trace T h hlocal
  simpa [embed, carryDTail15Base, shiftConfig] using hmain

/-- The exceptional rho=3, t=1 branch: A returns to A after twelve
steps rather than entering the longer A→D scan. -/
def carryAReturn12Area (x : Int) : Bool := decide (-3 ≤ x ∧ x ≤ 7)
def carryAReturn12Base : FConfig :=
  ⟨0, 0, [-3,-2,-1,1,2,3,4,5,6]⟩
def carryAReturn12Final : FConfig :=
  ⟨0, 6, [5,4,7,3,0,-3,-2,-1]⟩

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
  rfl

theorem carryAReturn12 (T : Int → Bool) (h : Int)
    (hlocal : ∀ x, carryAReturn12Area (x-h) = true →
      (embed carryAReturn12Base).tape (x-h) = T x) :
    run tm2 12 ⟨0,h,T⟩ =
      some (frame (fun x => carryAReturn12Area (x-h)) T
        (shiftConfig h (embed carryAReturn12Final))) := by
  have hmain := carryBridgeLift carryAReturn12Area
    (embed carryAReturn12Base) (embed carryAReturn12Final) 12
    carryAReturn12_trace T h hlocal
  simpa [embed, carryAReturn12Base, shiftConfig] using hmain

/-- The residue-3 bridge's framed A endpoint already supplies the first
three right-facing ones needed by the A→D scan.  If the untouched exterior
has ones at old coordinates h+2..h+10, the bridge output matches the
12-cell A→D input on its entire local window. -/
theorem carryBridge3_matches_carryAD12
    (T : Int → Bool) (h : Int)
    (hRight : ∀ i : Int, 2 ≤ i → i ≤ 10 → T (h+i) = true) :
    ∀ x, carryAD12Area (x-(h-2)) = true →
      (embed carryAD12Base).tape (x-(h-2)) =
        (frame (fun y => carryBridgeArea3 (y-h)) T
          (shiftConfig h (embed carryBridgeFinal3))).tape x := by
  intro x hx
  let i := x-h
  have hk : x-(h-2) = i+2 := by dsimp [i]; omega
  have hkRange : 0 ≤ x-(h-2) ∧ x-(h-2) ≤ 12 := by
    simpa [carryAD12Area] using hx
  have hiLo : -2 ≤ i := by dsimp [i]; omega
  have hiHi : i ≤ 10 := by dsimp [i]; omega
  by_cases hin : carryBridgeArea3 i = true
  · have harea : -4 ≤ i ∧ i ≤ 1 := by simpa [carryBridgeArea3] using hin
    have hcases : i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 := by omega
    rcases hcases with h2 | h1 | h0 | h1p
    · have hk0 : x-(h-2) = 0 := by dsimp [i] at h2; omega
      simp [embed, carryAD12Base, carryBridgeFinal3, frame, shiftConfig,
        carryBridgeArea3, i, h2, hk0]
    · have hk1 : x-(h-2) = 1 := by dsimp [i] at h1; omega
      simp [embed, carryAD12Base, carryBridgeFinal3, frame, shiftConfig,
        carryBridgeArea3, i, h1, hk1]
    · have hk2 : x-(h-2) = 2 := by dsimp [i] at h0; omega
      simp [embed, carryAD12Base, carryBridgeFinal3, frame, shiftConfig,
        carryBridgeArea3, i, h0, hk2]
    · have hk3 : x-(h-2) = 3 := by dsimp [i] at h1p; omega
      simp [embed, carryAD12Base, carryBridgeFinal3, frame, shiftConfig,
        carryBridgeArea3, i, h1p, hk3]
  · have hnot : carryBridgeArea3 i = false := by
      cases hh : carryBridgeArea3 i <;> simp_all
    have hiLo' : 2 ≤ i := by
      have harea : ¬ (-4 ≤ i ∧ i ≤ 1) := by simpa [carryBridgeArea3] using hnot
      omega
    have hR := hRight i hiLo' hiHi
    have hcoord : h+i = x := by dsimp [i]; omega
    have hR' : T x = true := by simpa [hcoord] using hR
    have hbase : (embed carryAD12Base).tape (x-(h-2)) = true := by
      simp [embed, carryAD12Base]
      omega
    have hout :
        (frame (fun y => carryBridgeArea3 (y-h)) T
          (shiftConfig h (embed carryBridgeFinal3))).tape x = true := by
      simp [frame, shiftConfig, i, hnot, hR']
    rw [hbase, hout]

/-- The short exceptional rho=3 branch: after carryBridge3, the A
endpoint matches the twelve-step A→A return window when the exterior has
the required single left marker, three right markers, and the following
zero. -/
theorem carryBridge3_matches_carryAReturn12
    (T : Int → Bool) (h : Int)
    (hLeft : T (h-5) = true)
    (hRight : ∀ i : Int, 2 ≤ i → i ≤ 4 → T (h+i) = true)
    (hZero : T (h+5) = false) :
    ∀ x, carryAReturn12Area (x-(h-2)) = true →
      (embed carryAReturn12Base).tape (x-(h-2)) =
        (frame (fun y => carryBridgeArea3 (y-h)) T
          (shiftConfig h (embed carryBridgeFinal3))).tape x := by
  intro x hx
  let i := x-h
  have hk : x-(h-2) = i+2 := by dsimp [i]; omega
  have hkRange : -3 ≤ x-(h-2) ∧ x-(h-2) ≤ 7 := by
    simpa [carryAReturn12Area] using hx
  have hiLo : -5 ≤ i := by dsimp [i]; omega
  have hiHi : i ≤ 5 := by dsimp [i]; omega
  by_cases hin : carryBridgeArea3 i = true
  · have harea : -4 ≤ i ∧ i ≤ 1 := by simpa [carryBridgeArea3] using hin
    have hcases : i = -4 ∨ i = -3 ∨ i = -2 ∨ i = -1 ∨ i = 0 ∨ i = 1 := by omega
    rcases hcases with h4 | h3 | h2 | h1 | h0 | h1p
    · have hk0 : x-(h-2) = -2 := by dsimp [i] at h4; omega
      simp [embed, carryAReturn12Base, carryBridgeFinal3, frame, shiftConfig,
        carryBridgeArea3, i, h4, hk0]
    · have hk1 : x-(h-2) = -1 := by dsimp [i] at h3; omega
      simp [embed, carryAReturn12Base, carryBridgeFinal3, frame, shiftConfig,
        carryBridgeArea3, i, h3, hk1]
    · have hk2 : x-(h-2) = 0 := by dsimp [i] at h2; omega
      simp [embed, carryAReturn12Base, carryBridgeFinal3, frame, shiftConfig,
        carryBridgeArea3, i, h2, hk2]
    · have hk3 : x-(h-2) = 1 := by dsimp [i] at h1; omega
      simp [embed, carryAReturn12Base, carryBridgeFinal3, frame, shiftConfig,
        carryBridgeArea3, i, h1, hk3]
    · have hk4 : x-(h-2) = 2 := by dsimp [i] at h0; omega
      simp [embed, carryAReturn12Base, carryBridgeFinal3, frame, shiftConfig,
        carryBridgeArea3, i, h0, hk4]
    · have hk5 : x-(h-2) = 3 := by dsimp [i] at h1p; omega
      simp [embed, carryAReturn12Base, carryBridgeFinal3, frame, shiftConfig,
        carryBridgeArea3, i, h1p, hk5]
  · have hnot : carryBridgeArea3 i = false := by
      cases hh : carryBridgeArea3 i <;> simp_all
    by_cases hleft : i = -5
    · have hcoord : h+i = x := by dsimp [i]; omega
      have hT : T x = true := by simpa [hcoord, hleft] using hLeft
      have hbase : (embed carryAReturn12Base).tape (x-(h-2)) = true := by
        simp [embed, carryAReturn12Base, hk, hleft]
      have hout :
          (frame (fun y => carryBridgeArea3 (y-h)) T
            (shiftConfig h (embed carryBridgeFinal3))).tape x = true := by
        simp [frame, shiftConfig, i, hnot, hT]
      rw [hbase, hout]
    · by_cases hlast : i = 5
      · have hcoord : h+i = x := by dsimp [i]; omega
        have hT : T x = false := by simpa [hcoord, hlast] using hZero
        have hbase : (embed carryAReturn12Base).tape (x-(h-2)) = false := by
          simp [embed, carryAReturn12Base, hk, hlast]
        have hout :
            (frame (fun y => carryBridgeArea3 (y-h)) T
              (shiftConfig h (embed carryBridgeFinal3))).tape x = false := by
          simp [frame, shiftConfig, i, hnot, hT]
        rw [hbase, hout]
      · have hiLo' : 2 ≤ i := by omega
        have hiHi' : i ≤ 4 := by omega
        have hR := hRight i hiLo' hiHi'
        have hcoord : h+i = x := by dsimp [i]; omega
        have hT : T x = true := by simpa [hcoord] using hR
        have hbase : (embed carryAReturn12Base).tape (x-(h-2)) = true := by
          simp [embed, carryAReturn12Base, hk]
          omega
        have hout :
            (frame (fun y => carryBridgeArea3 (y-h)) T
              (shiftConfig h (embed carryBridgeFinal3))).tape x = true := by
          simp [frame, shiftConfig, i, hnot, hT]
        rw [hbase, hout]

#print axioms carryBridge3_matches_carryAD12
#print axioms carryBridge3_matches_carryAReturn12
#print axioms carryAD12_trace
#print axioms carryDTail15_trace
#print axioms carryAReturn12_trace
#print axioms carryAD12
#print axioms carryDTail15
#print axioms carryAReturn12

end BB6Coverage.Agent48Champion
