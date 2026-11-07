import JF0Prefix

/-!
# C/B rightward sweep primitive for machine #429

This module isolates the raw C/1,B/0 sweep that appears after the F/0 setup
in the two-parameter J-chart investigation.

For each scanned pair 10, the machine writes 01 and advances two cells.
After k pairs the head is at h+2k in state C, with the processed interval
painted accordingly. At the boundary, C/0 followed by D/1 is fatal;
C/1 followed by B/1 reaches state A two cells farther right.

The exact J-chart application still requires composing the source-specific
F/0-to-C setup and proving its tape-pattern hypotheses. This file proves
the transition primitive and its exact branch costs; it does not claim that
the full J-chart composition is already established.
-/

namespace BB429CBPrimitiveSweep

open BB6Coverage
open BB429PhysicalFrontier

abbrev stateA : Fin 6 := ⟨0, by decide⟩
abbrev stateB : Fin 6 := ⟨1, by decide⟩
abbrev stateC : Fin 6 := ⟨2, by decide⟩
abbrev stateD : Fin 6 := ⟨3, by decide⟩

/-- The tape after k C/1,B/0 pairs have converted 10 to 01. -/
def cbPaint (t : Int → Bool) (h : Int) : Nat → Int → Bool
  | 0 => t
  | k+1 => fun x =>
      if x = h + 2*(k:Int) + 1 then true
      else if x = h + 2*(k:Int) then false
      else cbPaint t h k x

theorem run_add_cb (m : Machine) (a b : Nat) (c : Config) :
    run m (a+b) c = (run m a c).bind (fun d => run m b d) := by
  induction b with
  | zero => simp [run]
  | succ b ih =>
    calc
      run m (a+(b+1)) c = (run m (a+b) c).bind (rawStep m) := by rfl
      _ = ((run m a c).bind (fun d => run m b d)).bind (rawStep m) := by rw [ih]
      _ = (run m a c).bind (fun d => run m (b+1) d) := by
        cases h : run m a c with
        | none => simp [h]
        | some d => simp [h, run]

theorem cbPaint_outside_right (t : Int → Bool) (h : Int) (k : Nat) (x : Int)
    (hx : h + 2*(k:Int) ≤ x) : cbPaint t h k x = t x := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hx' : h + 2*(k:Int) ≤ x := by omega
    have hn0 : x ≠ h + 2*(k:Int) := by omega
    have hn1 : x ≠ h + 2*(k:Int) + 1 := by omega
    simp [cbPaint, hn0, hn1, ih hx']

/-- One C/1,B/0 pair converts 10 to 01 and advances two cells. -/
theorem run_two_CB_10 (h : Int) (t : Int → Bool)
    (h0 : t h = true) (h1 : t (h+1) = false) :
    run target429 2 {state:=stateC, head:=h, tape:=t} =
      some (applyMove (applyMove {state:=stateC, head:=h, tape:=t}
        ⟨false, true, stateB⟩) ⟨true, true, stateC⟩) := by
  let c : Config := {state:=stateC, head:=h, tape:=t}
  let mC : Move := ⟨false, true, stateB⟩
  let mB : Move := ⟨true, true, stateC⟩
  have hC1 : target429 (stateC,true) = some mC := by decide
  have hB0 : target429 (stateB,false) = some mB := by decide
  have hc : rawStep target429 c = some (applyMove c mC) := by
    simp [rawStep, readSlot, c, h0, hC1, mC]
  have hneq : h+1 ≠ h := by omega
  have hb : rawStep target429 (applyMove c mC) =
      some (applyMove (applyMove c mC) mB) := by
    simp [rawStep, readSlot, applyMove, c, mC, mB, hneq, h1, hB0]
  change (rawStep target429 c).bind (rawStep target429) = _
  rw [hc]
  simp only [Option.bind_some]
  rw [hb]

/-- k consecutive 10 pairs are swept rightward, producing 01 pairs. -/
theorem CB_sweep (h : Int) (t : Int → Bool) (k : Nat)
    (heven : ∀ i : Nat, i < k → t (h+2*(i:Int)) = true)
    (hodd : ∀ i : Nat, i < k → t (h+2*(i:Int)+1) = false) :
    run target429 (2*k) {state:=stateC, head:=h, tape:=t} =
      some {state:=stateC, head:=h+2*(k:Int), tape:=cbPaint t h k} := by
  induction k with
  | zero => simp [run, cbPaint]
  | succ k ih =>
    have he : ∀ i : Nat, i < k → t (h+2*(i:Int)) = true := by
      intro i hi
      exact heven i (by omega)
    have ho : ∀ i : Nat, i < k → t (h+2*(i:Int)+1) = false := by
      intro i hi
      exact hodd i (by omega)
    have hp := ih he ho
    have hx0 : cbPaint t h k (h+2*(k:Int)) = true := by
      rw [cbPaint_outside_right t h k (h+2*(k:Int)) (by omega)]
      exact heven k (by omega)
    have hx1 : cbPaint t h k (h+2*(k:Int)+1) = false := by
      rw [cbPaint_outside_right t h k (h+2*(k:Int)+1) (by omega)]
      exact hodd k (by omega)
    have htime : 2*(k+1) = 2*k+2 := by omega
    rw [htime, run_add_cb, hp]
    simp only [Option.bind_some]
    rw [run_two_CB_10 (h+2*(k:Int)) (cbPaint t h k) hx0 hx1]
    simp [applyMove, cbPaint, Int.mul_add]
    omega

/-- One C/1,B/1 boundary pair reaches A two cells to the right. -/
theorem run_two_CB_11 (h : Int) (t : Int → Bool)
    (h0 : t h = true) (h1 : t (h+1) = true) :
    run target429 2 {state:=stateC, head:=h, tape:=t} =
      some (applyMove (applyMove {state:=stateC, head:=h, tape:=t}
        ⟨false, true, stateB⟩) ⟨true, true, stateA⟩) := by
  let c : Config := {state:=stateC, head:=h, tape:=t}
  let mC : Move := ⟨false, true, stateB⟩
  let mB : Move := ⟨true, true, stateA⟩
  have hC1 : target429 (stateC,true) = some mC := by decide
  have hB1 : target429 (stateB,true) = some mB := by decide
  have hc : rawStep target429 c = some (applyMove c mC) := by
    simp [rawStep, readSlot, c, h0, hC1, mC]
  have hneq : h+1 ≠ h := by omega
  have hb : rawStep target429 (applyMove c mC) =
      some (applyMove (applyMove c mC) mB) := by
    simp [rawStep, readSlot, applyMove, c, mC, mB, hneq, h1, hB1]
  change (rawStep target429 c).bind (rawStep target429) = _
  rw [hc]
  simp only [Option.bind_some]
  rw [hb]

/-- If the boundary is 01, the sweep enters D/1 and halts. -/
theorem CB_fatal_tail (h : Int) (t : Int → Bool) (k : Nat)
    (heven : ∀ i : Nat, i < k → t (h+2*(i:Int)) = true)
    (hodd : ∀ i : Nat, i < k → t (h+2*(i:Int)+1) = false)
    (hend : t (h+2*(k:Int)) = false)
    (hnext : t (h+2*(k:Int)+1) = true) :
    ∃ d, run target429 (2*k+1) {state:=stateC,head:=h,tape:=t} = some d ∧
      d.state = stateD ∧ d.head = h+2*(k:Int)+1 ∧ rawStep target429 d = none := by
  have hsweep := CB_sweep h t k heven hodd
  have hend' : cbPaint t h k (h+2*(k:Int)) = false := by
    rw [cbPaint_outside_right t h k (h+2*(k:Int)) (by omega)]
    exact hend
  have hnext' : cbPaint t h k (h+2*(k:Int)+1) = true := by
    rw [cbPaint_outside_right t h k (h+2*(k:Int)+1) (by omega)]
    exact hnext
  have hC0 : target429 (stateC,false) = some (⟨false,true,stateD⟩ : Move) := by decide
  have hD1 : target429 (stateD,true) = none := by decide
  let c : Config := {state:=stateC,head:=h+2*(k:Int),tape:=cbPaint t h k}
  let d : Config := applyMove c ⟨false,true,stateD⟩
  have htail : run target429 1 c = some d := by
    simp [run, rawStep, readSlot, c, d, applyMove, hend', hC0]
  have hrun : run target429 (2*k+1) {state:=stateC,head:=h,tape:=t} = some d := by
    rw [show 2*k+1 = (2*k)+1 by omega, run_add_cb, hsweep]
    simp only [Option.bind_some]
    exact htail
  refine ⟨d, hrun, ?_, ?_, ?_⟩
  · rfl
  · simp [d,c,applyMove]
  · have hneq : h+2*(k:Int)+1 ≠ h+2*(k:Int) := by omega
    simp [rawStep, readSlot, d, c, applyMove, hnext', hneq, hD1]

/-- If the boundary is 11, the sweep continues into A two cells later. -/
theorem CB_continue_tail (h : Int) (t : Int → Bool) (k : Nat)
    (heven : ∀ i : Nat, i < k → t (h+2*(i:Int)) = true)
    (hodd : ∀ i : Nat, i < k → t (h+2*(i:Int)+1) = false)
    (hend : t (h+2*(k:Int)) = true)
    (hnext : t (h+2*(k:Int)+1) = true) :
    ∃ d, run target429 (2*k+2) {state:=stateC,head:=h,tape:=t} = some d ∧
      d.state = stateA ∧ d.head = h+2*(k:Int)+2 := by
  have hsweep := CB_sweep h t k heven hodd
  have hend' : cbPaint t h k (h+2*(k:Int)) = true := by
    rw [cbPaint_outside_right t h k (h+2*(k:Int)) (by omega)]
    exact hend
  have hnext' : cbPaint t h k (h+2*(k:Int)+1) = true := by
    rw [cbPaint_outside_right t h k (h+2*(k:Int)+1) (by omega)]
    exact hnext
  let c : Config := {state:=stateC,head:=h+2*(k:Int),tape:=cbPaint t h k}
  let d : Config := applyMove (applyMove c ⟨false,true,stateB⟩) ⟨true,true,stateA⟩
  have htail : run target429 2 c = some d := by
    rw [run_two_CB_11 (h+2*(k:Int)) (cbPaint t h k) hend' hnext']
  have hrun : run target429 (2*k+2) {state:=stateC,head:=h,tape:=t} = some d := by
    rw [show 2*k+2 = (2*k)+2 by omega, run_add_cb, hsweep]
    simp only [Option.bind_some]
    exact htail
  refine ⟨d, hrun, ?_, ?_⟩
  · rfl
  · simp [d,c,applyMove]
    omega

theorem CB_fatal_time (u : Nat) :
    (4*u*u+6*u+7) + 14 + (2*(2*u+2)+1) = 4*u*u+10*u+26 := by omega

theorem CB_continue_time (u : Nat) :
    (4*u*u+6*u+7) + 14 + (2*(2*u+2)+2) = 4*u*u+10*u+27 := by omega

end BB429CBPrimitiveSweep
