import CountedOneZeroUnary
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48Champion

/-- A frame is unchanged when its background already agrees with the
finite configuration throughout the framed window. -/
theorem frame_eq_of_matches (inside bg : Int → Bool) (c : Config)
    (hmatch : ∀ x, inside x = true → c.tape x = bg x) :
    frame inside bg c = {c with tape := bg} := by
  cases c with
  | mk s h tape =>
      have ht : (fun x => if inside x then tape x else bg x) = bg := by
        funext x
        by_cases hx : inside x = true
        · simp [hx, hmatch x hx]
        · simp [hx]
      simp [frame, ht]

/-- Root-shift commutes with finite-window framing. -/
theorem shift_frame (j : Int) (inside bg : Int → Bool) (c : Config) :
    shiftConfig j (frame inside bg c) =
      frame (fun x => inside (x-j)) (fun x => bg (x-j)) (shiftConfig j c) := by
  cases c with
  | mk s h tape => rfl

/-- Lift a finite-window source trace to an arbitrary infinite tape and
arbitrary head displacement. -/
theorem carryBridgeLift
    (inside : Int → Bool) (base final : Config) (steps : Nat)
    (htrace : ∀ bg, run tm2 steps (frame inside bg base) =
      some (frame inside bg final))
    (T : Int → Bool) (h : Int)
    (hmatch : ∀ x, inside (x-h) = true → base.tape (x-h) = T x) :
    run tm2 steps ({shiftConfig h base with tape := T}) =
      some (frame (fun x => inside (x-h)) T (shiftConfig h final)) := by
  let bg0 : Int → Bool := fun x => T (x+h)
  have hbg : (fun x => bg0 (x-h)) = T := by
    funext x
    simp [bg0]
  have hmatch' : ∀ x, (fun y => inside (y-h)) x = true →
      (shiftConfig h base).tape x = T x := by
    intro x hx
    simpa [shiftConfig] using hmatch x hx
  have hinput : shiftConfig h (frame inside bg0 base) =
      {shiftConfig h base with tape := T} := by
    rw [shift_frame h inside bg0 base, hbg]
    rw [frame_eq_of_matches (fun x => inside (x-h)) T
      (shiftConfig h base) hmatch']
    rfl
  have hrun0 := htrace bg0
  have hshift := shift_run h tm2 (frame inside bg0 base) steps
  rw [hrun0] at hshift
  rw [hinput] at hshift
  rw [shift_frame h inside bg0 final, hbg] at hshift
  exact hshift

/-- The rho=0 bridge: D at h, with the finite window [-1,10] equal to
0 0 0 111111111, advances twelve steps to D at h+10. -/
def carryBridgeArea0 (x : Int) : Bool := decide (-1 ≤ x ∧ x ≤ 10)
def carryBridgeBase0 : FConfig := ⟨3, 0, [2,3,4,5,6,7,8,9,10]⟩
def carryBridgeFinal0 : FConfig := ⟨3, 10, [7,4,1,0,-1,10]⟩

theorem carryBridge0_trace (bg : Int → Bool) :
    run tm2 12 (frame carryBridgeArea0 bg (embed carryBridgeBase0)) =
      some (frame carryBridgeArea0 bg (embed carryBridgeFinal0)) := by
  have he : fRun tm2 12 carryBridgeBase0 = some carryBridgeFinal0 := by decide
  have hc : (List.range 12).all (fun k =>
      match fRun tm2 k carryBridgeBase0 with
      | none => true
      | some c => carryBridgeArea0 c.head) = true := by decide
  rw [run_frame tm2 carryBridgeArea0 bg (embed carryBridgeBase0) 12
    (even_finite_heads tm2 carryBridgeArea0 carryBridgeBase0 12 hc)]
  rw [← finite_run_source tm2 12 carryBridgeBase0, he]
  rfl

theorem carryBridge0 (T : Int → Bool) (h : Int)
    (hmatch : ∀ i : Int, -1 ≤ i → i ≤ 10 →
      T (h+i) = decide (i ∈ ([2,3,4,5,6,7,8,9,10] : List Int))) :
    run tm2 12 ⟨3,h,T⟩ =
      some (frame (fun x => carryBridgeArea0 (x-h)) T
        (shiftConfig h (embed carryBridgeFinal0))) := by
  have hlocal : ∀ x, carryBridgeArea0 (x-h) = true →
      (embed carryBridgeBase0).tape (x-h) = T x := by
    intro x hx
    have hi : -1 ≤ x-h ∧ x-h ≤ 10 := by simpa [carryBridgeArea0] using hx
    have hv := hmatch (x-h) hi.1 hi.2
    have hs : h+(x-h) = x := by omega
    simpa [embed, carryBridgeBase0, hs] using hv.symm
  have hmain := carryBridgeLift carryBridgeArea0
    (embed carryBridgeBase0) (embed carryBridgeFinal0) 12
    carryBridge0_trace T h hlocal
  simpa [embed, carryBridgeBase0, shiftConfig] using hmain

/-- The rho=1 bridge: the local window [-2,6] has marks at 0 and 2..6. -/
def carryBridgeArea1 (x : Int) : Bool := decide (-2 ≤ x ∧ x ≤ 6)
def carryBridgeBase1 : FConfig := ⟨3, 0, [0,2,3,4,5,6]⟩
def carryBridgeFinal1 : FConfig := ⟨3, 6, [3,0,-1,-2,6]⟩

theorem carryBridge1_trace (bg : Int → Bool) :
    run tm2 12 (frame carryBridgeArea1 bg (embed carryBridgeBase1)) =
      some (frame carryBridgeArea1 bg (embed carryBridgeFinal1)) := by
  have he : fRun tm2 12 carryBridgeBase1 = some carryBridgeFinal1 := by decide
  have hc : (List.range 12).all (fun k =>
      match fRun tm2 k carryBridgeBase1 with
      | none => true
      | some c => carryBridgeArea1 c.head) = true := by decide
  rw [run_frame tm2 carryBridgeArea1 bg (embed carryBridgeBase1) 12
    (even_finite_heads tm2 carryBridgeArea1 carryBridgeBase1 12 hc)]
  rw [← finite_run_source tm2 12 carryBridgeBase1, he]
  rfl

theorem carryBridge1 (T : Int → Bool) (h : Int)
    (hmatch : ∀ i : Int, -2 ≤ i → i ≤ 6 →
      T (h+i) = decide (i ∈ ([0,2,3,4,5,6] : List Int))) :
    run tm2 12 ⟨3,h,T⟩ =
      some (frame (fun x => carryBridgeArea1 (x-h)) T
        (shiftConfig h (embed carryBridgeFinal1))) := by
  have hlocal : ∀ x, carryBridgeArea1 (x-h) = true →
      (embed carryBridgeBase1).tape (x-h) = T x := by
    intro x hx
    have hi : -2 ≤ x-h ∧ x-h ≤ 6 := by simpa [carryBridgeArea1] using hx
    have hv := hmatch (x-h) hi.1 hi.2
    have hs : h+(x-h) = x := by omega
    simpa [embed, carryBridgeBase1, hs] using hv.symm
  have hmain := carryBridgeLift carryBridgeArea1
    (embed carryBridgeBase1) (embed carryBridgeFinal1) 12
    carryBridge1_trace T h hlocal
  simpa [embed, carryBridgeBase1, shiftConfig] using hmain

/-- The rho=2 bridge: the local window [-3,2] has marks at -1, 0, 2. -/
def carryBridgeArea2 (x : Int) : Bool := decide (-3 ≤ x ∧ x ≤ 2)
def carryBridgeBase2 : FConfig := ⟨3, 0, [-1,0,2]⟩
def carryBridgeFinal2 : FConfig := ⟨3, 2, [-1,-2,-3,2]⟩

theorem carryBridge2_trace (bg : Int → Bool) :
    run tm2 12 (frame carryBridgeArea2 bg (embed carryBridgeBase2)) =
      some (frame carryBridgeArea2 bg (embed carryBridgeFinal2)) := by
  have he : fRun tm2 12 carryBridgeBase2 = some carryBridgeFinal2 := by decide
  have hc : (List.range 12).all (fun k =>
      match fRun tm2 k carryBridgeBase2 with
      | none => true
      | some c => carryBridgeArea2 c.head) = true := by decide
  rw [run_frame tm2 carryBridgeArea2 bg (embed carryBridgeBase2) 12
    (even_finite_heads tm2 carryBridgeArea2 carryBridgeBase2 12 hc)]
  rw [← finite_run_source tm2 12 carryBridgeBase2, he]
  rfl

theorem carryBridge2 (T : Int → Bool) (h : Int)
    (hmatch : ∀ i : Int, -3 ≤ i → i ≤ 2 →
      T (h+i) = decide (i ∈ ([-1,0,2] : List Int))) :
    run tm2 12 ⟨3,h,T⟩ =
      some (frame (fun x => carryBridgeArea2 (x-h)) T
        (shiftConfig h (embed carryBridgeFinal2))) := by
  have hlocal : ∀ x, carryBridgeArea2 (x-h) = true →
      (embed carryBridgeBase2).tape (x-h) = T x := by
    intro x hx
    have hi : -3 ≤ x-h ∧ x-h ≤ 2 := by simpa [carryBridgeArea2] using hx
    have hv := hmatch (x-h) hi.1 hi.2
    have hs : h+(x-h) = x := by omega
    simpa [embed, carryBridgeBase2, hs] using hv.symm
  have hmain := carryBridgeLift carryBridgeArea2
    (embed carryBridgeBase2) (embed carryBridgeFinal2) 12
    carryBridge2_trace T h hlocal
  simpa [embed, carryBridgeBase2, shiftConfig] using hmain

/-- The rho=3 bridge: the local window [-4,1] has marks at -2, -1, 0. -/
def carryBridgeArea3 (x : Int) : Bool := decide (-4 ≤ x ∧ x ≤ 1)
def carryBridgeBase3 : FConfig := ⟨3, 0, [-2,-1,0]⟩
def carryBridgeFinal3 : FConfig := ⟨0, -2, [-3,-4,-1,0,1]⟩

theorem carryBridge3_trace (bg : Int → Bool) :
    run tm2 12 (frame carryBridgeArea3 bg (embed carryBridgeBase3)) =
      some (frame carryBridgeArea3 bg (embed carryBridgeFinal3)) := by
  have he : fRun tm2 12 carryBridgeBase3 = some carryBridgeFinal3 := by decide
  have hc : (List.range 12).all (fun k =>
      match fRun tm2 k carryBridgeBase3 with
      | none => true
      | some c => carryBridgeArea3 c.head) = true := by decide
  rw [run_frame tm2 carryBridgeArea3 bg (embed carryBridgeBase3) 12
    (even_finite_heads tm2 carryBridgeArea3 carryBridgeBase3 12 hc)]
  rw [← finite_run_source tm2 12 carryBridgeBase3, he]
  rfl

theorem carryBridge3 (T : Int → Bool) (h : Int)
    (hmatch : ∀ i : Int, -4 ≤ i → i ≤ 1 →
      T (h+i) = decide (i ∈ ([-2,-1,0] : List Int))) :
    run tm2 12 ⟨3,h,T⟩ =
      some (frame (fun x => carryBridgeArea3 (x-h)) T
        (shiftConfig h (embed carryBridgeFinal3))) := by
  have hlocal : ∀ x, carryBridgeArea3 (x-h) = true →
      (embed carryBridgeBase3).tape (x-h) = T x := by
    intro x hx
    have hi : -4 ≤ x-h ∧ x-h ≤ 1 := by simpa [carryBridgeArea3] using hx
    have hv := hmatch (x-h) hi.1 hi.2
    have hs : h+(x-h) = x := by omega
    simpa [embed, carryBridgeBase3, hs] using hv.symm
  have hmain := carryBridgeLift carryBridgeArea3
    (embed carryBridgeBase3) (embed carryBridgeFinal3) 12
    carryBridge3_trace T h hlocal
  simpa [embed, carryBridgeBase3, shiftConfig] using hmain

#print axioms carryBridge0
#print axioms carryBridge1
#print axioms carryBridge2
#print axioms carryBridge3

end BB6Coverage.Agent48Champion
