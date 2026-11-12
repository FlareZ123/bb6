import CountedReset

namespace BB6Coverage.Agent8CountedReset

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder

/-!
A finite, source-authentic base family for the Rst0/Rst1/Rst2 pre-drain
prefix.  These are local framed traces for the a=b=0, odd-outer-counter
boundary pattern.  The surrounding infinite tape is arbitrary outside the
indicated interval.  This file does NOT yet identify the local frames with
all S1 source configurations; that embedding and the a,b,v₂ extensions
remain the universal-prefix proof gap.
-/

/-- The smallest interval containing every head query in the three
a=b=0, n odd, marker-specific base traces. -/
def resetBaseInside (m : Nat) (x : Int) : Bool :=
  if m = 0 then decide (-7 ≤ x ∧ x ≤ 14)
  else decide (-8 ≤ x ∧ x ≤ 14)

/-- Local input tape for the marker-zero base trace. -/
def resetBaseInput0 : FConfig :=
  ⟨3, 0, [-7, -4, -1, 2, 3, 4, 7, 8, 9]⟩

/-- Local input tape for the marker-one base trace. -/
def resetBaseInput1 : FConfig :=
  ⟨3, 0, [-8, -5, -2, 0, 2, 3, 4, 7, 8, 9]⟩

/-- Local input tape for the marker-two base trace. -/
def resetBaseInput2 : FConfig :=
  ⟨3, 0, [-6, -3, -1, 0, 2, 3, 4, 7, 8, 9]⟩

/-- Local output tape after the marker-zero base trace. -/
def resetBaseOutput0 : FConfig :=
  ⟨3, 5, [-7, -6, -5, -4, -1, 1, 2, 3, 4, 5, 7, 8, 9, 12, 13, 14]⟩

/-- Local output tape after the marker-one base trace. -/
def resetBaseOutput1 : FConfig :=
  ⟨3, 5, [-8, -7, -6, -5, -2, 0, 1, 2, 3, 4, 5, 7, 8, 9, 12, 13, 14]⟩

/-- Local output tape after the marker-two base trace. -/
def resetBaseOutput2 : FConfig :=
  ⟨3, 5, [-8, -7, -6, -3, -1, 0, 1, 2, 3, 4, 5, 7, 8, 9, 12, 13, 14]⟩

/-- Uniform notation for the three local input frames. -/
def resetBaseInput (m : Nat) : FConfig :=
  if m = 0 then resetBaseInput0
  else if m = 1 then resetBaseInput1
  else resetBaseInput2

/-- Uniform notation for the three local output frames. -/
def resetBaseOutput (m : Nat) : FConfig :=
  if m = 0 then resetBaseOutput0
  else if m = 1 then resetBaseOutput1
  else resetBaseOutput2

/-- Exact finite TM63 trace for all three marker base cases. -/
theorem resetBase_exact (m : Nat) (hm : m < 3) :
    fRun tm2 (63 + 4*m) (resetBaseInput m) =
      some (resetBaseOutput m) := by
  interval_cases m <;> decide

/-- The local odd-base trace length agrees with the candidate reset-prefix
cost at n=1, a=b=0. -/
theorem resetBase_cost_eq (m : Nat) :
    63 + 4*m = resetPrefixCost m 1 0 0 := by
  norm_num [resetPrefixCost]

/-- The base traces never query outside their local frame intervals. -/
theorem resetBase_heads (m : Nat) (hm : m < 3) :
    ∀ k, k < 63 + 4*m → ∀ d,
      run tm2 k (embed (resetBaseInput m)) = some d →
      resetBaseInside m d.head = true := by
  intro k hk d hd
  have hcheck :
      (List.range (63 + 4*m)).all (fun k =>
        match fRun tm2 k (resetBaseInput m) with
        | none => true
        | some f => resetBaseInside m f.head) = true := by
    interval_cases m <;> decide
  have hitem := List.all_eq_true.mp hcheck k (List.mem_range.mpr hk)
  have hsource := finite_run_source tm2 k (resetBaseInput m)
  cases hrun : fRun tm2 k (resetBaseInput m) with
  | none =>
      simp only [hrun, Option.map_none] at hsource
      rw [← hsource] at hd
      cases hd
  | some f =>
      simp only [hrun, Option.map_some] at hsource
      have hd' := Option.some.inj (hsource.trans hd)
      subst d
      simpa [hrun, embed] using hitem

/-- Arbitrary exterior bits are preserved: these are exact source-machine
runs of 63, 67, or 71 steps on the corresponding local Rst base frame. -/
theorem resetBase_frame (m : Nat) (hm : m < 3)
    (background : Int → Bool) :
    run tm2 (63 + 4*m)
      (frame (resetBaseInside m) background (embed (resetBaseInput m))) =
      some (frame (resetBaseInside m) background (embed (resetBaseOutput m))) := by
  rw [run_frame tm2 (resetBaseInside m) background
    (embed (resetBaseInput m)) (63 + 4*m) (resetBase_heads m hm)]
  rw [← finite_run_source tm2 (63 + 4*m) (resetBaseInput m)]
  rw [resetBase_exact m hm]
  rfl

#print axioms resetBase_exact
#print axioms resetBase_heads
#print axioms resetBase_frame

end BB6Coverage.Agent8CountedReset
