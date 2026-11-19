import Q4S0FirstCycleMacros

/-!
# Fixed finite bridges for the positive-z first-checkpoint setup macro

The five bridges below are exact finite traces of the original TM2 table.
They are lifted over arbitrary exterior tape by q4BridgeAt.  The larger
setup composition and its parameterized tape algebra are developed
separately.
-/

namespace BB6Coverage.Agent48PositiveZSetup

open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48Q4S0Macros

set_option maxHeartbeats 4000000

/-! B8: after the first left-one scan, return to state 3 two cells left. -/

def setupB8Inside (x : Int) : Bool :=
  decide (-3 ≤ x ∧ x ≤ 1)

def setupB8Start : FConfig := ⟨3, 0, [-1]⟩

def setupB8End : FConfig := ⟨3, -2, [-3,-2,0]⟩

theorem setupB8_exact :
    fRun tm2 8 setupB8Start = some setupB8End := by
  decide

theorem setupB8_heads :
    (List.range 8).all (fun k =>
      match fRun tm2 k setupB8Start with
      | none => true
      | some f => setupB8Inside f.head) = true := by
  decide

def setupB8Input (T : Int → Bool) (h : Int) : Prop :=
  T (h + (-3:Int)) = false ∧
  T (h + (-2:Int)) = false ∧
  T (h + (-1:Int)) = true ∧
  T h = false ∧
  T (h+1) = false

theorem setupB8_at (T : Int → Bool) (h : Int)
    (hin : setupB8Input T h) :
    run tm2 8 ⟨3,h,T⟩ =
      some (q4FrameAt T h setupB8Inside setupB8End) := by
  apply q4BridgeAt T h setupB8Inside setupB8Start setupB8End 8 rfl
    setupB8_exact setupB8_heads
  intro x hx
  have hrange : -3 ≤ x ∧ x ≤ 1 := by
    simpa [setupB8Inside] using hx
  have hcases : x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 := by omega
  rcases hcases with hx0|hx1|hx2|hx3|hx4 <;> subst x
  · simpa [setupB8Start] using hin.1
  · simpa [setupB8Start] using hin.2.1
  · simpa [setupB8Start] using hin.2.2.1
  · simpa [setupB8Start] using hin.2.2.2.1
  · simpa [setupB8Start] using hin.2.2.2.2

/-! B20: fixed bridge into the first rightward counted sweep. -/

def setupB20Inside (x : Int) : Bool :=
  decide (-5 ≤ x ∧ x ≤ 3)

def setupB20Start : FConfig := ⟨3, 0, [-3,-2,-1,2,3]⟩

def setupB20End : FConfig := ⟨3, 4, [-5,-4,-3,-1,0,1]⟩

theorem setupB20_exact :
    fRun tm2 20 setupB20Start = some setupB20End := by
  decide

theorem setupB20_heads :
    (List.range 20).all (fun k =>
      match fRun tm2 k setupB20Start with
      | none => true
      | some f => setupB20Inside f.head) = true := by
  decide

def setupB20Input (T : Int → Bool) (h : Int) : Prop :=
  T (h + (-5:Int)) = false ∧
  T (h + (-4:Int)) = false ∧
  T (h + (-3:Int)) = true ∧
  T (h + (-2:Int)) = true ∧
  T (h + (-1:Int)) = true ∧
  T h = false ∧
  T (h+1) = false ∧
  T (h+2) = true ∧
  T (h+3) = true

theorem setupB20_at (T : Int → Bool) (h : Int)
    (hin : setupB20Input T h) :
    run tm2 20 ⟨3,h,T⟩ =
      some (q4FrameAt T h setupB20Inside setupB20End) := by
  apply q4BridgeAt T h setupB20Inside setupB20Start setupB20End 20 rfl
    setupB20_exact setupB20_heads
  intro x hx
  have hrange : -5 ≤ x ∧ x ≤ 3 := by
    simpa [setupB20Inside] using hx
  have hcases : x = -5 ∨ x = -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨
      x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
  rcases hcases with hx0|hx1|hx2|hx3|hx4|hx5|hx6|hx7|hx8 <;> subst x
  · simpa [setupB20Start] using hin.1
  · simpa [setupB20Start] using hin.2.1
  · simpa [setupB20Start] using hin.2.2.1
  · simpa [setupB20Start] using hin.2.2.2.1
  · simpa [setupB20Start] using hin.2.2.2.2.1
  · simpa [setupB20Start] using hin.2.2.2.2.2.1
  · simpa [setupB20Start] using hin.2.2.2.2.2.2.1
  · simpa [setupB20Start] using hin.2.2.2.2.2.2.2.1
  · simpa [setupB20Start] using hin.2.2.2.2.2.2.2.2

/-! B9: fixed bridge between the z-sweep and the (A+1)-sweep. -/

def setupB9Inside (x : Int) : Bool :=
  decide (-2 ≤ x ∧ x ≤ 2)

def setupB9Start : FConfig := ⟨3, 0, [0,2]⟩

def setupB9End : FConfig := ⟨3, 3, [-2,-1,0]⟩

theorem setupB9_exact :
    fRun tm2 9 setupB9Start = some setupB9End := by
  decide

theorem setupB9_heads :
    (List.range 9).all (fun k =>
      match fRun tm2 k setupB9Start with
      | none => true
      | some f => setupB9Inside f.head) = true := by
  decide

def setupB9Input (T : Int → Bool) (h : Int) : Prop :=
  T (h + (-2:Int)) = false ∧
  T (h + (-1:Int)) = false ∧
  T h = true ∧
  T (h+1) = false ∧
  T (h+2) = true

theorem setupB9_at (T : Int → Bool) (h : Int)
    (hin : setupB9Input T h) :
    run tm2 9 ⟨3,h,T⟩ =
      some (q4FrameAt T h setupB9Inside setupB9End) := by
  apply q4BridgeAt T h setupB9Inside setupB9Start setupB9End 9 rfl
    setupB9_exact setupB9_heads
  intro x hx
  have hrange : -2 ≤ x ∧ x ≤ 2 := by
    simpa [setupB9Inside] using hx
  have hcases : x = -2 ∨ x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 := by omega
  rcases hcases with hx0|hx1|hx2|hx3|hx4 <;> subst x
  · simpa [setupB9Start] using hin.1
  · simpa [setupB9Start] using hin.2.1
  · simpa [setupB9Start] using hin.2.2.1
  · simpa [setupB9Start] using hin.2.2.2.1
  · simpa [setupB9Start] using hin.2.2.2.2

/-! B6: fixed bridge between the (A+1)- and (L+1)-sweeps. -/

def setupB6Inside (x : Int) : Bool :=
  decide (-1 ≤ x ∧ x ≤ 3)

def setupB6Start : FConfig := ⟨3, 0, [2,3]⟩

def setupB6End : FConfig := ⟨3, 4, [-1,0,1]⟩

theorem setupB6_exact :
    fRun tm2 6 setupB6Start = some setupB6End := by
  decide

theorem setupB6_heads :
    (List.range 6).all (fun k =>
      match fRun tm2 k setupB6Start with
      | none => true
      | some f => setupB6Inside f.head) = true := by
  decide

def setupB6Input (T : Int → Bool) (h : Int) : Prop :=
  T (h + (-1:Int)) = false ∧
  T h = false ∧
  T (h+1) = true ∧
  T (h+2) = true ∧
  T (h+3) = true

theorem setupB6_at (T : Int → Bool) (h : Int)
    (hin : setupB6Input T h) :
    run tm2 6 ⟨3,h,T⟩ =
      some (q4FrameAt T h setupB6Inside setupB6End) := by
  apply q4BridgeAt T h setupB6Inside setupB6Start setupB6End 6 rfl
    setupB6_exact setupB6_heads
  intro x hx
  have hrange : -1 ≤ x ∧ x ≤ 3 := by
    simpa [setupB6Inside] using hx
  have hcases : x = -1 ∨ x = 0 ∨ x = 1 ∨ x = 2 ∨ x = 3 := by omega
  rcases hcases with hx0|hx1|hx2|hx3|hx4 <;> subst x
  · simpa [setupB6Start] using hin.1
  · simpa [setupB6Start] using hin.2.1
  · simpa [setupB6Start] using hin.2.2.1
  · simpa [setupB6Start] using hin.2.2.2.1
  · simpa [setupB6Start] using hin.2.2.2.2

/-! B30: final local return to the new S0 D-head. -/

def setupB30Inside (x : Int) : Bool :=
  decide (-4 ≤ x ∧ x ≤ 5)

def setupB30Start : FConfig := ⟨3, 0, [-3,0]⟩

def setupB30End : FConfig := ⟨3, -4, [-2,-1,0,3,4,5]⟩

theorem setupB30_exact :
    fRun tm2 30 setupB30Start = some setupB30End := by
  decide

theorem setupB30_heads :
    (List.range 30).all (fun k =>
      match fRun tm2 k setupB30Start with
      | none => true
      | some f => setupB30Inside f.head) = true := by
  decide

def setupB30Input (T : Int → Bool) (h : Int) : Prop :=
  T (h + (-4:Int)) = false ∧
  T (h + (-3:Int)) = true ∧
  T (h + (-2:Int)) = false ∧
  T (h + (-1:Int)) = false ∧
  T h = true ∧
  T (h+1) = false ∧
  T (h+2) = false ∧
  T (h+3) = false ∧
  T (h+4) = false ∧
  T (h+5) = false

theorem setupB30_at (T : Int → Bool) (h : Int)
    (hin : setupB30Input T h) :
    run tm2 30 ⟨3,h,T⟩ =
      some (q4FrameAt T h setupB30Inside setupB30End) := by
  apply q4BridgeAt T h setupB30Inside setupB30Start setupB30End 30 rfl
    setupB30_exact setupB30_heads
  intro x hx
  have hrange : -4 ≤ x ∧ x ≤ 5 := by
    simpa [setupB30Inside] using hx
  have hcases : x = -4 ∨ x = -3 ∨ x = -2 ∨ x = -1 ∨ x = 0 ∨
      x = 1 ∨ x = 2 ∨ x = 3 ∨ x = 4 ∨ x = 5 := by omega
  rcases hcases with hx0|hx1|hx2|hx3|hx4|hx5|hx6|hx7|hx8|hx9 <;> subst x
  · simpa [setupB30Start] using hin.1
  · simpa [setupB30Start] using hin.2.1
  · simpa [setupB30Start] using hin.2.2.1
  · simpa [setupB30Start] using hin.2.2.2.1
  · simpa [setupB30Start] using hin.2.2.2.2.1
  · simpa [setupB30Start] using hin.2.2.2.2.2.1
  · simpa [setupB30Start] using hin.2.2.2.2.2.2.1
  · simpa [setupB30Start] using hin.2.2.2.2.2.2.2.1
  · simpa [setupB30Start] using hin.2.2.2.2.2.2.2.2.1
  · simpa [setupB30Start] using hin.2.2.2.2.2.2.2.2.2

#print axioms setupB8_at
#print axioms setupB20_at
#print axioms setupB9_at
#print axioms setupB6_at
#print axioms setupB30_at

end BB6Coverage.Agent48PositiveZSetup
