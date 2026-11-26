import PhaseTree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent47Extra91
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | _,_ => none)
def p_0 := refine parent (4,true) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.side 0 12 false (2))
theorem checked_0 : check 143 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 143 m := sound 143 _ cert_0 (by decide) checked_0
def p_1 := refine parent (4,true) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 0 16 true (-1))
theorem checked_1 : check 143 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 143 m := sound 143 _ cert_1 (by decide) checked_1
def p_2 := refine parent (4,true) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 7 6 false (1))
theorem checked_2 : check 143 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 143 m := sound 143 _ cert_2 (by decide) checked_2
def p_3 := refine parent (4,true) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 24 17 false (2))
theorem checked_3 : check 143 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 143 m := sound 143 _ cert_3 (by decide) checked_3
def p_4 := refine parent (4,true) (some ⟨false,false,1⟩)
def cert_4 : Tree := (.side 7 14 false (1))
theorem checked_4 : check 143 p_4 cert_4 = true := by decide +kernel
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 143 m := sound 143 _ cert_4 (by decide) checked_4
def p_5 := refine parent (4,true) (some ⟨false,true,1⟩)
def cert_5 : Tree := (.side 7 14 false (1))
theorem checked_5 : check 143 p_5 cert_5 = true := by decide +kernel
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 143 m := sound 143 _ cert_5 (by decide) checked_5
def p_6 := refine parent (4,true) (some ⟨true,false,1⟩)
def cert_6 : Tree := (.side 9 3 false (0))
theorem checked_6 : check 143 p_6 cert_6 = true := by decide +kernel
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 143 m := sound 143 _ cert_6 (by decide) checked_6
def p_7 := refine parent (4,true) (some ⟨true,true,1⟩)
def cert_7 : Tree := (.side 1 11 false (2))
theorem checked_7 : check 143 p_7 cert_7 = true := by decide +kernel
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 143 m := sound 143 _ cert_7 (by decide) checked_7
def p_8 := refine parent (4,true) (some ⟨false,false,2⟩)
def cert_8 : Tree := (.side 0 13 false (2))
theorem checked_8 : check 143 p_8 cert_8 = true := by decide +kernel
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 143 m := sound 143 _ cert_8 (by decide) checked_8
def p_9 := refine parent (4,true) (some ⟨false,true,2⟩)
def cert_9 : Tree := (.side 0 13 false (2))
theorem checked_9 : check 143 p_9 cert_9 = true := by decide +kernel
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 143 m := sound 143 _ cert_9 (by decide) checked_9
def p_10 := refine parent (4,true) (some ⟨true,false,2⟩)
def p_10_0 := refine p_10 (4,false) (some ⟨false,false,0⟩)
def cert_10_0 : Tree := (.side 0 19 false (2))
theorem checked_10_0 : check 143 p_10_0 cert_10_0 = true := by decide +kernel
theorem safe_10_0 : ∀ m, compatible p_10_0 m → WeightedBound 143 m := sound 143 _ cert_10_0 (by decide) checked_10_0
def p_10_1 := refine p_10 (4,false) (some ⟨false,true,0⟩)
def cert_10_1 : Tree := (.side 7 13 false (1))
theorem checked_10_1 : check 143 p_10_1 cert_10_1 = true := by decide +kernel
theorem safe_10_1 : ∀ m, compatible p_10_1 m → WeightedBound 143 m := sound 143 _ cert_10_1 (by decide) checked_10_1
def p_10_2 := refine p_10 (4,false) (some ⟨true,false,0⟩)
def cert_10_2 : Tree := (.side 7 13 false (1))
theorem checked_10_2 : check 143 p_10_2 cert_10_2 = true := by decide +kernel
theorem safe_10_2 : ∀ m, compatible p_10_2 m → WeightedBound 143 m := sound 143 _ cert_10_2 (by decide) checked_10_2
def p_10_3 := refine p_10 (4,false) (some ⟨true,true,0⟩)
def cert_10_3 : Tree := (.side 7 18 false (1))
theorem checked_10_3 : check 143 p_10_3 cert_10_3 = true := by decide +kernel
theorem safe_10_3 : ∀ m, compatible p_10_3 m → WeightedBound 143 m := sound 143 _ cert_10_3 (by decide) checked_10_3
def p_10_4 := refine p_10 (4,false) (some ⟨false,false,1⟩)
def cert_10_4 : Tree := (.side 7 21 false (1))
theorem checked_10_4 : check 143 p_10_4 cert_10_4 = true := by decide +kernel
theorem safe_10_4 : ∀ m, compatible p_10_4 m → WeightedBound 143 m := sound 143 _ cert_10_4 (by decide) checked_10_4
def p_10_5 := refine p_10 (4,false) (some ⟨false,true,1⟩)
def cert_10_5 : Tree := (.side 9 10 false (0))
theorem checked_10_5 : check 143 p_10_5 cert_10_5 = true := by decide +kernel
theorem safe_10_5 : ∀ m, compatible p_10_5 m → WeightedBound 143 m := sound 143 _ cert_10_5 (by decide) checked_10_5
def p_10_6 := refine p_10 (4,false) (some ⟨true,false,1⟩)
def cert_10_6 : Tree := (.side 9 10 false (0))
theorem checked_10_6 : check 143 p_10_6 cert_10_6 = true := by decide +kernel
theorem safe_10_6 : ∀ m, compatible p_10_6 m → WeightedBound 143 m := sound 143 _ cert_10_6 (by decide) checked_10_6
def p_10_7 := refine p_10 (4,false) (some ⟨true,true,1⟩)
def cert_10_7 : Tree := (.side 14 5 false (-1))
theorem checked_10_7 : check 143 p_10_7 cert_10_7 = true := by decide +kernel
theorem safe_10_7 : ∀ m, compatible p_10_7 m → WeightedBound 143 m := sound 143 _ cert_10_7 (by decide) checked_10_7
def p_10_8 := refine p_10 (4,false) (some ⟨false,false,2⟩)
def cert_10_8 : Tree := (.side 0 20 false (2))
theorem checked_10_8 : check 143 p_10_8 cert_10_8 = true := by decide +kernel
theorem safe_10_8 : ∀ m, compatible p_10_8 m → WeightedBound 143 m := sound 143 _ cert_10_8 (by decide) checked_10_8
def p_10_9 := refine p_10 (4,false) (some ⟨false,true,2⟩)
def cert_10_9 : Tree := (.side 12 7 false (-1))
theorem checked_10_9 : check 143 p_10_9 cert_10_9 = true := by decide +kernel
theorem safe_10_9 : ∀ m, compatible p_10_9 m → WeightedBound 143 m := sound 143 _ cert_10_9 (by decide) checked_10_9
def p_10_10 := refine p_10 (4,false) (some ⟨true,false,2⟩)
def cert_10_10 : Tree := (.side 12 7 false (-1))
theorem checked_10_10 : check 143 p_10_10 cert_10_10 = true := by decide +kernel
theorem safe_10_10 : ∀ m, compatible p_10_10 m → WeightedBound 143 m := sound 143 _ cert_10_10 (by decide) checked_10_10
def p_10_11 := refine p_10 (4,false) (some ⟨true,true,2⟩)
def cert_10_11 : Tree := (.side 7 20 false (1))
theorem checked_10_11 : check 143 p_10_11 cert_10_11 = true := by decide +kernel
theorem safe_10_11 : ∀ m, compatible p_10_11 m → WeightedBound 143 m := sound 143 _ cert_10_11 (by decide) checked_10_11
def p_10_12 := refine p_10 (4,false) (some ⟨false,false,3⟩)
def cert_10_12 : Tree := (.side 7 14 false (1))
theorem checked_10_12 : check 143 p_10_12 cert_10_12 = true := by decide +kernel
theorem safe_10_12 : ∀ m, compatible p_10_12 m → WeightedBound 143 m := sound 143 _ cert_10_12 (by decide) checked_10_12
def p_10_13 := refine p_10 (4,false) (some ⟨false,true,3⟩)
def cert_10_13 : Tree := (.side 7 14 false (1))
theorem checked_10_13 : check 143 p_10_13 cert_10_13 = true := by decide +kernel
theorem safe_10_13 : ∀ m, compatible p_10_13 m → WeightedBound 143 m := sound 143 _ cert_10_13 (by decide) checked_10_13
def p_10_14 := refine p_10 (4,false) (some ⟨true,false,3⟩)
def cert_10_14 : Tree := (.side 7 14 false (1))
theorem checked_10_14 : check 143 p_10_14 cert_10_14 = true := by decide +kernel
theorem safe_10_14 : ∀ m, compatible p_10_14 m → WeightedBound 143 m := sound 143 _ cert_10_14 (by decide) checked_10_14
def p_10_15 := refine p_10 (4,false) (some ⟨true,true,3⟩)
def cert_10_15 : Tree := (.side 7 18 false (1))
theorem checked_10_15 : check 143 p_10_15 cert_10_15 = true := by decide +kernel
theorem safe_10_15 : ∀ m, compatible p_10_15 m → WeightedBound 143 m := sound 143 _ cert_10_15 (by decide) checked_10_15
def p_10_16 := refine p_10 (4,false) (some ⟨false,false,4⟩)
def cert_10_16 : Tree := (.side 18 1 false (-4))
theorem checked_10_16 : check 143 p_10_16 cert_10_16 = true := by decide +kernel
theorem safe_10_16 : ∀ m, compatible p_10_16 m → WeightedBound 143 m := sound 143 _ cert_10_16 (by decide) checked_10_16
def p_10_17 := refine p_10 (4,false) (some ⟨false,true,4⟩)
def cert_10_17 : Tree := (.side 11 9 false (-1))
theorem checked_10_17 : check 143 p_10_17 cert_10_17 = true := by decide +kernel
theorem safe_10_17 : ∀ m, compatible p_10_17 m → WeightedBound 143 m := sound 143 _ cert_10_17 (by decide) checked_10_17
def p_10_18 := refine p_10 (4,false) (some ⟨true,false,4⟩)
def cert_10_18 : Tree := (.side 18 1 false (-4))
theorem checked_10_18 : check 143 p_10_18 cert_10_18 = true := by decide +kernel
theorem safe_10_18 : ∀ m, compatible p_10_18 m → WeightedBound 143 m := sound 143 _ cert_10_18 (by decide) checked_10_18
def p_10_19 := refine p_10 (4,false) (some ⟨true,true,4⟩)
def cert_10_19 : Tree := (.side 10 11 false (0))
theorem checked_10_19 : check 143 p_10_19 cert_10_19 = true := by decide +kernel
theorem safe_10_19 : ∀ m, compatible p_10_19 m → WeightedBound 143 m := sound 143 _ cert_10_19 (by decide) checked_10_19
def p_10_20 := refine p_10 (4,false) (some ⟨false,false,5⟩)
def cert_10_20 : Tree := (split 19 (5,false) 6 #[
(.side 0 20 false (2)),
(.side 13 7 false (-1)),
(.side 7 14 false (1)),
(.side 10 14 false (0)),
(.side 7 22 false (1)),
(.side 7 22 false (1)),
(.side 9 11 false (0)),
(.side 1 19 false (2)),
(.side 0 21 false (2)),
(.side 0 21 false (2)),
(.side 12 8 false (-1)),
(.side 7 21 false (1)),
(.side 7 15 false (1)),
(.side 7 15 false (1)),
(.side 7 15 false (1)),
(.side 7 19 false (1)),
(.side 18 2 false (-4)),
(.side 18 2 true (-5)),
(.side 18 2 false (-4)),
(.last 21 (5,true)),
(.side 19 1 false (-5)),
(.last 22 (5,true)),
(.side 19 1 false (-5)),
(.last 22 (5,true))])
theorem checked_10_20 : check 143 p_10_20 cert_10_20 = true := by decide +kernel
theorem safe_10_20 : ∀ m, compatible p_10_20 m → WeightedBound 143 m := sound 143 _ cert_10_20 (by decide) checked_10_20
def p_10_21 := refine p_10 (4,false) (some ⟨false,true,5⟩)
def cert_10_21 : Tree := (split 19 (5,false) 6 #[
(.side 13 7 false (-1)),
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 3 17 false (2)),
(.side 7 22 false (1)),
(.side 7 16 false (1)),
(.side 9 11 false (0)),
(.side 7 13 false (1)),
(.side 0 21 false (2)),
(.side 0 24 false (2)),
(.side 12 8 false (-1)),
(.side 10 10 false (0)),
(.side 7 15 false (1)),
(.side 8 12 false (0)),
(.side 7 15 false (1)),
(.side 7 17 false (1)),
(.side 18 2 true (-4)),
(.side 11 9 false (-1)),
(.last 21 (5,true)),
(.side 16 4 true (-4)),
(.side 19 1 false (-3)),
(.last 20 (5,true)),
(.side 19 1 false (-3)),
(.last 20 (5,true))])
theorem checked_10_21 : check 143 p_10_21 cert_10_21 = true := by decide +kernel
theorem safe_10_21 : ∀ m, compatible p_10_21 m → WeightedBound 143 m := sound 143 _ cert_10_21 (by decide) checked_10_21
def p_10_22 := refine p_10 (4,false) (some ⟨true,false,5⟩)
def cert_10_22 : Tree := (split 19 (5,false) 6 #[
(.side 13 7 false (-1)),
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 3 17 false (2)),
(.side 7 22 false (1)),
(.side 7 16 false (1)),
(.side 9 11 false (0)),
(.side 7 13 false (1)),
(.side 0 21 false (2)),
(.side 17 3 false (-3)),
(.side 12 8 false (-1)),
(.side 10 10 false (0)),
(.side 7 15 false (1)),
(.side 8 12 false (0)),
(.side 7 15 false (1)),
(.side 7 17 false (1)),
(.side 18 2 false (-4)),
(.side 11 9 false (-1)),
(.side 18 2 false (-4)),
(.side 16 4 false (-2)),
(.side 19 1 false (-5)),
(.last 20 (5,true)),
(.side 19 1 false (-5)),
(.last 20 (5,true))])
theorem checked_10_22 : check 143 p_10_22 cert_10_22 = true := by decide +kernel
theorem safe_10_22 : ∀ m, compatible p_10_22 m → WeightedBound 143 m := sound 143 _ cert_10_22 (by decide) checked_10_22
def p_10_23 := refine p_10 (4,false) (some ⟨true,true,5⟩)
def cert_10_23 : Tree := (split 19 (5,false) 6 #[
(.side 7 20 false (1)),
(.side 7 24 false (1)),
(.side 7 18 false (1)),
(.side 7 22 false (1)),
(.side 7 16 false (1)),
(.side 7 20 false (1)),
(.side 7 16 false (1)),
(.side 7 18 false (1)),
(.side 17 3 false (-3)),
(.side 6 26 false (2)),
(.side 17 3 false (-3)),
(.side 15 5 false (-1)),
(.side 8 12 false (0)),
(.side 14 7 false (-1)),
(.side 8 12 false (0)),
(.side 6 14 false (2)),
(.side 11 9 false (-1)),
(.side 7 22 false (1)),
(.side 11 9 false (-1)),
(.side 10 11 false (0)),
(.last 20 (5,true)),
(.last 20 (5,true)),
(.last 20 (5,true)),
(.last 20 (5,true))])
theorem checked_10_23 : check 143 p_10_23 cert_10_23 = true := by decide +kernel
theorem safe_10_23 : ∀ m, compatible p_10_23 m → WeightedBound 143 m := sound 143 _ cert_10_23 (by decide) checked_10_23
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 143 m := by
  apply split_safe 143 p_10 18 (4,false) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_10_0 | exact safe_10_1 | exact safe_10_2 | exact safe_10_3 | exact safe_10_4 | exact safe_10_5 | exact safe_10_6 | exact safe_10_7 | exact safe_10_8 | exact safe_10_9 | exact safe_10_10 | exact safe_10_11 | exact safe_10_12 | exact safe_10_13 | exact safe_10_14 | exact safe_10_15 | exact safe_10_16 | exact safe_10_17 | exact safe_10_18 | exact safe_10_19 | exact safe_10_20 | exact safe_10_21 | exact safe_10_22 | exact safe_10_23 | omega
def p_11 := refine parent (4,true) (some ⟨true,true,2⟩)
def cert_11 : Tree := (.side 7 13 false (1))
theorem checked_11 : check 143 p_11 cert_11 = true := by decide +kernel
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 143 m := sound 143 _ cert_11 (by decide) checked_11
def p_12 := refine parent (4,true) (some ⟨false,false,3⟩)
def cert_12 : Tree := (.side 7 7 false (1))
theorem checked_12 : check 143 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 143 m := sound 143 _ cert_12 (by decide) checked_12
def p_13 := refine parent (4,true) (some ⟨false,true,3⟩)
def cert_13 : Tree := (.side 7 7 false (1))
theorem checked_13 : check 143 p_13 cert_13 = true := by decide +kernel
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 143 m := sound 143 _ cert_13 (by decide) checked_13
def p_14 := refine parent (4,true) (some ⟨true,false,3⟩)
def cert_14 : Tree := (.side 7 7 false (1))
theorem checked_14 : check 143 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 143 m := sound 143 _ cert_14 (by decide) checked_14
def p_15 := refine parent (4,true) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 7 11 false (1))
theorem checked_15 : check 143 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 143 m := sound 143 _ cert_15 (by decide) checked_15
def p_16 := refine parent (4,true) (some ⟨false,false,4⟩)
def p_16_0 := refine p_16 (4,false) (some ⟨false,false,0⟩)
def cert_16_0 : Tree := (.side 0 13 false (2))
theorem checked_16_0 : check 143 p_16_0 cert_16_0 = true := by decide +kernel
theorem safe_16_0 : ∀ m, compatible p_16_0 m → WeightedBound 143 m := sound 143 _ cert_16_0 (by decide) checked_16_0
def p_16_1 := refine p_16 (4,false) (some ⟨false,true,0⟩)
def cert_16_1 : Tree := (.side 0 13 false (2))
theorem checked_16_1 : check 143 p_16_1 cert_16_1 = true := by decide +kernel
theorem safe_16_1 : ∀ m, compatible p_16_1 m → WeightedBound 143 m := sound 143 _ cert_16_1 (by decide) checked_16_1
def p_16_2 := refine p_16 (4,false) (some ⟨true,false,0⟩)
def cert_16_2 : Tree := (.side 7 7 false (1))
theorem checked_16_2 : check 143 p_16_2 cert_16_2 = true := by decide +kernel
theorem safe_16_2 : ∀ m, compatible p_16_2 m → WeightedBound 143 m := sound 143 _ cert_16_2 (by decide) checked_16_2
def p_16_3 := refine p_16 (4,false) (some ⟨true,true,0⟩)
def cert_16_3 : Tree := (.side 7 18 false (1))
theorem checked_16_3 : check 143 p_16_3 cert_16_3 = true := by decide +kernel
theorem safe_16_3 : ∀ m, compatible p_16_3 m → WeightedBound 143 m := sound 143 _ cert_16_3 (by decide) checked_16_3
def p_16_4 := refine p_16 (4,false) (some ⟨false,false,1⟩)
def cert_16_4 : Tree := (.side 7 15 false (1))
theorem checked_16_4 : check 143 p_16_4 cert_16_4 = true := by decide +kernel
theorem safe_16_4 : ∀ m, compatible p_16_4 m → WeightedBound 143 m := sound 143 _ cert_16_4 (by decide) checked_16_4
def p_16_5 := refine p_16 (4,false) (some ⟨false,true,1⟩)
def cert_16_5 : Tree := (.side 7 15 false (1))
theorem checked_16_5 : check 143 p_16_5 cert_16_5 = true := by decide +kernel
theorem safe_16_5 : ∀ m, compatible p_16_5 m → WeightedBound 143 m := sound 143 _ cert_16_5 (by decide) checked_16_5
def p_16_6 := refine p_16 (4,false) (some ⟨true,false,1⟩)
def cert_16_6 : Tree := (.side 9 4 false (0))
theorem checked_16_6 : check 143 p_16_6 cert_16_6 = true := by decide +kernel
theorem safe_16_6 : ∀ m, compatible p_16_6 m → WeightedBound 143 m := sound 143 _ cert_16_6 (by decide) checked_16_6
def p_16_7 := refine p_16 (4,false) (some ⟨true,true,1⟩)
def cert_16_7 : Tree := (.side 1 12 false (2))
theorem checked_16_7 : check 143 p_16_7 cert_16_7 = true := by decide +kernel
theorem safe_16_7 : ∀ m, compatible p_16_7 m → WeightedBound 143 m := sound 143 _ cert_16_7 (by decide) checked_16_7
def p_16_8 := refine p_16 (4,false) (some ⟨false,false,2⟩)
def cert_16_8 : Tree := (.side 0 14 false (2))
theorem checked_16_8 : check 143 p_16_8 cert_16_8 = true := by decide +kernel
theorem safe_16_8 : ∀ m, compatible p_16_8 m → WeightedBound 143 m := sound 143 _ cert_16_8 (by decide) checked_16_8
def p_16_9 := refine p_16 (4,false) (some ⟨false,true,2⟩)
def cert_16_9 : Tree := (.side 0 14 false (2))
theorem checked_16_9 : check 143 p_16_9 cert_16_9 = true := by decide +kernel
theorem safe_16_9 : ∀ m, compatible p_16_9 m → WeightedBound 143 m := sound 143 _ cert_16_9 (by decide) checked_16_9
def p_16_10 := refine p_16 (4,false) (some ⟨true,false,2⟩)
def cert_16_10 : Tree := (.side 11 7 false (-1))
theorem checked_16_10 : check 143 p_16_10 cert_16_10 = true := by decide +kernel
theorem safe_16_10 : ∀ m, compatible p_16_10 m → WeightedBound 143 m := sound 143 _ cert_16_10 (by decide) checked_16_10
def p_16_11 := refine p_16 (4,false) (some ⟨true,true,2⟩)
def cert_16_11 : Tree := (.side 7 14 false (1))
theorem checked_16_11 : check 143 p_16_11 cert_16_11 = true := by decide +kernel
theorem safe_16_11 : ∀ m, compatible p_16_11 m → WeightedBound 143 m := sound 143 _ cert_16_11 (by decide) checked_16_11
def p_16_12 := refine p_16 (4,false) (some ⟨false,false,3⟩)
def cert_16_12 : Tree := (.side 7 8 false (1))
theorem checked_16_12 : check 143 p_16_12 cert_16_12 = true := by decide +kernel
theorem safe_16_12 : ∀ m, compatible p_16_12 m → WeightedBound 143 m := sound 143 _ cert_16_12 (by decide) checked_16_12
def p_16_13 := refine p_16 (4,false) (some ⟨false,true,3⟩)
def cert_16_13 : Tree := (.side 7 8 false (1))
theorem checked_16_13 : check 143 p_16_13 cert_16_13 = true := by decide +kernel
theorem safe_16_13 : ∀ m, compatible p_16_13 m → WeightedBound 143 m := sound 143 _ cert_16_13 (by decide) checked_16_13
def p_16_14 := refine p_16 (4,false) (some ⟨true,false,3⟩)
def cert_16_14 : Tree := (.side 7 8 false (1))
theorem checked_16_14 : check 143 p_16_14 cert_16_14 = true := by decide +kernel
theorem safe_16_14 : ∀ m, compatible p_16_14 m → WeightedBound 143 m := sound 143 _ cert_16_14 (by decide) checked_16_14
def p_16_15 := refine p_16 (4,false) (some ⟨true,true,3⟩)
def cert_16_15 : Tree := (.side 7 12 false (1))
theorem checked_16_15 : check 143 p_16_15 cert_16_15 = true := by decide +kernel
theorem safe_16_15 : ∀ m, compatible p_16_15 m → WeightedBound 143 m := sound 143 _ cert_16_15 (by decide) checked_16_15
def p_16_16 := refine p_16 (4,false) (some ⟨false,false,4⟩)
def cert_16_16 : Tree := (.side 12 1 false (-2))
theorem checked_16_16 : check 143 p_16_16 cert_16_16 = true := by decide +kernel
theorem safe_16_16 : ∀ m, compatible p_16_16 m → WeightedBound 143 m := sound 143 _ cert_16_16 (by decide) checked_16_16
def p_16_17 := refine p_16 (4,false) (some ⟨false,true,4⟩)
def cert_16_17 : Tree := (.side 17 1 true (1))
theorem checked_16_17 : check 143 p_16_17 cert_16_17 = true := by decide +kernel
theorem safe_16_17 : ∀ m, compatible p_16_17 m → WeightedBound 143 m := sound 143 _ cert_16_17 (by decide) checked_16_17
def p_16_18 := refine p_16 (4,false) (some ⟨true,false,4⟩)
def cert_16_18 : Tree := (.side 12 1 false (-2))
theorem checked_16_18 : check 143 p_16_18 cert_16_18 = true := by decide +kernel
theorem safe_16_18 : ∀ m, compatible p_16_18 m → WeightedBound 143 m := sound 143 _ cert_16_18 (by decide) checked_16_18
def p_16_19 := refine p_16 (4,false) (some ⟨true,true,4⟩)
def cert_16_19 : Tree := (.side 21 1 true (-3))
theorem checked_16_19 : check 143 p_16_19 cert_16_19 = true := by decide +kernel
theorem safe_16_19 : ∀ m, compatible p_16_19 m → WeightedBound 143 m := sound 143 _ cert_16_19 (by decide) checked_16_19
def p_16_20 := refine p_16 (4,false) (some ⟨false,false,5⟩)
def cert_16_20 : Tree := (split 13 (5,false) 6 #[
(.side 0 14 false (2)),
(.side 0 14 false (2)),
(.side 7 8 false (1)),
(.side 7 19 false (1)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (0)),
(.side 1 13 false (2)),
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.side 11 8 false (-1)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.side 12 2 false (-2)),
(.side 12 2 true (-3)),
(.side 12 2 false (-2)),
(.last 15 (5,true)),
(.side 13 1 false (-3)),
(.last 18 (5,true)),
(.side 13 1 false (-3)),
(.last 18 (5,true))])
theorem checked_16_20 : check 143 p_16_20 cert_16_20 = true := by decide +kernel
theorem safe_16_20 : ∀ m, compatible p_16_20 m → WeightedBound 143 m := sound 143 _ cert_16_20 (by decide) checked_16_20
def p_16_21 := refine p_16 (4,false) (some ⟨false,true,5⟩)
def cert_16_21 : Tree := (split 13 (5,false) 6 #[
(.side 0 14 false (2)),
(.side 0 21 true (-2)),
(.side 7 8 false (1)),
(.side 19 19 false (2)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (0)),
(.side 1 13 false (2)),
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.side 11 8 false (-1)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.side 12 2 true (-2)),
(.side 17 2 true (1)),
(.last 15 (5,true)),
(.side 18 2 true (0)),
(.side 13 1 false (-1)),
(.last 16 (5,true)),
(.side 13 1 false (-1)),
(.last 16 (5,true))])
theorem checked_16_21 : check 143 p_16_21 cert_16_21 = true := by decide +kernel
theorem safe_16_21 : ∀ m, compatible p_16_21 m → WeightedBound 143 m := sound 143 _ cert_16_21 (by decide) checked_16_21
def p_16_22 := refine p_16 (4,false) (some ⟨true,false,5⟩)
def cert_16_22 : Tree := (split 13 (5,false) 6 #[
(.side 11 7 false (-1)),
(.side 7 14 false (1)),
(.side 7 8 false (1)),
(.side 3 11 false (2)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 9 5 false (0)),
(.side 7 7 false (1)),
(.side 0 15 false (2)),
(.side 12 3 false (-2)),
(.side 11 8 false (-1)),
(.side 10 4 false (0)),
(.side 7 9 false (1)),
(.side 8 6 false (0)),
(.side 7 9 false (1)),
(.side 7 11 false (1)),
(.side 12 2 false (-2)),
(.side 11 3 false (-1)),
(.side 12 2 false (-2)),
(.side 11 4 false (-1)),
(.side 13 1 false (-3)),
(.last 14 (5,true)),
(.side 13 1 false (-3)),
(.last 14 (5,true))])
theorem checked_16_22 : check 143 p_16_22 cert_16_22 = true := by decide +kernel
theorem safe_16_22 : ∀ m, compatible p_16_22 m → WeightedBound 143 m := sound 143 _ cert_16_22 (by decide) checked_16_22
def p_16_23 := refine p_16 (4,false) (some ⟨true,true,5⟩)
def cert_16_23 : Tree := (split 13 (5,false) 6 #[
(.side 7 14 false (1)),
(.side 33 15 false (1)),
(.side 7 12 false (1)),
(.side 6 25 false (2)),
(.side 7 10 false (1)),
(.side 7 20 false (1)),
(.side 7 10 false (1)),
(.side 7 18 false (1)),
(.side 12 3 false (-1)),
(.side 7 20 false (1)),
(.side 12 3 false (-1)),
(.side 2 12 false (2)),
(.side 8 6 false (0)),
(.side 7 14 false (1)),
(.side 8 6 false (0)),
(.side 4 10 false (2)),
(.side 11 3 false (-1)),
(.side 17 2 true (1)),
(.side 11 3 false (-1)),
(.side 21 2 true (-3)),
(.last 14 (5,true)),
(.last 16 (5,true)),
(.last 14 (5,true)),
(.last 16 (5,true))])
theorem checked_16_23 : check 143 p_16_23 cert_16_23 = true := by decide +kernel
theorem safe_16_23 : ∀ m, compatible p_16_23 m → WeightedBound 143 m := sound 143 _ cert_16_23 (by decide) checked_16_23
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 143 m := by
  apply split_safe 143 p_16 12 (4,false) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_16_0 | exact safe_16_1 | exact safe_16_2 | exact safe_16_3 | exact safe_16_4 | exact safe_16_5 | exact safe_16_6 | exact safe_16_7 | exact safe_16_8 | exact safe_16_9 | exact safe_16_10 | exact safe_16_11 | exact safe_16_12 | exact safe_16_13 | exact safe_16_14 | exact safe_16_15 | exact safe_16_16 | exact safe_16_17 | exact safe_16_18 | exact safe_16_19 | exact safe_16_20 | exact safe_16_21 | exact safe_16_22 | exact safe_16_23 | omega
def p_17 := refine parent (4,true) (some ⟨false,true,4⟩)
def p_17_0 := refine p_17 (4,false) (some ⟨false,false,0⟩)
def cert_17_0 : Tree := (.side 0 13 false (2))
theorem checked_17_0 : check 143 p_17_0 cert_17_0 = true := by decide +kernel
theorem safe_17_0 : ∀ m, compatible p_17_0 m → WeightedBound 143 m := sound 143 _ cert_17_0 (by decide) checked_17_0
def p_17_1 := refine p_17 (4,false) (some ⟨false,true,0⟩)
def cert_17_1 : Tree := (.side 0 20 true (-1))
theorem checked_17_1 : check 143 p_17_1 cert_17_1 = true := by decide +kernel
theorem safe_17_1 : ∀ m, compatible p_17_1 m → WeightedBound 143 m := sound 143 _ cert_17_1 (by decide) checked_17_1
def p_17_2 := refine p_17 (4,false) (some ⟨true,false,0⟩)
def cert_17_2 : Tree := (.side 7 7 false (1))
theorem checked_17_2 : check 143 p_17_2 cert_17_2 = true := by decide +kernel
theorem safe_17_2 : ∀ m, compatible p_17_2 m → WeightedBound 143 m := sound 143 _ cert_17_2 (by decide) checked_17_2
def p_17_3 := refine p_17 (4,false) (some ⟨true,true,0⟩)
def cert_17_3 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,2),(true,1)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty,.empty]⟩)
theorem checked_17_3 : check 143 p_17_3 cert_17_3 = true := by decide +kernel
theorem safe_17_3 : ∀ m, compatible p_17_3 m → WeightedBound 143 m := sound 143 _ cert_17_3 (by decide) checked_17_3
def p_17_4 := refine p_17 (4,false) (some ⟨false,false,1⟩)
def cert_17_4 : Tree := (.side 7 15 false (1))
theorem checked_17_4 : check 143 p_17_4 cert_17_4 = true := by decide +kernel
theorem safe_17_4 : ∀ m, compatible p_17_4 m → WeightedBound 143 m := sound 143 _ cert_17_4 (by decide) checked_17_4
def p_17_5 := refine p_17 (4,false) (some ⟨false,true,1⟩)
def cert_17_5 : Tree := (.side 13 15 false (4))
theorem checked_17_5 : check 143 p_17_5 cert_17_5 = true := by decide +kernel
theorem safe_17_5 : ∀ m, compatible p_17_5 m → WeightedBound 143 m := sound 143 _ cert_17_5 (by decide) checked_17_5
def p_17_6 := refine p_17 (4,false) (some ⟨true,false,1⟩)
def cert_17_6 : Tree := (.side 9 4 true (-1))
theorem checked_17_6 : check 143 p_17_6 cert_17_6 = true := by decide +kernel
theorem safe_17_6 : ∀ m, compatible p_17_6 m → WeightedBound 143 m := sound 143 _ cert_17_6 (by decide) checked_17_6
def p_17_7 := refine p_17 (4,false) (some ⟨true,true,1⟩)
def cert_17_7 : Tree := (.side 1 16 true (-1))
theorem checked_17_7 : check 143 p_17_7 cert_17_7 = true := by decide +kernel
theorem safe_17_7 : ∀ m, compatible p_17_7 m → WeightedBound 143 m := sound 143 _ cert_17_7 (by decide) checked_17_7
def p_17_8 := refine p_17 (4,false) (some ⟨false,false,2⟩)
def cert_17_8 : Tree := (.side 0 14 false (2))
theorem checked_17_8 : check 143 p_17_8 cert_17_8 = true := by decide +kernel
theorem safe_17_8 : ∀ m, compatible p_17_8 m → WeightedBound 143 m := sound 143 _ cert_17_8 (by decide) checked_17_8
def p_17_9 := refine p_17 (4,false) (some ⟨false,true,2⟩)
def cert_17_9 : Tree := (.side 0 20 true (-1))
theorem checked_17_9 : check 143 p_17_9 cert_17_9 = true := by decide +kernel
theorem safe_17_9 : ∀ m, compatible p_17_9 m → WeightedBound 143 m := sound 143 _ cert_17_9 (by decide) checked_17_9
def p_17_10 := refine p_17 (4,false) (some ⟨true,false,2⟩)
def cert_17_10 : Tree := (.side 7 20 false (1))
theorem checked_17_10 : check 143 p_17_10 cert_17_10 = true := by decide +kernel
theorem safe_17_10 : ∀ m, compatible p_17_10 m → WeightedBound 143 m := sound 143 _ cert_17_10 (by decide) checked_17_10
def p_17_11 := refine p_17 (4,false) (some ⟨true,true,2⟩)
def cert_17_11 : Tree := (.side 7 14 false (1))
theorem checked_17_11 : check 143 p_17_11 cert_17_11 = true := by decide +kernel
theorem safe_17_11 : ∀ m, compatible p_17_11 m → WeightedBound 143 m := sound 143 _ cert_17_11 (by decide) checked_17_11
def p_17_12 := refine p_17 (4,false) (some ⟨false,false,3⟩)
def cert_17_12 : Tree := (.side 7 8 false (1))
theorem checked_17_12 : check 143 p_17_12 cert_17_12 = true := by decide +kernel
theorem safe_17_12 : ∀ m, compatible p_17_12 m → WeightedBound 143 m := sound 143 _ cert_17_12 (by decide) checked_17_12
def p_17_13 := refine p_17 (4,false) (some ⟨false,true,3⟩)
def cert_17_13 : Tree := (.side 7 8 true (-1))
theorem checked_17_13 : check 143 p_17_13 cert_17_13 = true := by decide +kernel
theorem safe_17_13 : ∀ m, compatible p_17_13 m → WeightedBound 143 m := sound 143 _ cert_17_13 (by decide) checked_17_13
def p_17_14 := refine p_17 (4,false) (some ⟨true,false,3⟩)
def cert_17_14 : Tree := (.side 7 8 false (1))
theorem checked_17_14 : check 143 p_17_14 cert_17_14 = true := by decide +kernel
theorem safe_17_14 : ∀ m, compatible p_17_14 m → WeightedBound 143 m := sound 143 _ cert_17_14 (by decide) checked_17_14
def p_17_15 := refine p_17 (4,false) (some ⟨true,true,3⟩)
def cert_17_15 : Tree := (.side 7 12 false (1))
theorem checked_17_15 : check 143 p_17_15 cert_17_15 = true := by decide +kernel
theorem safe_17_15 : ∀ m, compatible p_17_15 m → WeightedBound 143 m := sound 143 _ cert_17_15 (by decide) checked_17_15
def p_17_16 := refine p_17 (4,false) (some ⟨false,false,4⟩)
def cert_17_16 : Tree := (.side 12 1 false (0))
theorem checked_17_16 : check 143 p_17_16 cert_17_16 = true := by decide +kernel
theorem safe_17_16 : ∀ m, compatible p_17_16 m → WeightedBound 143 m := sound 143 _ cert_17_16 (by decide) checked_17_16
def p_17_17 := refine p_17 (4,false) (some ⟨false,true,4⟩)
def cert_17_17 : Tree := (.side 15 1 true (3))
theorem checked_17_17 : check 143 p_17_17 cert_17_17 = true := by decide +kernel
theorem safe_17_17 : ∀ m, compatible p_17_17 m → WeightedBound 143 m := sound 143 _ cert_17_17 (by decide) checked_17_17
def p_17_18 := refine p_17 (4,false) (some ⟨true,false,4⟩)
def cert_17_18 : Tree := (.side 12 1 false (0))
theorem checked_17_18 : check 143 p_17_18 cert_17_18 = true := by decide +kernel
theorem safe_17_18 : ∀ m, compatible p_17_18 m → WeightedBound 143 m := sound 143 _ cert_17_18 (by decide) checked_17_18
def p_17_19 := refine p_17 (4,false) (some ⟨true,true,4⟩)
def cert_17_19 : Tree := (.side 15 1 true (3))
theorem checked_17_19 : check 143 p_17_19 cert_17_19 = true := by decide +kernel
theorem safe_17_19 : ∀ m, compatible p_17_19 m → WeightedBound 143 m := sound 143 _ cert_17_19 (by decide) checked_17_19
def p_17_20 := refine p_17 (4,false) (some ⟨false,false,5⟩)
def cert_17_20 : Tree := (split 13 (5,false) 6 #[
(.side 0 14 false (2)),
(.side 0 20 true (-1)),
(.side 7 8 false (1)),
(.side 28 19 false (2)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (0)),
(.side 1 13 false (2)),
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.side 12 10 false (0)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.side 12 2 false (0)),
(.side 12 2 true (-1)),
(.side 12 2 false (0)),
(.last 15 (5,true)),
(.side 13 1 false (-1)),
(.last 16 (5,true)),
(.side 13 1 false (-1)),
(.last 16 (5,true))])
theorem checked_17_20 : check 143 p_17_20 cert_17_20 = true := by decide +kernel
theorem safe_17_20 : ∀ m, compatible p_17_20 m → WeightedBound 143 m := sound 143 _ cert_17_20 (by decide) checked_17_20
def p_17_21 := refine p_17 (4,false) (some ⟨false,true,5⟩)
def cert_17_21 : Tree := (split 13 (5,false) 6 #[
(.side 0 20 true (-1)),
(.side 0 36 true (-1)),
(.side 7 8 true (-1)),
(.side 3 11 true (-1)),
(.side 7 16 false (1)),
(.side 19 21 true (-1)),
(.last 18 (5,true)),
(.side 1 20 true (-1)),
(.side 0 15 false (2)),
(.side 0 18 true (-1)),
(.last 20 (5,true)),
(.side 14 15 false (4)),
(.side 7 9 false (1)),
(.side 14 9 true (1)),
(.side 7 9 false (1)),
(.side 14 13 false (2)),
(.side 12 2 true (0)),
(.side 15 2 true (3)),
(.last 15 (5,true)),
(.side 15 2 true (3)),
(.side 13 1 false (1)),
(.last 14 (5,true)),
(.side 13 1 false (1)),
(.last 14 (5,true))])
theorem checked_17_21 : check 143 p_17_21 cert_17_21 = true := by decide +kernel
theorem safe_17_21 : ∀ m, compatible p_17_21 m → WeightedBound 143 m := sound 143 _ cert_17_21 (by decide) checked_17_21
def p_17_22 := refine p_17 (4,false) (some ⟨true,false,5⟩)
def cert_17_22 : Tree := (split 13 (5,false) 6 #[
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 7 8 false (1)),
(.side 3 11 false (2)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 9 5 false (0)),
(.side 7 7 false (1)),
(.side 0 15 false (2)),
(.side 12 3 false (0)),
(.side 12 10 false (0)),
(.side 10 4 true (-1)),
(.side 7 9 false (1)),
(.side 8 6 true (-1)),
(.side 7 9 false (1)),
(.side 7 11 false (1)),
(.side 12 2 false (0)),
(.side 18 3 true (2)),
(.side 12 2 false (0)),
(.side 18 3 true (2)),
(.side 13 1 false (-1)),
(.last 14 (5,true)),
(.side 13 1 false (-1)),
(.last 14 (5,true))])
theorem checked_17_22 : check 143 p_17_22 cert_17_22 = true := by decide +kernel
theorem safe_17_22 : ∀ m, compatible p_17_22 m → WeightedBound 143 m := sound 143 _ cert_17_22 (by decide) checked_17_22
def p_17_23 := refine p_17 (4,false) (some ⟨true,true,5⟩)
def cert_17_23 : Tree := (split 13 (5,false) 6 #[
(.side 7 14 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2),(true,6)],[(false,5)],[(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[(false,12),(false,4)],[(true,12),(true,4)],[(false,5),(false,13)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) (.branch .empty (.branch .leaf (.branch .leaf .leaf))))) (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty)),.empty]⟩),
(.side 7 12 false (1)),
(.side 6 26 false (3)),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,8)],[(true,2)],[(false,3)],[(true,3)],[],[(true,5)],[],[],[(true,8)]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[(false,4),(false,12)],[(true,4),(true,12)],[(false,9),(false,5)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch .leaf (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) .leaf) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) .leaf))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) .leaf) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) .leaf))) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) .empty)),.empty]⟩),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(true,2)],[(false,2)],[(true,4),(true,8)],[(true,5)],[(true,6)],[(false,6)]],#[(0,1),(0,2),(4,3),(0,0),(0,5),(0,6),(8,7),(0,0),(0,5)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[(false,3),(true,3),(false,6),(true,6),(false,7),(false,10),(true,10),(false,11),(true,11),(false,13),(true,13),(false,18),(false,21),(true,21),(false,24),(true,24),(true,26),(false,27),(true,27)],[(false,4),(false,16),(false,20),(false,23)],[(true,4)],[(false,5)],[(true,5)],[(true,7)],[(false,8),(false,22)],[(true,8),(true,19),(true,22)],[(false,9)],[(true,9)],[(false,12),(false,25)],[(true,12),(true,25)],[(false,14)],[(true,14)],[(false,15)],[(true,15),(true,17)],[(true,16)],[(false,17)],[(true,18)],[(false,19)],[(true,20),(true,23)],[(false,26)]],#[(0,1),(2,3),(4,5),(6,6),(7,8),(9,10),(6,6),(6,11),(12,13),(14,15),(6,6),(6,6),(16,17),(6,6),(18,19),(20,21),(7,22),(23,21),(6,24),(25,13),(7,26),(6,6),(12,13),(7,26),(6,6),(16,17),(27,6),(6,6)]⟩,#[(.branch .leaf (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf))) (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .leaf (.branch .empty (.branch .empty .leaf)))) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .leaf (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty .leaf)))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .leaf)) (.branch (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) (.branch .leaf (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))) (.branch (.branch .leaf (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf)))) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .leaf (.branch .empty (.branch .empty .leaf)))) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) (.branch .leaf (.branch .empty (.branch .leaf .leaf)))) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .empty .leaf))) (.branch .leaf (.branch .empty (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf)))) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .leaf (.branch .empty (.branch .empty .leaf)))) .empty)))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf))) (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .leaf))) (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty))),.empty]⟩),
(.side 12 3 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,6)],[(false,3),(false,7),(false,5)],[(true,3),(true,7),(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[(false,12)],[(true,12)],[(false,5),(false,13)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .leaf) (.branch (.branch .leaf (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch .leaf (.branch (.branch .empty .leaf) (.branch .leaf .leaf))))) .empty)),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf)))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) (.branch .leaf .leaf)))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .leaf) (.branch (.branch .leaf (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch .leaf (.branch (.branch .empty .leaf) (.branch .leaf .leaf))))) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch .leaf (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) .empty)),.empty]⟩),
(.side 12 3 false (1)),
(.side 2 16 true (-1)),
(.side 8 6 true (-1)),
(.side 27 14 false (1)),
(.last 19 (5,true)),
(.side 6 8 true (-1)),
(.last 16 (5,true)),
(.side 15 2 true (3)),
(.side 15 4 true (1)),
(.side 15 2 true (3)),
(.last 14 (5,true)),
(.last 14 (5,true)),
(.last 14 (5,true)),
(.last 14 (5,true))])
theorem checked_17_23 : check 143 p_17_23 cert_17_23 = true := by decide +kernel
theorem safe_17_23 : ∀ m, compatible p_17_23 m → WeightedBound 143 m := sound 143 _ cert_17_23 (by decide) checked_17_23
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 143 m := by
  apply split_safe 143 p_17 12 (4,false) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_17_0 | exact safe_17_1 | exact safe_17_2 | exact safe_17_3 | exact safe_17_4 | exact safe_17_5 | exact safe_17_6 | exact safe_17_7 | exact safe_17_8 | exact safe_17_9 | exact safe_17_10 | exact safe_17_11 | exact safe_17_12 | exact safe_17_13 | exact safe_17_14 | exact safe_17_15 | exact safe_17_16 | exact safe_17_17 | exact safe_17_18 | exact safe_17_19 | exact safe_17_20 | exact safe_17_21 | exact safe_17_22 | exact safe_17_23 | omega
def p_18 := refine parent (4,true) (some ⟨true,false,4⟩)
def p_18_0 := refine p_18 (4,false) (some ⟨false,false,0⟩)
def cert_18_0 : Tree := (.side 11 6 false (-1))
theorem checked_18_0 : check 143 p_18_0 cert_18_0 = true := by decide +kernel
theorem safe_18_0 : ∀ m, compatible p_18_0 m → WeightedBound 143 m := sound 143 _ cert_18_0 (by decide) checked_18_0
def p_18_1 := refine p_18 (4,false) (some ⟨false,true,0⟩)
def cert_18_1 : Tree := (.side 7 13 false (1))
theorem checked_18_1 : check 143 p_18_1 cert_18_1 = true := by decide +kernel
theorem safe_18_1 : ∀ m, compatible p_18_1 m → WeightedBound 143 m := sound 143 _ cert_18_1 (by decide) checked_18_1
def p_18_2 := refine p_18 (4,false) (some ⟨true,false,0⟩)
def cert_18_2 : Tree := (.side 7 7 false (1))
theorem checked_18_2 : check 143 p_18_2 cert_18_2 = true := by decide +kernel
theorem safe_18_2 : ∀ m, compatible p_18_2 m → WeightedBound 143 m := sound 143 _ cert_18_2 (by decide) checked_18_2
def p_18_3 := refine p_18 (4,false) (some ⟨true,true,0⟩)
def cert_18_3 : Tree := (.side 3 10 false (2))
theorem checked_18_3 : check 143 p_18_3 cert_18_3 = true := by decide +kernel
theorem safe_18_3 : ∀ m, compatible p_18_3 m → WeightedBound 143 m := sound 143 _ cert_18_3 (by decide) checked_18_3
def p_18_4 := refine p_18 (4,false) (some ⟨false,false,1⟩)
def cert_18_4 : Tree := (.side 7 15 false (1))
theorem checked_18_4 : check 143 p_18_4 cert_18_4 = true := by decide +kernel
theorem safe_18_4 : ∀ m, compatible p_18_4 m → WeightedBound 143 m := sound 143 _ cert_18_4 (by decide) checked_18_4
def p_18_5 := refine p_18 (4,false) (some ⟨false,true,1⟩)
def cert_18_5 : Tree := (.side 7 9 false (1))
theorem checked_18_5 : check 143 p_18_5 cert_18_5 = true := by decide +kernel
theorem safe_18_5 : ∀ m, compatible p_18_5 m → WeightedBound 143 m := sound 143 _ cert_18_5 (by decide) checked_18_5
def p_18_6 := refine p_18 (4,false) (some ⟨true,false,1⟩)
def cert_18_6 : Tree := (.side 9 4 false (0))
theorem checked_18_6 : check 143 p_18_6 cert_18_6 = true := by decide +kernel
theorem safe_18_6 : ∀ m, compatible p_18_6 m → WeightedBound 143 m := sound 143 _ cert_18_6 (by decide) checked_18_6
def p_18_7 := refine p_18 (4,false) (some ⟨true,true,1⟩)
def cert_18_7 : Tree := (.side 7 6 false (1))
theorem checked_18_7 : check 143 p_18_7 cert_18_7 = true := by decide +kernel
theorem safe_18_7 : ∀ m, compatible p_18_7 m → WeightedBound 143 m := sound 143 _ cert_18_7 (by decide) checked_18_7
def p_18_8 := refine p_18 (4,false) (some ⟨false,false,2⟩)
def cert_18_8 : Tree := (.side 0 14 false (2))
theorem checked_18_8 : check 143 p_18_8 cert_18_8 = true := by decide +kernel
theorem safe_18_8 : ∀ m, compatible p_18_8 m → WeightedBound 143 m := sound 143 _ cert_18_8 (by decide) checked_18_8
def p_18_9 := refine p_18 (4,false) (some ⟨false,true,2⟩)
def cert_18_9 : Tree := (.side 0 16 false (2))
theorem checked_18_9 : check 143 p_18_9 cert_18_9 = true := by decide +kernel
theorem safe_18_9 : ∀ m, compatible p_18_9 m → WeightedBound 143 m := sound 143 _ cert_18_9 (by decide) checked_18_9
def p_18_10 := refine p_18 (4,false) (some ⟨true,false,2⟩)
def cert_18_10 : Tree := (.side 11 7 false (-1))
theorem checked_18_10 : check 143 p_18_10 cert_18_10 = true := by decide +kernel
theorem safe_18_10 : ∀ m, compatible p_18_10 m → WeightedBound 143 m := sound 143 _ cert_18_10 (by decide) checked_18_10
def p_18_11 := refine p_18 (4,false) (some ⟨true,true,2⟩)
def cert_18_11 : Tree := (.side 10 3 false (0))
theorem checked_18_11 : check 143 p_18_11 cert_18_11 = true := by decide +kernel
theorem safe_18_11 : ∀ m, compatible p_18_11 m → WeightedBound 143 m := sound 143 _ cert_18_11 (by decide) checked_18_11
def p_18_12 := refine p_18 (4,false) (some ⟨false,false,3⟩)
def cert_18_12 : Tree := (.side 7 8 false (1))
theorem checked_18_12 : check 143 p_18_12 cert_18_12 = true := by decide +kernel
theorem safe_18_12 : ∀ m, compatible p_18_12 m → WeightedBound 143 m := sound 143 _ cert_18_12 (by decide) checked_18_12
def p_18_13 := refine p_18 (4,false) (some ⟨false,true,3⟩)
def cert_18_13 : Tree := (.side 8 5 false (0))
theorem checked_18_13 : check 143 p_18_13 cert_18_13 = true := by decide +kernel
theorem safe_18_13 : ∀ m, compatible p_18_13 m → WeightedBound 143 m := sound 143 _ cert_18_13 (by decide) checked_18_13
def p_18_14 := refine p_18 (4,false) (some ⟨true,false,3⟩)
def cert_18_14 : Tree := (.side 7 8 false (1))
theorem checked_18_14 : check 143 p_18_14 cert_18_14 = true := by decide +kernel
theorem safe_18_14 : ∀ m, compatible p_18_14 m → WeightedBound 143 m := sound 143 _ cert_18_14 (by decide) checked_18_14
def p_18_15 := refine p_18 (4,false) (some ⟨true,true,3⟩)
def cert_18_15 : Tree := (.side 7 10 false (1))
theorem checked_18_15 : check 143 p_18_15 cert_18_15 = true := by decide +kernel
theorem safe_18_15 : ∀ m, compatible p_18_15 m → WeightedBound 143 m := sound 143 _ cert_18_15 (by decide) checked_18_15
def p_18_16 := refine p_18 (4,false) (some ⟨false,false,4⟩)
def cert_18_16 : Tree := (.side 12 1 false (-2))
theorem checked_18_16 : check 143 p_18_16 cert_18_16 = true := by decide +kernel
theorem safe_18_16 : ∀ m, compatible p_18_16 m → WeightedBound 143 m := sound 143 _ cert_18_16 (by decide) checked_18_16
def p_18_17 := refine p_18 (4,false) (some ⟨false,true,4⟩)
def cert_18_17 : Tree := (.side 11 2 true (-2))
theorem checked_18_17 : check 143 p_18_17 cert_18_17 = true := by decide +kernel
theorem safe_18_17 : ∀ m, compatible p_18_17 m → WeightedBound 143 m := sound 143 _ cert_18_17 (by decide) checked_18_17
def p_18_18 := refine p_18 (4,false) (some ⟨true,false,4⟩)
def cert_18_18 : Tree := (.side 12 1 false (-2))
theorem checked_18_18 : check 143 p_18_18 cert_18_18 = true := by decide +kernel
theorem safe_18_18 : ∀ m, compatible p_18_18 m → WeightedBound 143 m := sound 143 _ cert_18_18 (by decide) checked_18_18
def p_18_19 := refine p_18 (4,false) (some ⟨true,true,4⟩)
def cert_18_19 : Tree := (.side 11 3 false (-1))
theorem checked_18_19 : check 143 p_18_19 cert_18_19 = true := by decide +kernel
theorem safe_18_19 : ∀ m, compatible p_18_19 m → WeightedBound 143 m := sound 143 _ cert_18_19 (by decide) checked_18_19
def p_18_20 := refine p_18 (4,false) (some ⟨false,false,5⟩)
def cert_18_20 : Tree := (split 13 (5,false) 6 #[
(.side 0 14 false (2)),
(.side 7 8 false (1)),
(.side 7 8 false (1)),
(.side 7 13 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (0)),
(.side 9 5 false (0)),
(.side 11 6 false (-1)),
(.side 0 15 false (2)),
(.side 11 8 false (-1)),
(.side 11 8 false (-1)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.side 12 2 false (-2)),
(.side 12 2 true (-3)),
(.side 12 2 false (-2)),
(.last 15 (5,true)),
(.side 13 1 false (-3)),
(.last 15 (5,true)),
(.side 13 1 false (-3)),
(.last 15 (5,true))])
theorem checked_18_20 : check 143 p_18_20 cert_18_20 = true := by decide +kernel
theorem safe_18_20 : ∀ m, compatible p_18_20 m → WeightedBound 143 m := sound 143 _ cert_18_20 (by decide) checked_18_20
def p_18_21 := refine p_18 (4,false) (some ⟨false,true,5⟩)
def cert_18_21 : Tree := (split 13 (5,true) 6 #[
(.side 0 14 false (2)),
(.side 0 35 false (2)),
(.side 7 8 false (1)),
(.side 5 17 false (2)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (0)),
(.side 1 13 false (2)),
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.side 11 8 false (-1)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.last 15 (5,false)),
(.last 15 (5,false)),
(.side 12 2 true (-2)),
(.last 15 (5,false)),
(.last 14 (5,false)),
(.last 14 (5,false)),
(.last 14 (5,false)),
(.last 14 (5,false))])
theorem checked_18_21 : check 143 p_18_21 cert_18_21 = true := by decide +kernel
theorem safe_18_21 : ∀ m, compatible p_18_21 m → WeightedBound 143 m := sound 143 _ cert_18_21 (by decide) checked_18_21
def p_18_22 := refine p_18 (4,false) (some ⟨true,false,5⟩)
def cert_18_22 : Tree := (split 13 (5,false) 6 #[
(.side 11 7 false (-1)),
(.side 7 12 false (1)),
(.side 7 8 false (1)),
(.side 5 9 false (2)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 9 5 false (0)),
(.side 7 7 false (1)),
(.side 0 15 false (2)),
(.side 12 3 false (-2)),
(.side 11 8 false (-1)),
(.side 10 4 false (0)),
(.side 7 9 false (1)),
(.side 8 6 false (0)),
(.side 7 9 false (1)),
(.side 7 11 false (1)),
(.side 12 2 false (-2)),
(.side 11 3 false (-1)),
(.side 12 2 false (-2)),
(.side 11 4 false (-1)),
(.side 13 1 false (-3)),
(.last 14 (5,true)),
(.side 13 1 false (-3)),
(.last 14 (5,true))])
theorem checked_18_22 : check 143 p_18_22 cert_18_22 = true := by decide +kernel
theorem safe_18_22 : ∀ m, compatible p_18_22 m → WeightedBound 143 m := sound 143 _ cert_18_22 (by decide) checked_18_22
def p_18_23 := refine p_18 (4,false) (some ⟨true,true,5⟩)
def cert_18_23 : Tree := (split 13 (5,true) 6 #[
(.side 7 14 false (1)),
(.side 4 22 false (2)),
(.side 7 12 false (1)),
(.side 6 39 false (2)),
(.side 7 10 false (1)),
(.side 7 20 false (1)),
(.side 7 10 false (1)),
(.side 7 18 false (1)),
(.last 16 (5,false)),
(.side 7 20 false (1)),
(.last 16 (5,false)),
(.side 2 12 false (2)),
(.side 8 6 false (0)),
(.side 7 14 false (1)),
(.side 8 6 false (0)),
(.side 4 10 false (2)),
(.side 11 3 false (-1)),
(.last 15 (5,false)),
(.side 11 3 false (-1)),
(.last 15 (5,false)),
(.last 15 (5,false)),
(.last 14 (5,false)),
(.last 15 (5,false)),
(.last 14 (5,false))])
theorem checked_18_23 : check 143 p_18_23 cert_18_23 = true := by decide +kernel
theorem safe_18_23 : ∀ m, compatible p_18_23 m → WeightedBound 143 m := sound 143 _ cert_18_23 (by decide) checked_18_23
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 143 m := by
  apply split_safe 143 p_18 12 (4,false) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_18_0 | exact safe_18_1 | exact safe_18_2 | exact safe_18_3 | exact safe_18_4 | exact safe_18_5 | exact safe_18_6 | exact safe_18_7 | exact safe_18_8 | exact safe_18_9 | exact safe_18_10 | exact safe_18_11 | exact safe_18_12 | exact safe_18_13 | exact safe_18_14 | exact safe_18_15 | exact safe_18_16 | exact safe_18_17 | exact safe_18_18 | exact safe_18_19 | exact safe_18_20 | exact safe_18_21 | exact safe_18_22 | exact safe_18_23 | omega
def p_19 := refine parent (4,true) (some ⟨true,true,4⟩)
def p_19_0 := refine p_19 (4,false) (some ⟨false,false,0⟩)
def cert_19_0 : Tree := (.side 7 13 false (1))
theorem checked_19_0 : check 143 p_19_0 cert_19_0 = true := by decide +kernel
theorem safe_19_0 : ∀ m, compatible p_19_0 m → WeightedBound 143 m := sound 143 _ cert_19_0 (by decide) checked_19_0
def p_19_1 := refine p_19 (4,false) (some ⟨false,true,0⟩)
def cert_19_1 : Tree := (.side 0 20 true (-1))
theorem checked_19_1 : check 143 p_19_1 cert_19_1 = true := by decide +kernel
theorem safe_19_1 : ∀ m, compatible p_19_1 m → WeightedBound 143 m := sound 143 _ cert_19_1 (by decide) checked_19_1
def p_19_2 := refine p_19 (4,false) (some ⟨true,false,0⟩)
def cert_19_2 : Tree := (.side 7 11 false (1))
theorem checked_19_2 : check 143 p_19_2 cert_19_2 = true := by decide +kernel
theorem safe_19_2 : ∀ m, compatible p_19_2 m → WeightedBound 143 m := sound 143 _ cert_19_2 (by decide) checked_19_2
def p_19_3 := refine p_19 (4,false) (some ⟨true,true,0⟩)
def cert_19_3 : Tree := (.side 6 9 false (2))
theorem checked_19_3 : check 143 p_19_3 cert_19_3 = true := by decide +kernel
theorem safe_19_3 : ∀ m, compatible p_19_3 m → WeightedBound 143 m := sound 143 _ cert_19_3 (by decide) checked_19_3
def p_19_4 := refine p_19 (4,false) (some ⟨false,false,1⟩)
def cert_19_4 : Tree := (.side 7 9 false (1))
theorem checked_19_4 : check 143 p_19_4 cert_19_4 = true := by decide +kernel
theorem safe_19_4 : ∀ m, compatible p_19_4 m → WeightedBound 143 m := sound 143 _ cert_19_4 (by decide) checked_19_4
def p_19_5 := refine p_19 (4,false) (some ⟨false,true,1⟩)
def cert_19_5 : Tree := (.side 24 19 false (2))
theorem checked_19_5 : check 143 p_19_5 cert_19_5 = true := by decide +kernel
theorem safe_19_5 : ∀ m, compatible p_19_5 m → WeightedBound 143 m := sound 143 _ cert_19_5 (by decide) checked_19_5
def p_19_6 := refine p_19 (4,false) (some ⟨true,false,1⟩)
def cert_19_6 : Tree := (.side 7 9 false (1))
theorem checked_19_6 : check 143 p_19_6 cert_19_6 = true := by decide +kernel
theorem safe_19_6 : ∀ m, compatible p_19_6 m → WeightedBound 143 m := sound 143 _ cert_19_6 (by decide) checked_19_6
def p_19_7 := refine p_19 (4,false) (some ⟨true,true,1⟩)
def cert_19_7 : Tree := (.side 24 17 false (2))
theorem checked_19_7 : check 143 p_19_7 cert_19_7 = true := by decide +kernel
theorem safe_19_7 : ∀ m, compatible p_19_7 m → WeightedBound 143 m := sound 143 _ cert_19_7 (by decide) checked_19_7
def p_19_8 := refine p_19 (4,false) (some ⟨false,false,2⟩)
def cert_19_8 : Tree := (.side 0 16 false (2))
theorem checked_19_8 : check 143 p_19_8 cert_19_8 = true := by decide +kernel
theorem safe_19_8 : ∀ m, compatible p_19_8 m → WeightedBound 143 m := sound 143 _ cert_19_8 (by decide) checked_19_8
def p_19_9 := refine p_19 (4,false) (some ⟨false,true,2⟩)
def cert_19_9 : Tree := (.side 28 19 false (2))
theorem checked_19_9 : check 143 p_19_9 cert_19_9 = true := by decide +kernel
theorem safe_19_9 : ∀ m, compatible p_19_9 m → WeightedBound 143 m := sound 143 _ cert_19_9 (by decide) checked_19_9
def p_19_10 := refine p_19 (4,false) (some ⟨true,false,2⟩)
def cert_19_10 : Tree := (.side 10 11 false (0))
theorem checked_19_10 : check 143 p_19_10 cert_19_10 = true := by decide +kernel
theorem safe_19_10 : ∀ m, compatible p_19_10 m → WeightedBound 143 m := sound 143 _ cert_19_10 (by decide) checked_19_10
def p_19_11 := refine p_19 (4,false) (some ⟨true,true,2⟩)
def cert_19_11 : Tree := (.side 2 11 false (2))
theorem checked_19_11 : check 143 p_19_11 cert_19_11 = true := by decide +kernel
theorem safe_19_11 : ∀ m, compatible p_19_11 m → WeightedBound 143 m := sound 143 _ cert_19_11 (by decide) checked_19_11
def p_19_12 := refine p_19 (4,false) (some ⟨false,false,3⟩)
def cert_19_12 : Tree := (.side 8 5 false (0))
theorem checked_19_12 : check 143 p_19_12 cert_19_12 = true := by decide +kernel
theorem safe_19_12 : ∀ m, compatible p_19_12 m → WeightedBound 143 m := sound 143 _ cert_19_12 (by decide) checked_19_12
def p_19_13 := refine p_19 (4,false) (some ⟨false,true,3⟩)
def cert_19_13 : Tree := (.side 7 13 false (1))
theorem checked_19_13 : check 143 p_19_13 cert_19_13 = true := by decide +kernel
theorem safe_19_13 : ∀ m, compatible p_19_13 m → WeightedBound 143 m := sound 143 _ cert_19_13 (by decide) checked_19_13
def p_19_14 := refine p_19 (4,false) (some ⟨true,false,3⟩)
def cert_19_14 : Tree := (.side 8 5 false (0))
theorem checked_19_14 : check 143 p_19_14 cert_19_14 = true := by decide +kernel
theorem safe_19_14 : ∀ m, compatible p_19_14 m → WeightedBound 143 m := sound 143 _ cert_19_14 (by decide) checked_19_14
def p_19_15 := refine p_19 (4,false) (some ⟨true,true,3⟩)
def cert_19_15 : Tree := (.side 4 9 false (2))
theorem checked_19_15 : check 143 p_19_15 cert_19_15 = true := by decide +kernel
theorem safe_19_15 : ∀ m, compatible p_19_15 m → WeightedBound 143 m := sound 143 _ cert_19_15 (by decide) checked_19_15
def p_19_16 := refine p_19 (4,false) (some ⟨false,false,4⟩)
def cert_19_16 : Tree := (.side 11 2 true (-1))
theorem checked_19_16 : check 143 p_19_16 cert_19_16 = true := by decide +kernel
theorem safe_19_16 : ∀ m, compatible p_19_16 m → WeightedBound 143 m := sound 143 _ cert_19_16 (by decide) checked_19_16
def p_19_17 := refine p_19 (4,false) (some ⟨false,true,4⟩)
def cert_19_17 : Tree := (.side 15 1 true (3))
theorem checked_19_17 : check 143 p_19_17 cert_19_17 = true := by decide +kernel
theorem safe_19_17 : ∀ m, compatible p_19_17 m → WeightedBound 143 m := sound 143 _ cert_19_17 (by decide) checked_19_17
def p_19_18 := refine p_19 (4,false) (some ⟨true,false,4⟩)
def cert_19_18 : Tree := (.side 17 3 true (1))
theorem checked_19_18 : check 143 p_19_18 cert_19_18 = true := by decide +kernel
theorem safe_19_18 : ∀ m, compatible p_19_18 m → WeightedBound 143 m := sound 143 _ cert_19_18 (by decide) checked_19_18
def p_19_19 := refine p_19 (4,false) (some ⟨true,true,4⟩)
def cert_19_19 : Tree := (.side 15 1 true (3))
theorem checked_19_19 : check 143 p_19_19 cert_19_19 = true := by decide +kernel
theorem safe_19_19 : ∀ m, compatible p_19_19 m → WeightedBound 143 m := sound 143 _ cert_19_19 (by decide) checked_19_19
def p_19_20 := refine p_19 (4,false) (some ⟨false,false,5⟩)
def cert_19_20 : Tree := (split 13 (5,true) 6 #[
(.side 0 14 false (2)),
(.side 0 20 true (-1)),
(.side 7 8 false (1)),
(.side 28 19 false (2)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (0)),
(.side 1 13 false (2)),
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.last 23 (5,false)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.last 15 (5,false)),
(.last 15 (5,false)),
(.last 15 (5,false)),
(.side 12 2 true (-1)),
(.last 14 (5,false)),
(.last 14 (5,false)),
(.last 14 (5,false)),
(.last 14 (5,false))])
theorem checked_19_20 : check 143 p_19_20 cert_19_20 = true := by decide +kernel
theorem safe_19_20 : ∀ m, compatible p_19_20 m → WeightedBound 143 m := sound 143 _ cert_19_20 (by decide) checked_19_20
def p_19_21 := refine p_19 (4,false) (some ⟨false,true,5⟩)
def cert_19_21 : Tree := (split 13 (5,false) 6 #[
(.side 28 19 false (2)),
(.last 137 (5,true)),
(.side 7 13 false (1)),
(.side 3 11 true (-1)),
(.side 1 13 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[(true,4)],[(false,5)],[(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[(false,4),(false,12)],[(true,4),(true,12)],[(false,9)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch .leaf (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .leaf) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) (.branch .empty (.branch .leaf (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .leaf) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .leaf) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)),.empty]⟩),
(.last 18 (5,true)),
(.side 1 20 true (-1)),
(.side 7 15 false (1)),
(.side 0 18 true (-1)),
(.side 7 15 false (1)),
(.side 24 19 false (2)),
(.side 7 13 false (1)),
(.side 14 9 true (1)),
(.side 7 13 false (1)),
(.side 14 17 false (2)),
(.side 12 2 true (0)),
(.side 15 2 true (3)),
(.last 15 (5,true)),
(.side 15 2 true (3)),
(.last 15 (5,true)),
(.last 14 (5,true)),
(.last 15 (5,true)),
(.last 14 (5,true))])
theorem checked_19_21 : check 143 p_19_21 cert_19_21 = true := by decide +kernel
theorem safe_19_21 : ∀ m, compatible p_19_21 m → WeightedBound 143 m := sound 143 _ cert_19_21 (by decide) checked_19_21
def p_19_22 := refine p_19 (4,false) (some ⟨true,false,5⟩)
def cert_19_22 : Tree := (split 13 (5,true) 6 #[
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 7 8 false (1)),
(.side 3 11 false (2)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 9 5 false (0)),
(.side 7 7 false (1)),
(.side 0 15 false (2)),
(.last 16 (5,false)),
(.last 23 (5,false)),
(.side 10 4 true (-1)),
(.side 7 9 false (1)),
(.side 8 6 true (-1)),
(.side 7 9 false (1)),
(.side 7 11 false (1)),
(.last 15 (5,false)),
(.side 18 3 true (2)),
(.last 15 (5,false)),
(.side 18 3 true (2)),
(.last 14 (5,false)),
(.last 15 (5,false)),
(.last 14 (5,false)),
(.last 15 (5,false))])
theorem checked_19_22 : check 143 p_19_22 cert_19_22 = true := by decide +kernel
theorem safe_19_22 : ∀ m, compatible p_19_22 m → WeightedBound 143 m := sound 143 _ cert_19_22 (by decide) checked_19_22
def p_19_23 := refine p_19 (4,false) (some ⟨true,true,5⟩)
def cert_19_23 : Tree := (split 13 (5,false) 6 #[
(.side 3 11 false (2)),
(.side 4 15 false (3)),
(.side 5 9 false (2)),
(.side 6 13 false (3)),
(.side 7 7 false (1)),
(.side 4 11 false (2)),
(.side 7 7 false (1)),
(.side 6 9 false (2)),
(.side 10 4 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[(false,12)],[(true,12)],[(false,5),(false,13)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf)))) .empty)),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .leaf) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf)))) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty)),.empty]⟩),
(.last 17 (5,true)),
(.side 24 17 false (2)),
(.side 7 11 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6),(false,4)],[(true,2),(true,6),(true,4)],[(false,5)],[(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)),.empty]⟩),
(.side 7 11 false (1)),
(.side 14 15 false (2)),
(.last 16 (5,true)),
(.side 15 2 true (3)),
(.side 15 4 true (1)),
(.side 15 2 true (3)),
(.last 14 (5,true)),
(.last 14 (5,true)),
(.last 14 (5,true)),
(.last 14 (5,true))])
theorem checked_19_23 : check 143 p_19_23 cert_19_23 = true := by decide +kernel
theorem safe_19_23 : ∀ m, compatible p_19_23 m → WeightedBound 143 m := sound 143 _ cert_19_23 (by decide) checked_19_23
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 143 m := by
  apply split_safe 143 p_19 12 (4,false) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_19_0 | exact safe_19_1 | exact safe_19_2 | exact safe_19_3 | exact safe_19_4 | exact safe_19_5 | exact safe_19_6 | exact safe_19_7 | exact safe_19_8 | exact safe_19_9 | exact safe_19_10 | exact safe_19_11 | exact safe_19_12 | exact safe_19_13 | exact safe_19_14 | exact safe_19_15 | exact safe_19_16 | exact safe_19_17 | exact safe_19_18 | exact safe_19_19 | exact safe_19_20 | exact safe_19_21 | exact safe_19_22 | exact safe_19_23 | omega
def p_20 := refine parent (4,true) (some ⟨false,false,5⟩)
def p_20_0 := refine p_20 (5,false) (some ⟨false,false,0⟩)
def cert_20_0 : Tree := (.side 0 13 false (2))
theorem checked_20_0 : check 143 p_20_0 cert_20_0 = true := by decide +kernel
theorem safe_20_0 : ∀ m, compatible p_20_0 m → WeightedBound 143 m := sound 143 _ cert_20_0 (by decide) checked_20_0
def p_20_1 := refine p_20 (5,false) (some ⟨false,true,0⟩)
def cert_20_1 : Tree := (.side 0 13 false (2))
theorem checked_20_1 : check 143 p_20_1 cert_20_1 = true := by decide +kernel
theorem safe_20_1 : ∀ m, compatible p_20_1 m → WeightedBound 143 m := sound 143 _ cert_20_1 (by decide) checked_20_1
def p_20_2 := refine p_20 (5,false) (some ⟨true,false,0⟩)
def cert_20_2 : Tree := (.side 7 7 false (1))
theorem checked_20_2 : check 143 p_20_2 cert_20_2 = true := by decide +kernel
theorem safe_20_2 : ∀ m, compatible p_20_2 m → WeightedBound 143 m := sound 143 _ cert_20_2 (by decide) checked_20_2
def p_20_3 := refine p_20 (5,false) (some ⟨true,true,0⟩)
def cert_20_3 : Tree := (.side 7 18 false (1))
theorem checked_20_3 : check 143 p_20_3 cert_20_3 = true := by decide +kernel
theorem safe_20_3 : ∀ m, compatible p_20_3 m → WeightedBound 143 m := sound 143 _ cert_20_3 (by decide) checked_20_3
def p_20_4 := refine p_20 (5,false) (some ⟨false,false,1⟩)
def cert_20_4 : Tree := (.side 7 15 false (1))
theorem checked_20_4 : check 143 p_20_4 cert_20_4 = true := by decide +kernel
theorem safe_20_4 : ∀ m, compatible p_20_4 m → WeightedBound 143 m := sound 143 _ cert_20_4 (by decide) checked_20_4
def p_20_5 := refine p_20 (5,false) (some ⟨false,true,1⟩)
def cert_20_5 : Tree := (.side 7 15 false (1))
theorem checked_20_5 : check 143 p_20_5 cert_20_5 = true := by decide +kernel
theorem safe_20_5 : ∀ m, compatible p_20_5 m → WeightedBound 143 m := sound 143 _ cert_20_5 (by decide) checked_20_5
def p_20_6 := refine p_20 (5,false) (some ⟨true,false,1⟩)
def cert_20_6 : Tree := (.side 9 4 false (0))
theorem checked_20_6 : check 143 p_20_6 cert_20_6 = true := by decide +kernel
theorem safe_20_6 : ∀ m, compatible p_20_6 m → WeightedBound 143 m := sound 143 _ cert_20_6 (by decide) checked_20_6
def p_20_7 := refine p_20 (5,false) (some ⟨true,true,1⟩)
def cert_20_7 : Tree := (.side 1 12 false (2))
theorem checked_20_7 : check 143 p_20_7 cert_20_7 = true := by decide +kernel
theorem safe_20_7 : ∀ m, compatible p_20_7 m → WeightedBound 143 m := sound 143 _ cert_20_7 (by decide) checked_20_7
def p_20_8 := refine p_20 (5,false) (some ⟨false,false,2⟩)
def cert_20_8 : Tree := (.side 0 14 false (2))
theorem checked_20_8 : check 143 p_20_8 cert_20_8 = true := by decide +kernel
theorem safe_20_8 : ∀ m, compatible p_20_8 m → WeightedBound 143 m := sound 143 _ cert_20_8 (by decide) checked_20_8
def p_20_9 := refine p_20 (5,false) (some ⟨false,true,2⟩)
def cert_20_9 : Tree := (.side 0 14 false (2))
theorem checked_20_9 : check 143 p_20_9 cert_20_9 = true := by decide +kernel
theorem safe_20_9 : ∀ m, compatible p_20_9 m → WeightedBound 143 m := sound 143 _ cert_20_9 (by decide) checked_20_9
def p_20_10 := refine p_20 (5,false) (some ⟨true,false,2⟩)
def cert_20_10 : Tree := (split 18 (5,true) 6 #[
(.side 0 19 false (2)),
(.side 0 19 false (2)),
(.side 7 13 false (1)),
(.side 7 24 false (1)),
(.side 7 21 false (1)),
(.side 7 21 false (1)),
(.side 9 10 false (0)),
(.side 1 18 false (2)),
(.side 0 20 false (2)),
(.side 0 20 false (2)),
(.side 13 6 false (-2)),
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 7 14 false (1)),
(.side 7 14 false (1)),
(.side 7 18 false (1)),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.side 12 7 false (-2)),
(.side 12 7 false (-2)),
(.side 12 7 false (-2)),
(.last 21 (4,false))])
theorem checked_20_10 : check 143 p_20_10 cert_20_10 = true := by decide +kernel
theorem safe_20_10 : ∀ m, compatible p_20_10 m → WeightedBound 143 m := sound 143 _ cert_20_10 (by decide) checked_20_10
def p_20_11 := refine p_20 (5,false) (some ⟨true,true,2⟩)
def cert_20_11 : Tree := (.side 7 14 false (1))
theorem checked_20_11 : check 143 p_20_11 cert_20_11 = true := by decide +kernel
theorem safe_20_11 : ∀ m, compatible p_20_11 m → WeightedBound 143 m := sound 143 _ cert_20_11 (by decide) checked_20_11
def p_20_12 := refine p_20 (5,false) (some ⟨false,false,3⟩)
def cert_20_12 : Tree := (.side 7 8 false (1))
theorem checked_20_12 : check 143 p_20_12 cert_20_12 = true := by decide +kernel
theorem safe_20_12 : ∀ m, compatible p_20_12 m → WeightedBound 143 m := sound 143 _ cert_20_12 (by decide) checked_20_12
def p_20_13 := refine p_20 (5,false) (some ⟨false,true,3⟩)
def cert_20_13 : Tree := (.side 7 8 false (1))
theorem checked_20_13 : check 143 p_20_13 cert_20_13 = true := by decide +kernel
theorem safe_20_13 : ∀ m, compatible p_20_13 m → WeightedBound 143 m := sound 143 _ cert_20_13 (by decide) checked_20_13
def p_20_14 := refine p_20 (5,false) (some ⟨true,false,3⟩)
def cert_20_14 : Tree := (.side 7 8 false (1))
theorem checked_20_14 : check 143 p_20_14 cert_20_14 = true := by decide +kernel
theorem safe_20_14 : ∀ m, compatible p_20_14 m → WeightedBound 143 m := sound 143 _ cert_20_14 (by decide) checked_20_14
def p_20_15 := refine p_20 (5,false) (some ⟨true,true,3⟩)
def cert_20_15 : Tree := (.side 7 12 false (1))
theorem checked_20_15 : check 143 p_20_15 cert_20_15 = true := by decide +kernel
theorem safe_20_15 : ∀ m, compatible p_20_15 m → WeightedBound 143 m := sound 143 _ cert_20_15 (by decide) checked_20_15
def p_20_16 := refine p_20 (5,false) (some ⟨false,false,4⟩)
def cert_20_16 : Tree := (split 13 (4,false) 6 #[
(.side 0 14 false (2)),
(.side 0 14 false (2)),
(.side 7 8 false (1)),
(.side 7 19 false (1)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (0)),
(.side 1 13 false (2)),
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.last 19 (5,true)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.side 13 1 false (-3)),
(.side 20 1 true (0)),
(.side 13 1 false (-3)),
(.last 19 (5,true)),
(.side 12 2 false (-2)),
(.side 12 2 true (-3)),
(.side 12 2 false (-2)),
(.side 11 4 false (-1))])
theorem checked_20_16 : check 143 p_20_16 cert_20_16 = true := by decide +kernel
theorem safe_20_16 : ∀ m, compatible p_20_16 m → WeightedBound 143 m := sound 143 _ cert_20_16 (by decide) checked_20_16
def p_20_17 := refine p_20 (5,false) (some ⟨false,true,4⟩)
def cert_20_17 : Tree := (split 13 (4,false) 6 #[
(.side 0 14 false (2)),
(.last 18 (5,true)),
(.side 7 8 false (1)),
(.last 18 (5,true)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (0)),
(.side 1 13 false (2)),
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.last 19 (5,true)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.side 13 1 false (-1)),
(.side 18 1 true (2)),
(.side 13 1 false (-1)),
(.last 17 (5,true)),
(.side 12 2 true (-2)),
(.last 16 (5,true)),
(.side 11 4 true (-2)),
(.last 16 (5,true))])
theorem checked_20_17 : check 143 p_20_17 cert_20_17 = true := by decide +kernel
theorem safe_20_17 : ∀ m, compatible p_20_17 m → WeightedBound 143 m := sound 143 _ cert_20_17 (by decide) checked_20_17
def p_20_18 := refine p_20 (5,false) (some ⟨true,false,4⟩)
def cert_20_18 : Tree := (split 13 (4,false) 6 #[
(.last 18 (5,true)),
(.side 7 14 false (1)),
(.side 7 8 false (1)),
(.side 3 11 false (2)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 9 5 false (0)),
(.side 7 7 false (1)),
(.side 0 15 false (2)),
(.side 0 17 false (2)),
(.last 19 (5,true)),
(.side 10 4 false (0)),
(.side 7 9 false (1)),
(.side 8 6 false (0)),
(.side 7 9 false (1)),
(.side 7 11 false (1)),
(.side 13 1 false (-3)),
(.side 11 3 false (-1)),
(.side 13 1 false (-3)),
(.last 15 (5,true)),
(.side 12 2 false (-2)),
(.last 14 (5,true)),
(.side 12 2 false (-2)),
(.last 14 (5,true))])
theorem checked_20_18 : check 143 p_20_18 cert_20_18 = true := by decide +kernel
theorem safe_20_18 : ∀ m, compatible p_20_18 m → WeightedBound 143 m := sound 143 _ cert_20_18 (by decide) checked_20_18
def p_20_19 := refine p_20 (5,false) (some ⟨true,true,4⟩)
def cert_20_19 : Tree := (split 13 (4,false) 6 #[
(.side 7 14 false (1)),
(.last 18 (5,true)),
(.side 7 12 false (1)),
(.last 18 (5,true)),
(.side 7 10 false (1)),
(.side 7 20 false (1)),
(.side 7 10 false (1)),
(.side 7 18 false (1)),
(.side 0 17 false (2)),
(.side 7 20 false (1)),
(.last 21 (5,true)),
(.side 2 12 false (2)),
(.side 8 6 false (0)),
(.side 7 14 false (1)),
(.side 8 6 false (0)),
(.side 4 10 false (2)),
(.side 11 3 false (-1)),
(.side 18 1 true (2)),
(.side 11 3 false (-1)),
(.last 17 (5,true)),
(.last 14 (5,true)),
(.last 16 (5,true)),
(.last 14 (5,true)),
(.last 16 (5,true))])
theorem checked_20_19 : check 143 p_20_19 cert_20_19 = true := by decide +kernel
theorem safe_20_19 : ∀ m, compatible p_20_19 m → WeightedBound 143 m := sound 143 _ cert_20_19 (by decide) checked_20_19
def p_20_20 := refine p_20 (5,false) (some ⟨false,false,5⟩)
def cert_20_20 : Tree := (.side 12 1 false (-2))
theorem checked_20_20 : check 143 p_20_20 cert_20_20 = true := by decide +kernel
theorem safe_20_20 : ∀ m, compatible p_20_20 m → WeightedBound 143 m := sound 143 _ cert_20_20 (by decide) checked_20_20
def p_20_21 := refine p_20 (5,false) (some ⟨false,true,5⟩)
def cert_20_21 : Tree := (split 16 (5,true) 6 #[
(.side 0 17 true (-2)),
(.side 0 17 true (-2)),
(.side 23 1 true (-1)),
(.side 12 40 true (-2)),
(.side 12 20 true (-3)),
(.side 12 20 true (-2)),
(.side 20 1 true (0)),
(.side 1 16 true (-2)),
(.side 0 18 true (-2)),
(.side 0 18 true (-2)),
(.side 16 6 false (2)),
(.side 12 19 true (-2)),
(.side 24 1 true (-2)),
(.side 24 1 true (0)),
(.side 7 12 true (-2)),
(.side 12 17 true (-2)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.side 17 1 true (1)),
(.side 17 1 true (3)),
(.side 15 2 true (1)),
(.side 17 1 true (3))])
theorem checked_20_21 : check 143 p_20_21 cert_20_21 = true := by decide +kernel
theorem safe_20_21 : ∀ m, compatible p_20_21 m → WeightedBound 143 m := sound 143 _ cert_20_21 (by decide) checked_20_21
def p_20_22 := refine p_20 (5,false) (some ⟨true,false,5⟩)
def cert_20_22 : Tree := (.side 12 1 false (-2))
theorem checked_20_22 : check 143 p_20_22 cert_20_22 = true := by decide +kernel
theorem safe_20_22 : ∀ m, compatible p_20_22 m → WeightedBound 143 m := sound 143 _ cert_20_22 (by decide) checked_20_22
def p_20_23 := refine p_20 (5,false) (some ⟨true,true,5⟩)
def cert_20_23 : Tree := (split 16 (5,true) 6 #[
(.side 6 16 false (2)),
(.side 24 81 false (4)),
(.side 6 14 false (2)),
(.side 24 38 false (4)),
(.side 6 12 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,2),(true,1)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 6 12 false (2)),
(.side 16 24 false (4)),
(.last 21 (4,false)),
(.side 16 28 false (4)),
(.last 21 (4,false)),
(.side 6 42 false (3)),
(.side 6 30 false (2)),
(.side 6 16 false (3)),
(.side 6 30 false (2)),
(.side 6 38 false (3)),
(.last 21 (4,false)),
(.last 17 (4,false)),
(.last 21 (4,false)),
(.last 17 (4,false)),
(.side 21 1 true (-3)),
(.side 17 1 true (3)),
(.side 19 3 false (-1)),
(.side 17 1 true (3))])
theorem checked_20_23 : check 143 p_20_23 cert_20_23 = true := by decide +kernel
theorem safe_20_23 : ∀ m, compatible p_20_23 m → WeightedBound 143 m := sound 143 _ cert_20_23 (by decide) checked_20_23
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 143 m := by
  apply split_safe 143 p_20 12 (5,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_20_0 | exact safe_20_1 | exact safe_20_2 | exact safe_20_3 | exact safe_20_4 | exact safe_20_5 | exact safe_20_6 | exact safe_20_7 | exact safe_20_8 | exact safe_20_9 | exact safe_20_10 | exact safe_20_11 | exact safe_20_12 | exact safe_20_13 | exact safe_20_14 | exact safe_20_15 | exact safe_20_16 | exact safe_20_17 | exact safe_20_18 | exact safe_20_19 | exact safe_20_20 | exact safe_20_21 | exact safe_20_22 | exact safe_20_23 | omega
def p_21 := refine parent (4,true) (some ⟨false,true,5⟩)
def p_21_0 := refine p_21 (5,false) (some ⟨false,false,0⟩)
def cert_21_0 : Tree := (.side 0 13 false (2))
theorem checked_21_0 : check 143 p_21_0 cert_21_0 = true := by decide +kernel
theorem safe_21_0 : ∀ m, compatible p_21_0 m → WeightedBound 143 m := sound 143 _ cert_21_0 (by decide) checked_21_0
def p_21_1 := refine p_21 (5,false) (some ⟨false,true,0⟩)
def cert_21_1 : Tree := (.side 0 20 true (-1))
theorem checked_21_1 : check 143 p_21_1 cert_21_1 = true := by decide +kernel
theorem safe_21_1 : ∀ m, compatible p_21_1 m → WeightedBound 143 m := sound 143 _ cert_21_1 (by decide) checked_21_1
def p_21_2 := refine p_21 (5,false) (some ⟨true,false,0⟩)
def cert_21_2 : Tree := (.side 7 7 false (1))
theorem checked_21_2 : check 143 p_21_2 cert_21_2 = true := by decide +kernel
theorem safe_21_2 : ∀ m, compatible p_21_2 m → WeightedBound 143 m := sound 143 _ cert_21_2 (by decide) checked_21_2
def p_21_3 := refine p_21 (5,false) (some ⟨true,true,0⟩)
def cert_21_3 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,2),(true,1)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),.empty]⟩)
theorem checked_21_3 : check 143 p_21_3 cert_21_3 = true := by decide +kernel
theorem safe_21_3 : ∀ m, compatible p_21_3 m → WeightedBound 143 m := sound 143 _ cert_21_3 (by decide) checked_21_3
def p_21_4 := refine p_21 (5,false) (some ⟨false,false,1⟩)
def cert_21_4 : Tree := (.side 7 15 false (1))
theorem checked_21_4 : check 143 p_21_4 cert_21_4 = true := by decide +kernel
theorem safe_21_4 : ∀ m, compatible p_21_4 m → WeightedBound 143 m := sound 143 _ cert_21_4 (by decide) checked_21_4
def p_21_5 := refine p_21 (5,false) (some ⟨false,true,1⟩)
def cert_21_5 : Tree := (.side 13 15 false (4))
theorem checked_21_5 : check 143 p_21_5 cert_21_5 = true := by decide +kernel
theorem safe_21_5 : ∀ m, compatible p_21_5 m → WeightedBound 143 m := sound 143 _ cert_21_5 (by decide) checked_21_5
def p_21_6 := refine p_21 (5,false) (some ⟨true,false,1⟩)
def cert_21_6 : Tree := (.side 9 4 true (-1))
theorem checked_21_6 : check 143 p_21_6 cert_21_6 = true := by decide +kernel
theorem safe_21_6 : ∀ m, compatible p_21_6 m → WeightedBound 143 m := sound 143 _ cert_21_6 (by decide) checked_21_6
def p_21_7 := refine p_21 (5,false) (some ⟨true,true,1⟩)
def cert_21_7 : Tree := (.side 1 16 true (-1))
theorem checked_21_7 : check 143 p_21_7 cert_21_7 = true := by decide +kernel
theorem safe_21_7 : ∀ m, compatible p_21_7 m → WeightedBound 143 m := sound 143 _ cert_21_7 (by decide) checked_21_7
def p_21_8 := refine p_21 (5,false) (some ⟨false,false,2⟩)
def cert_21_8 : Tree := (.side 0 14 false (2))
theorem checked_21_8 : check 143 p_21_8 cert_21_8 = true := by decide +kernel
theorem safe_21_8 : ∀ m, compatible p_21_8 m → WeightedBound 143 m := sound 143 _ cert_21_8 (by decide) checked_21_8
def p_21_9 := refine p_21 (5,false) (some ⟨false,true,2⟩)
def cert_21_9 : Tree := (.side 0 20 true (-1))
theorem checked_21_9 : check 143 p_21_9 cert_21_9 = true := by decide +kernel
theorem safe_21_9 : ∀ m, compatible p_21_9 m → WeightedBound 143 m := sound 143 _ cert_21_9 (by decide) checked_21_9
def p_21_10 := refine p_21 (5,false) (some ⟨true,false,2⟩)
def cert_21_10 : Tree := (.side 7 20 false (1))
theorem checked_21_10 : check 143 p_21_10 cert_21_10 = true := by decide +kernel
theorem safe_21_10 : ∀ m, compatible p_21_10 m → WeightedBound 143 m := sound 143 _ cert_21_10 (by decide) checked_21_10
def p_21_11 := refine p_21 (5,false) (some ⟨true,true,2⟩)
def cert_21_11 : Tree := (.side 7 14 false (1))
theorem checked_21_11 : check 143 p_21_11 cert_21_11 = true := by decide +kernel
theorem safe_21_11 : ∀ m, compatible p_21_11 m → WeightedBound 143 m := sound 143 _ cert_21_11 (by decide) checked_21_11
def p_21_12 := refine p_21 (5,false) (some ⟨false,false,3⟩)
def cert_21_12 : Tree := (.side 7 8 false (1))
theorem checked_21_12 : check 143 p_21_12 cert_21_12 = true := by decide +kernel
theorem safe_21_12 : ∀ m, compatible p_21_12 m → WeightedBound 143 m := sound 143 _ cert_21_12 (by decide) checked_21_12
def p_21_13 := refine p_21 (5,false) (some ⟨false,true,3⟩)
def cert_21_13 : Tree := (.side 7 8 true (-1))
theorem checked_21_13 : check 143 p_21_13 cert_21_13 = true := by decide +kernel
theorem safe_21_13 : ∀ m, compatible p_21_13 m → WeightedBound 143 m := sound 143 _ cert_21_13 (by decide) checked_21_13
def p_21_14 := refine p_21 (5,false) (some ⟨true,false,3⟩)
def cert_21_14 : Tree := (.side 7 8 false (1))
theorem checked_21_14 : check 143 p_21_14 cert_21_14 = true := by decide +kernel
theorem safe_21_14 : ∀ m, compatible p_21_14 m → WeightedBound 143 m := sound 143 _ cert_21_14 (by decide) checked_21_14
def p_21_15 := refine p_21 (5,false) (some ⟨true,true,3⟩)
def cert_21_15 : Tree := (.side 7 12 false (1))
theorem checked_21_15 : check 143 p_21_15 cert_21_15 = true := by decide +kernel
theorem safe_21_15 : ∀ m, compatible p_21_15 m → WeightedBound 143 m := sound 143 _ cert_21_15 (by decide) checked_21_15
def p_21_16 := refine p_21 (5,false) (some ⟨false,false,4⟩)
def cert_21_16 : Tree := (split 13 (4,false) 6 #[
(.side 0 14 false (2)),
(.side 0 20 true (-1)),
(.side 7 8 false (1)),
(.side 28 19 false (2)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (0)),
(.side 1 13 false (2)),
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.side 13 9 false (-1)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.side 13 1 false (-1)),
(.side 18 1 true (2)),
(.side 13 1 false (-1)),
(.side 18 1 true (2)),
(.side 12 2 false (0)),
(.side 12 2 true (-1)),
(.side 12 2 false (0)),
(.side 11 4 true (-1))])
theorem checked_21_16 : check 143 p_21_16 cert_21_16 = true := by decide +kernel
theorem safe_21_16 : ∀ m, compatible p_21_16 m → WeightedBound 143 m := sound 143 _ cert_21_16 (by decide) checked_21_16
def p_21_17 := refine p_21 (5,false) (some ⟨false,true,4⟩)
def cert_21_17 : Tree := (split 13 (4,false) 6 #[
(.side 0 20 true (-1)),
(.side 0 36 true (-1)),
(.side 7 8 true (-1)),
(.side 3 11 true (-1)),
(.side 7 16 false (1)),
(.side 19 21 true (-1)),
(.side 18 5 true (2)),
(.side 1 20 true (-1)),
(.side 0 15 false (2)),
(.side 0 17 true (-1)),
(.side 20 7 true (2)),
(.side 14 15 false (4)),
(.side 7 9 false (1)),
(.side 14 9 true (1)),
(.side 7 9 false (1)),
(.side 14 13 false (2)),
(.side 13 1 false (1)),
(.side 16 1 true (4)),
(.side 13 1 false (1)),
(.side 16 1 true (4)),
(.side 12 2 true (0)),
(.last 14 (5,true)),
(.last 16 (5,true)),
(.last 14 (5,true))])
theorem checked_21_17 : check 143 p_21_17 cert_21_17 = true := by decide +kernel
theorem safe_21_17 : ∀ m, compatible p_21_17 m → WeightedBound 143 m := sound 143 _ cert_21_17 (by decide) checked_21_17
def p_21_18 := refine p_21 (5,false) (some ⟨true,false,4⟩)
def cert_21_18 : Tree := (split 13 (4,false) 6 #[
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 7 8 false (1)),
(.side 3 11 false (2)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 9 5 false (0)),
(.side 7 7 false (1)),
(.side 0 15 false (2)),
(.side 0 17 false (2)),
(.side 13 9 false (-1)),
(.side 10 4 true (-1)),
(.side 7 9 false (1)),
(.side 8 6 true (-1)),
(.side 7 9 false (1)),
(.side 7 11 false (1)),
(.side 13 1 false (-1)),
(.last 18 (5,true)),
(.side 13 1 false (-1)),
(.last 18 (5,true)),
(.side 12 2 false (0)),
(.last 14 (5,true)),
(.side 12 2 false (0)),
(.last 14 (5,true))])
theorem checked_21_18 : check 143 p_21_18 cert_21_18 = true := by decide +kernel
theorem safe_21_18 : ∀ m, compatible p_21_18 m → WeightedBound 143 m := sound 143 _ cert_21_18 (by decide) checked_21_18
def p_21_19 := refine p_21 (5,false) (some ⟨true,true,4⟩)
def cert_21_19 : Tree := (split 13 (4,false) 6 #[
(.side 7 14 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2),(true,6)],[(false,5)],[(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[(false,12),(false,4)],[(true,12),(true,4)],[(false,5),(false,13)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) (.branch .empty (.branch .leaf (.branch .leaf .leaf))))) (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) .empty) .empty)) .empty),.empty]⟩),
(.side 7 12 false (1)),
(.side 6 26 false (3)),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,8)],[(true,2)],[(false,3)],[(true,3)],[],[(true,5)],[],[],[(true,8)]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[(false,4),(false,12)],[(true,4),(true,12)],[(false,9),(false,5)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch .leaf (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) .leaf) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) .leaf))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) .leaf) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) .leaf))) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty)) .empty),.empty]⟩),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(true,2)],[(false,2)],[(true,4),(true,8)],[(true,5)],[(true,6)],[(false,6)]],#[(0,1),(0,2),(4,3),(0,0),(0,5),(0,6),(8,7),(0,0),(0,5)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[(false,3),(true,3),(false,6),(true,6),(false,7),(false,10),(true,10),(false,11),(true,11),(false,13),(true,13),(false,18),(false,21),(true,21),(false,24),(true,24),(true,26),(false,27),(true,27)],[(false,4),(false,16),(false,20),(false,23)],[(true,4)],[(false,5)],[(true,5)],[(true,7)],[(false,8),(false,22)],[(true,8),(true,19),(true,22)],[(false,9)],[(true,9)],[(false,12),(false,25)],[(true,12),(true,25)],[(false,14)],[(true,14)],[(false,15)],[(true,15),(true,17)],[(true,16)],[(false,17)],[(true,18)],[(false,19)],[(true,20),(true,23)],[(false,26)]],#[(0,1),(2,3),(4,5),(6,6),(7,8),(9,10),(6,6),(6,11),(12,13),(14,15),(6,6),(6,6),(16,17),(6,6),(18,19),(20,21),(7,22),(23,21),(6,24),(25,13),(7,26),(6,6),(12,13),(7,26),(6,6),(16,17),(27,6),(6,6)]⟩,#[(.branch .leaf (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf))) (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .leaf (.branch .empty (.branch .empty .leaf)))) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .leaf (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty .leaf)))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .leaf)) (.branch (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) (.branch .leaf (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))) (.branch (.branch .leaf (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf)))) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .leaf (.branch .empty (.branch .empty .leaf)))) .empty)))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf))) (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .leaf))) (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) (.branch .leaf (.branch .empty (.branch .leaf .leaf)))) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .empty .leaf))) (.branch .leaf (.branch .empty (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf)))) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .leaf (.branch .empty (.branch .empty .leaf)))) .empty)))),.empty]⟩),
(.side 0 17 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,2)],[(false,2)],[(true,5),(true,10)],[(false,6)],[(true,6)],[(true,8)],[(false,8)]],#[(0,1),(3,2),(5,4),(0,0),(0,0),(0,6),(7,8),(0,0),(10,9),(0,0),(0,6)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,16)],[(true,2)],[(false,3),(true,3),(false,4),(false,6),(true,6),(false,7),(true,7),(false,13),(true,13),(false,14),(true,15),(false,17),(true,17),(false,18),(false,20),(true,20),(false,21),(true,21),(true,22),(false,23),(true,23),(false,25),(true,25)],[(true,4)],[(false,5)],[(true,5),(true,19)],[(false,8),(false,24)],[(true,8),(true,24)],[(false,9)],[(true,9)],[(false,10)],[(true,10)],[(false,11)],[(true,11)],[(false,12)],[(true,12)],[(true,14)],[(false,15)],[(true,16)],[(true,18)],[(false,19)],[(false,22)]],#[(0,1),(2,3),(4,5),(6,6),(6,7),(8,9),(6,6),(6,6),(10,11),(12,13),(14,15),(16,17),(18,19),(6,6),(6,20),(21,6),(4,22),(6,6),(6,23),(24,9),(6,6),(6,6),(25,6),(6,6),(10,11),(6,6)]⟩,#[(.branch (.branch (.branch .leaf (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))) (.branch .empty (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .leaf (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf)))),(.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .leaf .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .leaf))) (.branch (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .leaf (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .leaf) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) .empty),.empty]⟩),
(.side 13 11 false (1)),
(.side 2 16 true (-1)),
(.side 8 6 true (-1)),
(.side 27 14 false (1)),
(.last 20 (5,true)),
(.side 6 8 true (-1)),
(.side 16 3 true (2)),
(.side 16 1 true (4)),
(.last 15 (5,true)),
(.side 16 1 true (4)),
(.last 14 (5,true)),
(.last 14 (5,true)),
(.last 14 (5,true)),
(.last 14 (5,true))])
theorem checked_21_19 : check 143 p_21_19 cert_21_19 = true := by decide +kernel
theorem safe_21_19 : ∀ m, compatible p_21_19 m → WeightedBound 143 m := sound 143 _ cert_21_19 (by decide) checked_21_19
def p_21_20 := refine p_21 (5,false) (some ⟨false,false,5⟩)
def cert_21_20 : Tree := (.side 12 1 false (0))
theorem checked_21_20 : check 143 p_21_20 cert_21_20 = true := by decide +kernel
theorem safe_21_20 : ∀ m, compatible p_21_20 m → WeightedBound 143 m := sound 143 _ cert_21_20 (by decide) checked_21_20
def p_21_21 := refine p_21 (5,false) (some ⟨false,true,5⟩)
def cert_21_21 : Tree := (split 14 (5,true) 6 #[
(.side 0 15 true (-1)),
(.side 0 15 true (-1)),
(.side 21 1 true (1)),
(.side 12 36 true (-1)),
(.side 12 18 true (-2)),
(.side 12 18 true (0)),
(.side 18 1 true (2)),
(.side 1 14 true (-1)),
(.side 0 16 true (-1)),
(.side 0 16 true (-1)),
(.side 20 1 true (2)),
(.side 12 17 true (-1)),
(.side 22 1 true (0)),
(.side 22 1 true (2)),
(.side 7 10 true (-1)),
(.side 12 15 true (-1)),
(.last 15 (4,false)),
(.last 15 (4,false)),
(.last 15 (4,false)),
(.last 15 (4,false)),
(.side 15 1 true (1)),
(.side 15 1 true (3)),
(.side 13 2 true (1)),
(.side 15 1 true (3))])
theorem checked_21_21 : check 143 p_21_21 cert_21_21 = true := by decide +kernel
theorem safe_21_21 : ∀ m, compatible p_21_21 m → WeightedBound 143 m := sound 143 _ cert_21_21 (by decide) checked_21_21
def p_21_22 := refine p_21 (5,false) (some ⟨true,false,5⟩)
def cert_21_22 : Tree := (.side 12 1 false (0))
theorem checked_21_22 : check 143 p_21_22 cert_21_22 = true := by decide +kernel
theorem safe_21_22 : ∀ m, compatible p_21_22 m → WeightedBound 143 m := sound 143 _ cert_21_22 (by decide) checked_21_22
def p_21_23 := refine p_21 (5,false) (some ⟨true,true,5⟩)
def cert_21_23 : Tree := (split 14 (5,true) 6 #[
(.side 3 12 true (-1)),
(.side 0 15 true (-1)),
(.side 5 10 true (-1)),
(.side 22 30 false (4)),
(.side 20 1 true (0)),
(.side 36 1 true (4)),
(.side 7 8 true (-1)),
(.side 34 1 true (4)),
(.side 17 1 true (1)),
(.side 38 1 true (4)),
(.last 20 (4,false)),
(.side 6 34 false (3)),
(.side 6 22 false (2)),
(.side 6 12 true (-1)),
(.side 6 22 false (2)),
(.side 6 30 false (3)),
(.side 16 1 true (2)),
(.last 15 (4,false)),
(.last 17 (4,false)),
(.last 15 (4,false)),
(.side 17 1 true (-1)),
(.side 15 1 true (3)),
(.side 15 3 false (1)),
(.side 15 1 true (3))])
theorem checked_21_23 : check 143 p_21_23 cert_21_23 = true := by decide +kernel
theorem safe_21_23 : ∀ m, compatible p_21_23 m → WeightedBound 143 m := sound 143 _ cert_21_23 (by decide) checked_21_23
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 143 m := by
  apply split_safe 143 p_21 12 (5,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_21_0 | exact safe_21_1 | exact safe_21_2 | exact safe_21_3 | exact safe_21_4 | exact safe_21_5 | exact safe_21_6 | exact safe_21_7 | exact safe_21_8 | exact safe_21_9 | exact safe_21_10 | exact safe_21_11 | exact safe_21_12 | exact safe_21_13 | exact safe_21_14 | exact safe_21_15 | exact safe_21_16 | exact safe_21_17 | exact safe_21_18 | exact safe_21_19 | exact safe_21_20 | exact safe_21_21 | exact safe_21_22 | exact safe_21_23 | omega
def p_22 := refine parent (4,true) (some ⟨true,false,5⟩)
def p_22_0 := refine p_22 (5,false) (some ⟨false,false,0⟩)
def cert_22_0 : Tree := (split 17 (5,true) 6 #[
(.side 13 5 false (-1)),
(.side 7 18 false (1)),
(.side 7 12 false (1)),
(.side 3 15 false (2)),
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 9 9 false (0)),
(.side 7 11 false (1)),
(.side 0 19 false (2)),
(.last 19 (4,false)),
(.side 13 6 false (-1)),
(.side 10 8 false (0)),
(.side 7 13 false (1)),
(.side 8 10 false (0)),
(.side 7 13 false (1)),
(.side 7 15 false (1)),
(.last 18 (4,false)),
(.side 11 7 false (-1)),
(.last 18 (4,false)),
(.side 16 2 true (-3)),
(.side 0 19 false (2)),
(.side 0 20 false (2)),
(.side 12 6 false (-1)),
(.side 3 17 false (2))])
theorem checked_22_0 : check 143 p_22_0 cert_22_0 = true := by decide +kernel
theorem safe_22_0 : ∀ m, compatible p_22_0 m → WeightedBound 143 m := sound 143 _ cert_22_0 (by decide) checked_22_0
def p_22_1 := refine p_22 (5,false) (some ⟨false,true,0⟩)
def cert_22_1 : Tree := (.side 7 13 false (1))
theorem checked_22_1 : check 143 p_22_1 cert_22_1 = true := by decide +kernel
theorem safe_22_1 : ∀ m, compatible p_22_1 m → WeightedBound 143 m := sound 143 _ cert_22_1 (by decide) checked_22_1
def p_22_2 := refine p_22 (5,false) (some ⟨true,false,0⟩)
def cert_22_2 : Tree := (.side 7 7 false (1))
theorem checked_22_2 : check 143 p_22_2 cert_22_2 = true := by decide +kernel
theorem safe_22_2 : ∀ m, compatible p_22_2 m → WeightedBound 143 m := sound 143 _ cert_22_2 (by decide) checked_22_2
def p_22_3 := refine p_22 (5,false) (some ⟨true,true,0⟩)
def cert_22_3 : Tree := (.side 3 10 false (2))
theorem checked_22_3 : check 143 p_22_3 cert_22_3 = true := by decide +kernel
theorem safe_22_3 : ∀ m, compatible p_22_3 m → WeightedBound 143 m := sound 143 _ cert_22_3 (by decide) checked_22_3
def p_22_4 := refine p_22 (5,false) (some ⟨false,false,1⟩)
def cert_22_4 : Tree := (.side 7 15 false (1))
theorem checked_22_4 : check 143 p_22_4 cert_22_4 = true := by decide +kernel
theorem safe_22_4 : ∀ m, compatible p_22_4 m → WeightedBound 143 m := sound 143 _ cert_22_4 (by decide) checked_22_4
def p_22_5 := refine p_22 (5,false) (some ⟨false,true,1⟩)
def cert_22_5 : Tree := (.side 7 9 false (1))
theorem checked_22_5 : check 143 p_22_5 cert_22_5 = true := by decide +kernel
theorem safe_22_5 : ∀ m, compatible p_22_5 m → WeightedBound 143 m := sound 143 _ cert_22_5 (by decide) checked_22_5
def p_22_6 := refine p_22 (5,false) (some ⟨true,false,1⟩)
def cert_22_6 : Tree := (.side 9 4 false (0))
theorem checked_22_6 : check 143 p_22_6 cert_22_6 = true := by decide +kernel
theorem safe_22_6 : ∀ m, compatible p_22_6 m → WeightedBound 143 m := sound 143 _ cert_22_6 (by decide) checked_22_6
def p_22_7 := refine p_22 (5,false) (some ⟨true,true,1⟩)
def cert_22_7 : Tree := (.side 7 6 false (1))
theorem checked_22_7 : check 143 p_22_7 cert_22_7 = true := by decide +kernel
theorem safe_22_7 : ∀ m, compatible p_22_7 m → WeightedBound 143 m := sound 143 _ cert_22_7 (by decide) checked_22_7
def p_22_8 := refine p_22 (5,false) (some ⟨false,false,2⟩)
def cert_22_8 : Tree := (.side 0 14 false (2))
theorem checked_22_8 : check 143 p_22_8 cert_22_8 = true := by decide +kernel
theorem safe_22_8 : ∀ m, compatible p_22_8 m → WeightedBound 143 m := sound 143 _ cert_22_8 (by decide) checked_22_8
def p_22_9 := refine p_22 (5,false) (some ⟨false,true,2⟩)
def cert_22_9 : Tree := (split 14 (4,false) 6 #[
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.side 7 9 false (1)),
(.side 7 20 false (1)),
(.side 7 17 false (1)),
(.side 7 17 false (1)),
(.side 9 6 false (0)),
(.side 1 14 false (2)),
(.side 0 16 false (2)),
(.side 0 16 false (2)),
(.last 20 (5,true)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 7 10 false (1)),
(.side 7 10 false (1)),
(.side 7 14 false (1)),
(.side 14 1 false (-2)),
(.side 21 1 true (1)),
(.side 14 1 false (-2)),
(.last 19 (5,true)),
(.side 0 17 false (2)),
(.side 0 17 false (2)),
(.side 12 3 false (-1)),
(.side 7 22 false (1))])
theorem checked_22_9 : check 143 p_22_9 cert_22_9 = true := by decide +kernel
theorem safe_22_9 : ∀ m, compatible p_22_9 m → WeightedBound 143 m := sound 143 _ cert_22_9 (by decide) checked_22_9
def p_22_10 := refine p_22 (5,false) (some ⟨true,false,2⟩)
def cert_22_10 : Tree := (split 18 (5,true) 6 #[
(.side 14 5 false (-2)),
(.side 7 19 false (1)),
(.side 7 13 false (1)),
(.side 3 16 false (2)),
(.side 7 21 false (1)),
(.side 7 15 false (1)),
(.side 9 10 false (0)),
(.side 7 12 false (1)),
(.side 0 20 false (2)),
(.last 20 (4,false)),
(.side 13 6 false (-2)),
(.side 10 9 false (0)),
(.side 7 14 false (1)),
(.side 8 11 false (0)),
(.side 7 14 false (1)),
(.side 7 16 false (1)),
(.last 19 (4,false)),
(.side 11 8 false (-1)),
(.last 19 (4,false)),
(.side 17 2 true (-4)),
(.side 12 7 false (-2)),
(.side 12 8 true (-4)),
(.side 12 7 false (-2)),
(.side 10 11 false (0))])
theorem checked_22_10 : check 143 p_22_10 cert_22_10 = true := by decide +kernel
theorem safe_22_10 : ∀ m, compatible p_22_10 m → WeightedBound 143 m := sound 143 _ cert_22_10 (by decide) checked_22_10
def p_22_11 := refine p_22 (5,false) (some ⟨true,true,2⟩)
def cert_22_11 : Tree := (.side 10 3 false (0))
theorem checked_22_11 : check 143 p_22_11 cert_22_11 = true := by decide +kernel
theorem safe_22_11 : ∀ m, compatible p_22_11 m → WeightedBound 143 m := sound 143 _ cert_22_11 (by decide) checked_22_11
def p_22_12 := refine p_22 (5,false) (some ⟨false,false,3⟩)
def cert_22_12 : Tree := (.side 7 8 false (1))
theorem checked_22_12 : check 143 p_22_12 cert_22_12 = true := by decide +kernel
theorem safe_22_12 : ∀ m, compatible p_22_12 m → WeightedBound 143 m := sound 143 _ cert_22_12 (by decide) checked_22_12
def p_22_13 := refine p_22 (5,false) (some ⟨false,true,3⟩)
def cert_22_13 : Tree := (.side 8 5 false (0))
theorem checked_22_13 : check 143 p_22_13 cert_22_13 = true := by decide +kernel
theorem safe_22_13 : ∀ m, compatible p_22_13 m → WeightedBound 143 m := sound 143 _ cert_22_13 (by decide) checked_22_13
def p_22_14 := refine p_22 (5,false) (some ⟨true,false,3⟩)
def cert_22_14 : Tree := (.side 7 8 false (1))
theorem checked_22_14 : check 143 p_22_14 cert_22_14 = true := by decide +kernel
theorem safe_22_14 : ∀ m, compatible p_22_14 m → WeightedBound 143 m := sound 143 _ cert_22_14 (by decide) checked_22_14
def p_22_15 := refine p_22 (5,false) (some ⟨true,true,3⟩)
def cert_22_15 : Tree := (.side 7 10 false (1))
theorem checked_22_15 : check 143 p_22_15 cert_22_15 = true := by decide +kernel
theorem safe_22_15 : ∀ m, compatible p_22_15 m → WeightedBound 143 m := sound 143 _ cert_22_15 (by decide) checked_22_15
def p_22_16 := refine p_22 (5,false) (some ⟨false,false,4⟩)
def cert_22_16 : Tree := (split 13 (4,false) 6 #[
(.side 0 14 false (2)),
(.side 7 8 false (1)),
(.side 7 8 false (1)),
(.side 7 13 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (0)),
(.side 9 5 false (0)),
(.last 17 (5,true)),
(.side 0 15 false (2)),
(.last 19 (5,true)),
(.last 19 (5,true)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.side 13 1 false (-3)),
(.side 11 4 true (-3)),
(.side 13 1 false (-3)),
(.last 16 (5,true)),
(.side 12 2 false (-2)),
(.side 12 2 true (-3)),
(.side 12 2 false (-2)),
(.side 11 4 false (-1))])
theorem checked_22_16 : check 143 p_22_16 cert_22_16 = true := by decide +kernel
theorem safe_22_16 : ∀ m, compatible p_22_16 m → WeightedBound 143 m := sound 143 _ cert_22_16 (by decide) checked_22_16
def p_22_17 := refine p_22 (5,false) (some ⟨false,true,4⟩)
def cert_22_17 : Tree := (.side 11 2 true (-2))
theorem checked_22_17 : check 143 p_22_17 cert_22_17 = true := by decide +kernel
theorem safe_22_17 : ∀ m, compatible p_22_17 m → WeightedBound 143 m := sound 143 _ cert_22_17 (by decide) checked_22_17
def p_22_18 := refine p_22 (5,false) (some ⟨true,false,4⟩)
def cert_22_18 : Tree := (split 13 (4,false) 6 #[
(.last 18 (5,true)),
(.side 7 12 false (1)),
(.side 7 8 false (1)),
(.side 5 9 false (2)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 9 5 false (0)),
(.side 7 7 false (1)),
(.side 0 15 false (2)),
(.last 21 (5,true)),
(.last 19 (5,true)),
(.side 10 4 false (0)),
(.side 7 9 false (1)),
(.side 8 6 false (0)),
(.side 7 9 false (1)),
(.side 7 11 false (1)),
(.side 13 1 false (-3)),
(.side 11 3 false (-1)),
(.side 13 1 false (-3)),
(.last 15 (5,true)),
(.side 12 2 false (-2)),
(.last 14 (5,true)),
(.side 12 2 false (-2)),
(.last 14 (5,true))])
theorem checked_22_18 : check 143 p_22_18 cert_22_18 = true := by decide +kernel
theorem safe_22_18 : ∀ m, compatible p_22_18 m → WeightedBound 143 m := sound 143 _ cert_22_18 (by decide) checked_22_18
def p_22_19 := refine p_22 (5,false) (some ⟨true,true,4⟩)
def cert_22_19 : Tree := (split 14 (5,true) 6 #[
(.side 13 5 false (-1)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 3 12 false (2)),
(.side 7 17 false (1)),
(.side 7 11 false (1)),
(.side 9 6 false (0)),
(.side 7 8 false (1)),
(.side 0 16 false (2)),
(.last 16 (4,false)),
(.side 13 6 false (-1)),
(.side 10 5 false (0)),
(.side 7 10 false (1)),
(.side 8 7 false (0)),
(.side 7 10 false (1)),
(.side 7 12 false (1)),
(.last 15 (4,false)),
(.side 11 4 true (-2)),
(.last 15 (4,false)),
(.side 13 2 true (-2)),
(.last 16 (4,false)),
(.last 17 (4,false)),
(.side 12 3 false (-1)),
(.last 17 (4,false))])
theorem checked_22_19 : check 143 p_22_19 cert_22_19 = true := by decide +kernel
theorem safe_22_19 : ∀ m, compatible p_22_19 m → WeightedBound 143 m := sound 143 _ cert_22_19 (by decide) checked_22_19
def p_22_20 := refine p_22 (5,false) (some ⟨false,false,5⟩)
def cert_22_20 : Tree := (.side 12 1 false (-2))
theorem checked_22_20 : check 143 p_22_20 cert_22_20 = true := by decide +kernel
theorem safe_22_20 : ∀ m, compatible p_22_20 m → WeightedBound 143 m := sound 143 _ cert_22_20 (by decide) checked_22_20
def p_22_21 := refine p_22 (5,false) (some ⟨false,true,5⟩)
def cert_22_21 : Tree := (split 13 (5,true) 6 #[
(.side 0 14 false (2)),
(.side 0 33 false (2)),
(.side 7 8 false (1)),
(.side 19 19 false (2)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (0)),
(.side 1 13 false (2)),
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.side 13 6 false (-1)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.last 14 (4,false)),
(.last 14 (4,false)),
(.last 14 (4,false)),
(.last 14 (4,false)),
(.side 19 1 true (1)),
(.side 17 1 true (3)),
(.side 12 2 true (-2)),
(.side 17 1 true (3))])
theorem checked_22_21 : check 143 p_22_21 cert_22_21 = true := by decide +kernel
theorem safe_22_21 : ∀ m, compatible p_22_21 m → WeightedBound 143 m := sound 143 _ cert_22_21 (by decide) checked_22_21
def p_22_22 := refine p_22 (5,false) (some ⟨true,false,5⟩)
def cert_22_22 : Tree := (.side 12 1 false (-2))
theorem checked_22_22 : check 143 p_22_22 cert_22_22 = true := by decide +kernel
theorem safe_22_22 : ∀ m, compatible p_22_22 m → WeightedBound 143 m := sound 143 _ cert_22_22 (by decide) checked_22_22
def p_22_23 := refine p_22 (5,false) (some ⟨true,true,5⟩)
def cert_22_23 : Tree := (split 13 (5,true) 6 #[
(.side 7 14 false (1)),
(.side 27 27 false (-1)),
(.side 7 12 false (1)),
(.side 6 18 false (2)),
(.side 7 10 false (1)),
(.side 7 20 false (1)),
(.side 7 10 false (1)),
(.side 7 18 false (1)),
(.last 15 (4,false)),
(.side 7 20 false (1)),
(.last 15 (4,false)),
(.side 2 12 false (2)),
(.side 8 6 false (0)),
(.side 7 14 false (1)),
(.side 8 6 false (0)),
(.side 4 10 false (2)),
(.side 11 3 false (-1)),
(.last 14 (4,false)),
(.side 11 3 false (-1)),
(.last 14 (4,false)),
(.side 26 1 true (-4)),
(.side 17 1 true (3)),
(.side 12 3 false (-1)),
(.side 17 1 true (3))])
theorem checked_22_23 : check 143 p_22_23 cert_22_23 = true := by decide +kernel
theorem safe_22_23 : ∀ m, compatible p_22_23 m → WeightedBound 143 m := sound 143 _ cert_22_23 (by decide) checked_22_23
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 143 m := by
  apply split_safe 143 p_22 12 (5,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_22_0 | exact safe_22_1 | exact safe_22_2 | exact safe_22_3 | exact safe_22_4 | exact safe_22_5 | exact safe_22_6 | exact safe_22_7 | exact safe_22_8 | exact safe_22_9 | exact safe_22_10 | exact safe_22_11 | exact safe_22_12 | exact safe_22_13 | exact safe_22_14 | exact safe_22_15 | exact safe_22_16 | exact safe_22_17 | exact safe_22_18 | exact safe_22_19 | exact safe_22_20 | exact safe_22_21 | exact safe_22_22 | exact safe_22_23 | omega
def p_23 := refine parent (4,true) (some ⟨true,true,5⟩)
def p_23_0 := refine p_23 (5,false) (some ⟨false,false,0⟩)
def cert_23_0 : Tree := (.side 7 13 false (1))
theorem checked_23_0 : check 143 p_23_0 cert_23_0 = true := by decide +kernel
theorem safe_23_0 : ∀ m, compatible p_23_0 m → WeightedBound 143 m := sound 143 _ cert_23_0 (by decide) checked_23_0
def p_23_1 := refine p_23 (5,false) (some ⟨false,true,0⟩)
def cert_23_1 : Tree := (.side 0 20 true (-1))
theorem checked_23_1 : check 143 p_23_1 cert_23_1 = true := by decide +kernel
theorem safe_23_1 : ∀ m, compatible p_23_1 m → WeightedBound 143 m := sound 143 _ cert_23_1 (by decide) checked_23_1
def p_23_2 := refine p_23 (5,false) (some ⟨true,false,0⟩)
def cert_23_2 : Tree := (.side 7 11 false (1))
theorem checked_23_2 : check 143 p_23_2 cert_23_2 = true := by decide +kernel
theorem safe_23_2 : ∀ m, compatible p_23_2 m → WeightedBound 143 m := sound 143 _ cert_23_2 (by decide) checked_23_2
def p_23_3 := refine p_23 (5,false) (some ⟨true,true,0⟩)
def cert_23_3 : Tree := (.side 6 9 false (2))
theorem checked_23_3 : check 143 p_23_3 cert_23_3 = true := by decide +kernel
theorem safe_23_3 : ∀ m, compatible p_23_3 m → WeightedBound 143 m := sound 143 _ cert_23_3 (by decide) checked_23_3
def p_23_4 := refine p_23 (5,false) (some ⟨false,false,1⟩)
def cert_23_4 : Tree := (.side 7 9 false (1))
theorem checked_23_4 : check 143 p_23_4 cert_23_4 = true := by decide +kernel
theorem safe_23_4 : ∀ m, compatible p_23_4 m → WeightedBound 143 m := sound 143 _ cert_23_4 (by decide) checked_23_4
def p_23_5 := refine p_23 (5,false) (some ⟨false,true,1⟩)
def cert_23_5 : Tree := (.side 24 19 false (2))
theorem checked_23_5 : check 143 p_23_5 cert_23_5 = true := by decide +kernel
theorem safe_23_5 : ∀ m, compatible p_23_5 m → WeightedBound 143 m := sound 143 _ cert_23_5 (by decide) checked_23_5
def p_23_6 := refine p_23 (5,false) (some ⟨true,false,1⟩)
def cert_23_6 : Tree := (.side 7 9 false (1))
theorem checked_23_6 : check 143 p_23_6 cert_23_6 = true := by decide +kernel
theorem safe_23_6 : ∀ m, compatible p_23_6 m → WeightedBound 143 m := sound 143 _ cert_23_6 (by decide) checked_23_6
def p_23_7 := refine p_23 (5,false) (some ⟨true,true,1⟩)
def cert_23_7 : Tree := (.side 24 17 false (2))
theorem checked_23_7 : check 143 p_23_7 cert_23_7 = true := by decide +kernel
theorem safe_23_7 : ∀ m, compatible p_23_7 m → WeightedBound 143 m := sound 143 _ cert_23_7 (by decide) checked_23_7
def p_23_8 := refine p_23 (5,false) (some ⟨false,false,2⟩)
def cert_23_8 : Tree := (split 14 (4,false) 6 #[
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.side 7 9 false (1)),
(.side 7 20 false (1)),
(.side 7 17 false (1)),
(.side 7 17 false (1)),
(.side 9 6 false (0)),
(.side 1 14 false (2)),
(.side 0 16 false (2)),
(.side 0 16 false (2)),
(.side 10 11 false (0)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 7 10 false (1)),
(.side 7 10 false (1)),
(.side 7 14 false (1)),
(.side 14 1 false (-2)),
(.side 21 1 true (1)),
(.side 14 1 false (-2)),
(.side 33 1 true (-3)),
(.side 0 17 false (2)),
(.side 0 17 false (2)),
(.side 0 17 false (2)),
(.side 12 3 false (0))])
theorem checked_23_8 : check 143 p_23_8 cert_23_8 = true := by decide +kernel
theorem safe_23_8 : ∀ m, compatible p_23_8 m → WeightedBound 143 m := sound 143 _ cert_23_8 (by decide) checked_23_8
def p_23_9 := refine p_23 (5,false) (some ⟨false,true,2⟩)
def cert_23_9 : Tree := (.side 28 19 false (2))
theorem checked_23_9 : check 143 p_23_9 cert_23_9 = true := by decide +kernel
theorem safe_23_9 : ∀ m, compatible p_23_9 m → WeightedBound 143 m := sound 143 _ cert_23_9 (by decide) checked_23_9
def p_23_10 := refine p_23 (5,false) (some ⟨true,false,2⟩)
def cert_23_10 : Tree := (split 14 (4,false) 6 #[
(.side 0 15 false (2)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 14 false (1)),
(.side 7 17 false (1)),
(.side 9 6 true (-2)),
(.side 9 6 false (0)),
(.side 10 9 false (0)),
(.side 0 16 false (2)),
(.side 10 11 false (0)),
(.side 10 11 false (0)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 7 10 false (1)),
(.side 7 10 false (1)),
(.side 7 14 false (1)),
(.side 14 1 false (-2)),
(.last 22 (5,true)),
(.side 14 1 false (-2)),
(.last 28 (5,true)),
(.side 10 12 false (0)),
(.side 10 12 false (0)),
(.side 10 12 false (0)),
(.side 12 3 false (0))])
theorem checked_23_10 : check 143 p_23_10 cert_23_10 = true := by decide +kernel
theorem safe_23_10 : ∀ m, compatible p_23_10 m → WeightedBound 143 m := sound 143 _ cert_23_10 (by decide) checked_23_10
def p_23_11 := refine p_23 (5,false) (some ⟨true,true,2⟩)
def cert_23_11 : Tree := (.side 2 11 false (2))
theorem checked_23_11 : check 143 p_23_11 cert_23_11 = true := by decide +kernel
theorem safe_23_11 : ∀ m, compatible p_23_11 m → WeightedBound 143 m := sound 143 _ cert_23_11 (by decide) checked_23_11
def p_23_12 := refine p_23 (5,false) (some ⟨false,false,3⟩)
def cert_23_12 : Tree := (.side 8 5 false (0))
theorem checked_23_12 : check 143 p_23_12 cert_23_12 = true := by decide +kernel
theorem safe_23_12 : ∀ m, compatible p_23_12 m → WeightedBound 143 m := sound 143 _ cert_23_12 (by decide) checked_23_12
def p_23_13 := refine p_23 (5,false) (some ⟨false,true,3⟩)
def cert_23_13 : Tree := (.side 7 13 false (1))
theorem checked_23_13 : check 143 p_23_13 cert_23_13 = true := by decide +kernel
theorem safe_23_13 : ∀ m, compatible p_23_13 m → WeightedBound 143 m := sound 143 _ cert_23_13 (by decide) checked_23_13
def p_23_14 := refine p_23 (5,false) (some ⟨true,false,3⟩)
def cert_23_14 : Tree := (.side 8 5 false (0))
theorem checked_23_14 : check 143 p_23_14 cert_23_14 = true := by decide +kernel
theorem safe_23_14 : ∀ m, compatible p_23_14 m → WeightedBound 143 m := sound 143 _ cert_23_14 (by decide) checked_23_14
def p_23_15 := refine p_23 (5,false) (some ⟨true,true,3⟩)
def cert_23_15 : Tree := (.side 4 9 false (2))
theorem checked_23_15 : check 143 p_23_15 cert_23_15 = true := by decide +kernel
theorem safe_23_15 : ∀ m, compatible p_23_15 m → WeightedBound 143 m := sound 143 _ cert_23_15 (by decide) checked_23_15
def p_23_16 := refine p_23 (5,false) (some ⟨false,false,4⟩)
def cert_23_16 : Tree := (.side 11 2 true (-1))
theorem checked_23_16 : check 143 p_23_16 cert_23_16 = true := by decide +kernel
theorem safe_23_16 : ∀ m, compatible p_23_16 m → WeightedBound 143 m := sound 143 _ cert_23_16 (by decide) checked_23_16
def p_23_17 := refine p_23 (5,false) (some ⟨false,true,4⟩)
def cert_23_17 : Tree := (split 13 (4,false) 6 #[
(.side 28 19 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4)],[(true,3)],[(false,6)],[(false,7)],[(true,8)],[(true,9),(true,23)],[(false,10)],[(false,11)],[(true,12)],[(true,13)],[(true,11)],[(false,15)],[(false,16)],[(true,17)],[(true,15)],[(true,7)],[(false,20)],[(false,21),(false,26)],[(true,22)],[(true,20)],[(true,21),(true,26)],[(false,25)],[(true,25)]],#[(0,1),(3,2),(0,0),(4,6),(0,5),(0,0),(7,0),(8,20),(0,9),(0,10),(11,0),(12,15),(0,13),(0,14),(0,0),(16,19),(17,0),(0,18),(0,0),(0,0),(21,24),(22,25),(0,23),(0,10),(0,0),(26,27),(22,25),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[(false,3),(true,3),(true,5),(false,6),(true,6),(false,9),(true,9),(false,10),(true,11),(false,14),(true,14),(false,15),(true,15),(false,19),(true,19),(false,20),(true,21),(false,23),(true,23),(true,25),(false,26),(true,26),(false,27),(true,27),(false,28),(true,29),(false,32),(true,32),(false,33),(true,33),(false,34),(true,34),(false,35),(true,36),(false,38),(true,38),(false,39),(true,39),(false,43),(true,43),(false,46),(true,47),(false,49),(true,49),(false,50),(true,50),(false,51),(true,51),(false,54),(true,55),(false,57),(true,57),(false,58),(true,58)],[(false,4)],[(true,4)],[(false,5)],[(false,7)],[(true,7)],[(false,8)],[(true,8)],[(true,10)],[(false,11)],[(false,12)],[(true,12)],[(false,13)],[(true,13)],[(false,16)],[(true,16)],[(false,17)],[(true,17)],[(false,18)],[(true,18)],[(true,20)],[(false,21)],[(false,22),(false,40)],[(true,22),(true,40)],[(false,24)],[(true,24)],[(false,25)],[(true,28)],[(false,29),(true,31)],[(false,30)],[(true,30)],[(false,31)],[(true,35)],[(false,36)],[(false,37)],[(true,37)],[(false,41)],[(true,41)],[(false,42)],[(true,42)],[(false,44)],[(true,44)],[(false,45)],[(true,45),(true,53)],[(true,46)],[(false,47)],[(false,48),(false,56)],[(true,48),(true,56)],[(false,52)],[(true,52)],[(false,53)],[(true,54)],[(false,55)]],#[(0,1),(2,3),(4,5),(6,6),(7,8),(9,6),(6,6),(10,11),(12,13),(6,6),(6,14),(15,6),(16,17),(18,19),(6,6),(6,6),(20,21),(22,23),(24,25),(6,6),(6,26),(27,6),(28,29),(6,6),(30,31),(32,6),(6,6),(6,6),(6,33),(34,6),(35,36),(37,34),(6,6),(6,6),(6,6),(6,38),(39,6),(40,41),(6,6),(6,6),(28,29),(42,43),(44,45),(6,6),(46,47),(48,49),(6,50),(51,6),(52,53),(6,6),(6,6),(6,6),(54,55),(56,49),(6,57),(58,6),(52,53),(6,6),(6,6)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .leaf (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty (.branch .empty (.branch .leaf (.branch .empty .leaf))))) (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf)) .empty))))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty)))) (.branch (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) .empty) .empty) (.branch .leaf (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty))))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf)) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .leaf))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) .empty) .leaf)) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)))))),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty))) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) .leaf)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch .empty .leaf))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch .empty (.branch .empty .leaf))) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .leaf (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty))) (.branch (.branch (.branch .leaf (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .leaf) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .leaf (.branch .leaf (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))))) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty) .empty))))),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .leaf (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) .empty)))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty))) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .empty))))),.empty]⟩),
(.side 7 13 false (1)),
(.side 3 11 true (-1)),
(.side 1 13 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[(true,4)],[(false,5)],[(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[(false,4),(false,12)],[(true,4),(true,12)],[(false,9)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch .leaf (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .leaf) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) (.branch .empty (.branch .leaf (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .leaf) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .leaf) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),.empty]⟩),
(.side 18 5 true (2)),
(.side 1 20 true (-1)),
(.side 7 15 false (1)),
(.side 0 17 true (-1)),
(.side 7 15 false (1)),
(.side 24 19 false (2)),
(.side 7 13 false (1)),
(.side 14 9 true (1)),
(.side 7 13 false (1)),
(.side 14 17 false (2)),
(.side 11 4 true (-1)),
(.side 16 1 true (4)),
(.last 16 (5,true)),
(.side 16 1 true (4)),
(.side 12 2 true (0)),
(.last 14 (5,true)),
(.last 16 (5,true)),
(.last 14 (5,true))])
theorem checked_23_17 : check 143 p_23_17 cert_23_17 = true := by decide +kernel
theorem safe_23_17 : ∀ m, compatible p_23_17 m → WeightedBound 143 m := sound 143 _ cert_23_17 (by decide) checked_23_17
def p_23_18 := refine p_23 (5,false) (some ⟨true,false,4⟩)
def cert_23_18 : Tree := (split 14 (5,true) 6 #[
(.side 7 15 false (1)),
(.side 0 24 true (-1)),
(.side 7 13 false (1)),
(.side 6 11 false (2)),
(.side 7 11 false (1)),
(.side 28 21 false (2)),
(.side 7 11 false (1)),
(.side 28 19 false (2)),
(.last 16 (4,false)),
(.side 32 21 false (2)),
(.last 16 (4,false)),
(.side 2 13 false (2)),
(.side 8 7 false (0)),
(.side 7 15 false (1)),
(.side 8 7 false (0)),
(.side 4 11 false (2)),
(.side 11 4 true (-1)),
(.last 15 (4,false)),
(.side 13 2 true (-1)),
(.last 15 (4,false)),
(.last 17 (4,false)),
(.last 16 (4,false)),
(.last 17 (4,false)),
(.side 18 3 true (2))])
theorem checked_23_18 : check 143 p_23_18 cert_23_18 = true := by decide +kernel
theorem safe_23_18 : ∀ m, compatible p_23_18 m → WeightedBound 143 m := sound 143 _ cert_23_18 (by decide) checked_23_18
def p_23_19 := refine p_23 (5,false) (some ⟨true,true,4⟩)
def cert_23_19 : Tree := (split 13 (4,false) 6 #[
(.side 3 11 false (2)),
(.side 4 15 false (3)),
(.side 5 9 false (2)),
(.side 6 13 false (3)),
(.side 7 7 false (1)),
(.side 4 11 false (2)),
(.side 7 7 false (1)),
(.side 6 9 false (2)),
(.side 10 4 true (-1)),
(.side 6 19 false (3)),
(.last 18 (5,true)),
(.side 24 17 false (2)),
(.side 7 11 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,3),(true,1),(true,5)],[(false,2),(false,5)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),.empty]⟩),
(.side 7 11 false (1)),
(.side 14 15 false (2)),
(.side 16 3 true (2)),
(.side 16 1 true (4)),
(.last 15 (5,true)),
(.side 16 1 true (4)),
(.last 14 (5,true)),
(.last 14 (5,true)),
(.last 14 (5,true)),
(.last 14 (5,true))])
theorem checked_23_19 : check 143 p_23_19 cert_23_19 = true := by decide +kernel
theorem safe_23_19 : ∀ m, compatible p_23_19 m → WeightedBound 143 m := sound 143 _ cert_23_19 (by decide) checked_23_19
def p_23_20 := refine p_23 (5,false) (some ⟨false,false,5⟩)
def cert_23_20 : Tree := (split 13 (5,true) 6 #[
(.side 0 14 false (2)),
(.side 0 20 true (-1)),
(.side 7 8 false (1)),
(.side 28 19 false (2)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (0)),
(.side 1 13 false (2)),
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.last 22 (4,false)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.last 14 (4,false)),
(.last 14 (4,false)),
(.last 14 (4,false)),
(.last 14 (4,false)),
(.side 14 1 false (-2)),
(.side 14 1 false (0)),
(.side 14 1 false (-2)),
(.side 12 2 true (-1))])
theorem checked_23_20 : check 143 p_23_20 cert_23_20 = true := by decide +kernel
theorem safe_23_20 : ∀ m, compatible p_23_20 m → WeightedBound 143 m := sound 143 _ cert_23_20 (by decide) checked_23_20
def p_23_21 := refine p_23 (5,false) (some ⟨false,true,5⟩)
def cert_23_21 : Tree := (split 14 (5,true) 6 #[
(.side 0 15 true (-1)),
(.side 0 15 true (-1)),
(.side 21 1 true (1)),
(.side 146 1 true (8)),
(.side 24 23 false (0)),
(.side 12 18 true (0)),
(.side 18 1 true (2)),
(.side 1 14 true (-1)),
(.side 6 56 false (2)),
(.side 0 16 true (-1)),
(.side 20 1 true (2)),
(.side 73 1 true (3)),
(.side 38 1 true (-2)),
(.side 22 1 true (2)),
(.side 6 38 false (2)),
(.side 65 15 true (-1)),
(.last 15 (4,false)),
(.last 15 (4,false)),
(.last 15 (4,false)),
(.last 15 (4,false)),
(.side 15 1 true (1)),
(.side 15 1 true (3)),
(.side 13 2 true (1)),
(.side 15 1 true (3))])
theorem checked_23_21 : check 143 p_23_21 cert_23_21 = true := by decide +kernel
theorem safe_23_21 : ∀ m, compatible p_23_21 m → WeightedBound 143 m := sound 143 _ cert_23_21 (by decide) checked_23_21
def p_23_22 := refine p_23 (5,false) (some ⟨true,false,5⟩)
def cert_23_22 : Tree := (split 13 (5,true) 6 #[
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 7 8 false (1)),
(.side 3 11 false (2)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 9 5 false (0)),
(.side 7 7 false (1)),
(.side 0 15 false (2)),
(.last 15 (4,false)),
(.last 22 (4,false)),
(.side 10 4 true (-1)),
(.side 7 9 false (1)),
(.side 8 6 true (-1)),
(.side 7 9 false (1)),
(.side 7 11 false (1)),
(.last 14 (4,false)),
(.last 19 (4,false)),
(.last 14 (4,false)),
(.last 19 (4,false)),
(.side 14 1 false (-2)),
(.side 15 1 false (1)),
(.side 14 1 false (-2)),
(.side 17 3 true (1))])
theorem checked_23_22 : check 143 p_23_22 cert_23_22 = true := by decide +kernel
theorem safe_23_22 : ∀ m, compatible p_23_22 m → WeightedBound 143 m := sound 143 _ cert_23_22 (by decide) checked_23_22
def p_23_23 := refine p_23 (5,false) (some ⟨true,true,5⟩)
def cert_23_23 : Tree := (split 14 (5,true) 6 #[
(.side 6 32 false (2)),
(.side 0 15 true (-1)),
(.side 6 28 false (2)),
(.side 22 13 false (4)),
(.side 6 24 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,2),(true,1)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 6 24 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,2),(true,1)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),.empty,(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 17 1 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6)],[],[(false,3),(false,5)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),.empty,(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.side 13 4 true (0)),
(.side 6 15 false (3)),
(.side 6 9 false (2)),
(.side 6 32 false (3)),
(.side 6 9 false (2)),
(.side 6 13 false (3)),
(.side 16 1 true (2)),
(.last 15 (4,false)),
(.side 14 2 true (1)),
(.last 15 (4,false)),
(.side 18 1 true (-2)),
(.side 15 1 true (3)),
(.side 16 3 false (0)),
(.side 15 1 true (3))])
theorem checked_23_23 : check 143 p_23_23 cert_23_23 = true := by decide +kernel
theorem safe_23_23 : ∀ m, compatible p_23_23 m → WeightedBound 143 m := sound 143 _ cert_23_23 (by decide) checked_23_23
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 143 m := by
  apply split_safe 143 p_23 12 (5,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_23_0 | exact safe_23_1 | exact safe_23_2 | exact safe_23_3 | exact safe_23_4 | exact safe_23_5 | exact safe_23_6 | exact safe_23_7 | exact safe_23_8 | exact safe_23_9 | exact safe_23_10 | exact safe_23_11 | exact safe_23_12 | exact safe_23_13 | exact safe_23_14 | exact safe_23_15 | exact safe_23_16 | exact safe_23_17 | exact safe_23_18 | exact safe_23_19 | exact safe_23_20 | exact safe_23_21 | exact safe_23_22 | exact safe_23_23 | omega
theorem safe : ∀ m, compatible parent m → WeightedBound 143 m := by
  apply split_safe 143 parent 11 (4,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23 | omega
theorem cover : Cover (WeightedBound 143) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra91
