import PhaseTree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent47Root33
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,true,1⟩)
  | _,_ => none)
def p_0 := refine parent (4,false) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.side 0 28 true (-2))
theorem checked_0 : check 162 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 162 m := sound 162 _ cert_0 (by decide) checked_0
def p_1 := refine parent (4,false) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 0 28 true (-2))
theorem checked_1 : check 162 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 162 m := sound 162 _ cert_1 (by decide) checked_1
def p_2 := refine parent (4,false) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 26 3 true (4))
theorem checked_2 : check 162 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 162 m := sound 162 _ cert_2 (by decide) checked_2
def p_3 := refine parent (4,false) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 24 18 true (2))
theorem checked_3 : check 162 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 162 m := sound 162 _ cert_3 (by decide) checked_3
def p_4 := refine parent (4,false) (some ⟨false,false,1⟩)
def cert_4 : Tree := (.side 15 13 true (1))
theorem checked_4 : check 162 p_4 cert_4 = true := by decide +kernel
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 162 m := sound 162 _ cert_4 (by decide) checked_4
def p_5 := refine parent (4,false) (some ⟨false,true,1⟩)
def cert_5 : Tree := (.side 15 13 true (1))
theorem checked_5 : check 162 p_5 cert_5 = true := by decide +kernel
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 162 m := sound 162 _ cert_5 (by decide) checked_5
def p_6 := refine parent (4,false) (some ⟨true,false,1⟩)
def p_6_0 := refine p_6 (2,true) (some ⟨false,false,0⟩)
def cert_6_0 : Tree := (.side 17 13 true (1))
theorem checked_6_0 : check 162 p_6_0 cert_6_0 = true := by decide +kernel
theorem safe_6_0 : ∀ m, compatible p_6_0 m → WeightedBound 162 m := sound 162 _ cert_6_0 (by decide) checked_6_0
def p_6_1 := refine p_6 (2,true) (some ⟨false,true,0⟩)
def cert_6_1 : Tree := (.side 11 36 true (-1))
theorem checked_6_1 : check 162 p_6_1 cert_6_1 = true := by decide +kernel
theorem safe_6_1 : ∀ m, compatible p_6_1 m → WeightedBound 162 m := sound 162 _ cert_6_1 (by decide) checked_6_1
def p_6_2 := refine p_6 (2,true) (some ⟨true,false,0⟩)
def cert_6_2 : Tree := (.side 19 11 true (1))
theorem checked_6_2 : check 162 p_6_2 cert_6_2 = true := by decide +kernel
theorem safe_6_2 : ∀ m, compatible p_6_2 m → WeightedBound 162 m := sound 162 _ cert_6_2 (by decide) checked_6_2
def p_6_3 := refine p_6 (2,true) (some ⟨true,true,0⟩)
def cert_6_3 : Tree := (.side 11 34 true (-1))
theorem checked_6_3 : check 162 p_6_3 cert_6_3 = true := by decide +kernel
theorem safe_6_3 : ∀ m, compatible p_6_3 m → WeightedBound 162 m := sound 162 _ cert_6_3 (by decide) checked_6_3
def p_6_4 := refine p_6 (2,true) (some ⟨false,false,1⟩)
def cert_6_4 : Tree := (.side 26 4 true (4))
theorem checked_6_4 : check 162 p_6_4 cert_6_4 = true := by decide +kernel
theorem safe_6_4 : ∀ m, compatible p_6_4 m → WeightedBound 162 m := sound 162 _ cert_6_4 (by decide) checked_6_4
def p_6_5 := refine p_6 (2,true) (some ⟨false,true,1⟩)
def cert_6_5 : Tree := (.side 24 21 true (2))
theorem checked_6_5 : check 162 p_6_5 cert_6_5 = true := by decide +kernel
theorem safe_6_5 : ∀ m, compatible p_6_5 m → WeightedBound 162 m := sound 162 _ cert_6_5 (by decide) checked_6_5
def p_6_6 := refine p_6 (2,true) (some ⟨true,false,1⟩)
def cert_6_6 : Tree := (.side 13 17 true (1))
theorem checked_6_6 : check 162 p_6_6 cert_6_6 = true := by decide +kernel
theorem safe_6_6 : ∀ m, compatible p_6_6 m → WeightedBound 162 m := sound 162 _ cert_6_6 (by decide) checked_6_6
def p_6_7 := refine p_6 (2,true) (some ⟨true,true,1⟩)
def cert_6_7 : Tree := (.side 24 19 true (2))
theorem checked_6_7 : check 162 p_6_7 cert_6_7 = true := by decide +kernel
theorem safe_6_7 : ∀ m, compatible p_6_7 m → WeightedBound 162 m := sound 162 _ cert_6_7 (by decide) checked_6_7
def p_6_8 := refine p_6 (2,true) (some ⟨false,false,2⟩)
def cert_6_8 : Tree := (.side 0 54 true (-2))
theorem checked_6_8 : check 162 p_6_8 cert_6_8 = true := by decide +kernel
theorem safe_6_8 : ∀ m, compatible p_6_8 m → WeightedBound 162 m := sound 162 _ cert_6_8 (by decide) checked_6_8
def p_6_9 := refine p_6 (2,true) (some ⟨false,true,2⟩)
def cert_6_9 : Tree := (.side 24 21 true (2))
theorem checked_6_9 : check 162 p_6_9 cert_6_9 = true := by decide +kernel
theorem safe_6_9 : ∀ m, compatible p_6_9 m → WeightedBound 162 m := sound 162 _ cert_6_9 (by decide) checked_6_9
def p_6_10 := refine p_6 (2,true) (some ⟨true,false,2⟩)
def cert_6_10 : Tree := (.side 42 6 false (0))
theorem checked_6_10 : check 162 p_6_10 cert_6_10 = true := by decide +kernel
theorem safe_6_10 : ∀ m, compatible p_6_10 m → WeightedBound 162 m := sound 162 _ cert_6_10 (by decide) checked_6_10
def p_6_11 := refine p_6 (2,true) (some ⟨true,true,2⟩)
def cert_6_11 : Tree := (.side 2 28 true (-2))
theorem checked_6_11 : check 162 p_6_11 cert_6_11 = true := by decide +kernel
theorem safe_6_11 : ∀ m, compatible p_6_11 m → WeightedBound 162 m := sound 162 _ cert_6_11 (by decide) checked_6_11
def p_6_12 := refine p_6 (2,true) (some ⟨false,false,3⟩)
def cert_6_12 : Tree := (.side 13 20 true (1))
theorem checked_6_12 : check 162 p_6_12 cert_6_12 = true := by decide +kernel
theorem safe_6_12 : ∀ m, compatible p_6_12 m → WeightedBound 162 m := sound 162 _ cert_6_12 (by decide) checked_6_12
def p_6_13 := refine p_6 (2,true) (some ⟨false,true,3⟩)
def cert_6_13 : Tree := (.side 26 6 true (4))
theorem checked_6_13 : check 162 p_6_13 cert_6_13 = true := by decide +kernel
theorem safe_6_13 : ∀ m, compatible p_6_13 m → WeightedBound 162 m := sound 162 _ cert_6_13 (by decide) checked_6_13
def p_6_14 := refine p_6 (2,true) (some ⟨true,false,3⟩)
def cert_6_14 : Tree := (.side 21 9 true (1))
theorem checked_6_14 : check 162 p_6_14 cert_6_14 = true := by decide +kernel
theorem safe_6_14 : ∀ m, compatible p_6_14 m → WeightedBound 162 m := sound 162 _ cert_6_14 (by decide) checked_6_14
def p_6_15 := refine p_6 (2,true) (some ⟨true,true,3⟩)
def cert_6_15 : Tree := (.side 4 26 true (-2))
theorem checked_6_15 : check 162 p_6_15 cert_6_15 = true := by decide +kernel
theorem safe_6_15 : ∀ m, compatible p_6_15 m → WeightedBound 162 m := sound 162 _ cert_6_15 (by decide) checked_6_15
def p_6_16 := refine p_6 (2,true) (some ⟨false,false,4⟩)
def cert_6_16 : Tree := (.side 14 16 true (1))
theorem checked_6_16 : check 162 p_6_16 cert_6_16 = true := by decide +kernel
theorem safe_6_16 : ∀ m, compatible p_6_16 m → WeightedBound 162 m := sound 162 _ cert_6_16 (by decide) checked_6_16
def p_6_17 := refine p_6 (2,true) (some ⟨false,true,4⟩)
def cert_6_17 : Tree := (.side 27 3 true (4))
theorem checked_6_17 : check 162 p_6_17 cert_6_17 = true := by decide +kernel
theorem safe_6_17 : ∀ m, compatible p_6_17 m → WeightedBound 162 m := sound 162 _ cert_6_17 (by decide) checked_6_17
def p_6_18 := refine p_6 (2,true) (some ⟨true,false,4⟩)
def cert_6_18 : Tree := (.side 25 5 true (3))
theorem checked_6_18 : check 162 p_6_18 cert_6_18 = true := by decide +kernel
theorem safe_6_18 : ∀ m, compatible p_6_18 m → WeightedBound 162 m := sound 162 _ cert_6_18 (by decide) checked_6_18
def p_6_19 := refine p_6 (2,true) (some ⟨true,true,4⟩)
def cert_6_19 : Tree := (.side 13 18 true (1))
theorem checked_6_19 : check 162 p_6_19 cert_6_19 = true := by decide +kernel
theorem safe_6_19 : ∀ m, compatible p_6_19 m → WeightedBound 162 m := sound 162 _ cert_6_19 (by decide) checked_6_19
def p_6_20 := refine p_6 (2,true) (some ⟨false,false,5⟩)
def cert_6_20 : Tree := (split 30 (5,true) 6 #[
(.side 11 37 true (-1)),
(.side 0 31 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 24 21 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 15 16 true (1)),
(.side 13 24 true (1)),
(.side 1 30 true (-2)),
(.side 0 54 true (-2)),
(.side 0 32 true (-2)),
(.last 51 (5,false)),
(.side 16 15 true (1)),
(.side 6 50 false (5)),
(.side 26 7 true (4)),
(.side 13 20 true (1)),
(.side 18 13 true (1)),
(.side 100 21 false (0)),
(.side 27 4 true (4)),
(.side 49 4 false (1)),
(.side 13 19 true (1)),
(.last 31 (5,false)),
(.last 31 (5,false)),
(.last 31 (5,false)),
(.last 31 (5,false))])
theorem checked_6_20 : check 162 p_6_20 cert_6_20 = true := by decide +kernel
theorem safe_6_20 : ∀ m, compatible p_6_20 m → WeightedBound 162 m := sound 162 _ cert_6_20 (by decide) checked_6_20
def p_6_21 := refine p_6 (2,true) (some ⟨false,true,5⟩)
def cert_6_21 : Tree := (split 30 (5,false) 6 #[
(.side 24 21 true (2)),
(.side 0 31 true (-2)),
(.side 26 6 true (4)),
(.side 24 27 true (2)),
(.side 1 30 true (-2)),
(.side 15 16 true (1)),
(.side 28 3 true (4)),
(.side 11 36 true (-1)),
(.side 16 15 true (1)),
(.side 11 38 true (-1)),
(.side 7 28 true (-2)),
(.side 24 21 true (2)),
(.side 18 13 true (1)),
(.side 26 7 true (4)),
(.side 7 26 true (-2)),
(.side 24 19 true (2)),
(.side 13 19 true (1)),
(.side 27 4 true (4)),
(.side 24 8 true (2)),
(.side 13 19 true (1)),
(.last 32 (5,true)),
(.side 30 1 true (6)),
(.last 32 (5,true)),
(.side 30 1 true (6))])
theorem checked_6_21 : check 162 p_6_21 cert_6_21 = true := by decide +kernel
theorem safe_6_21 : ∀ m, compatible p_6_21 m → WeightedBound 162 m := sound 162 _ cert_6_21 (by decide) checked_6_21
def p_6_22 := refine p_6 (2,true) (some ⟨true,false,5⟩)
def cert_6_22 : Tree := (split 30 (5,true) 6 #[
(.side 11 37 true (-1)),
(.side 17 14 true (1)),
(.side 13 19 true (1)),
(.side 3 28 true (-2)),
(.side 11 35 true (-1)),
(.side 26 5 true (4)),
(.side 74 3 false (7)),
(.side 26 5 true (4)),
(.side 11 35 true (-1)),
(.last 32 (5,false)),
(.last 51 (5,false)),
(.side 29 2 true (4)),
(.side 46 34 false (3)),
(.side 13 21 true (1)),
(.side 22 9 true (1)),
(.side 20 11 true (1)),
(.side 46 4 false (1)),
(.side 14 17 true (1)),
(.side 11 25 true (-1)),
(.side 24 23 true (2)),
(.last 31 (5,false)),
(.last 32 (5,false)),
(.last 31 (5,false)),
(.last 32 (5,false))])
theorem checked_6_22 : check 162 p_6_22 cert_6_22 = true := by decide +kernel
theorem safe_6_22 : ∀ m, compatible p_6_22 m → WeightedBound 162 m := sound 162 _ cert_6_22 (by decide) checked_6_22
def p_6_23 := refine p_6 (2,true) (some ⟨true,true,5⟩)
def cert_6_23 : Tree := (split 30 (5,false) 6 #[
(.side 3 28 true (-2)),
(.side 24 27 true (2)),
(.side 5 26 true (-2)),
(.side 24 25 true (2)),
(.side 26 5 true (4)),
(.side 11 36 true (-1)),
(.side 13 18 true (1)),
(.side 11 34 true (-1)),
(.side 29 2 true (5)),
(.side 11 36 true (-1)),
(.last 32 (5,true)),
(.side 24 19 true (2)),
(.side 20 11 true (1)),
(.side 26 7 true (4)),
(.side 7 24 true (-2)),
(.side 24 17 true (2)),
(.side 24 23 true (2)),
(.side 27 4 true (4)),
(.side 25 6 true (3)),
(.side 13 19 true (1)),
(.last 31 (5,true)),
(.side 30 1 true (6)),
(.last 31 (5,true)),
(.side 30 1 true (6))])
theorem checked_6_23 : check 162 p_6_23 cert_6_23 = true := by decide +kernel
theorem safe_6_23 : ∀ m, compatible p_6_23 m → WeightedBound 162 m := sound 162 _ cert_6_23 (by decide) checked_6_23
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 162 m := by
  apply split_safe 162 p_6 29 (2,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_6_0 | exact safe_6_1 | exact safe_6_2 | exact safe_6_3 | exact safe_6_4 | exact safe_6_5 | exact safe_6_6 | exact safe_6_7 | exact safe_6_8 | exact safe_6_9 | exact safe_6_10 | exact safe_6_11 | exact safe_6_12 | exact safe_6_13 | exact safe_6_14 | exact safe_6_15 | exact safe_6_16 | exact safe_6_17 | exact safe_6_18 | exact safe_6_19 | exact safe_6_20 | exact safe_6_21 | exact safe_6_22 | exact safe_6_23 | omega
def p_7 := refine parent (4,false) (some ⟨true,true,1⟩)
def cert_7 : Tree := (.side 1 27 true (-2))
theorem checked_7 : check 162 p_7 cert_7 = true := by decide +kernel
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 162 m := sound 162 _ cert_7 (by decide) checked_7
def p_8 := refine parent (4,false) (some ⟨false,false,2⟩)
def cert_8 : Tree := (.side 11 35 true (-1))
theorem checked_8 : check 162 p_8 cert_8 = true := by decide +kernel
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 162 m := sound 162 _ cert_8 (by decide) checked_8
def p_9 := refine parent (4,false) (some ⟨false,true,2⟩)
def cert_9 : Tree := (.side 0 29 true (-2))
theorem checked_9 : check 162 p_9 cert_9 = true := by decide +kernel
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 162 m := sound 162 _ cert_9 (by decide) checked_9
def p_10 := refine parent (4,false) (some ⟨true,false,2⟩)
def p_10_0 := refine p_10 (2,true) (some ⟨false,false,0⟩)
def cert_10_0 : Tree := (.side 11 35 true (-1))
theorem checked_10_0 : check 162 p_10_0 cert_10_0 = true := by decide +kernel
theorem safe_10_0 : ∀ m, compatible p_10_0 m → WeightedBound 162 m := sound 162 _ cert_10_0 (by decide) checked_10_0
def p_10_1 := refine p_10 (2,true) (some ⟨false,true,0⟩)
def cert_10_1 : Tree := (.side 54 28 true (2))
theorem checked_10_1 : check 162 p_10_1 cert_10_1 = true := by decide +kernel
theorem safe_10_1 : ∀ m, compatible p_10_1 m → WeightedBound 162 m := sound 162 _ cert_10_1 (by decide) checked_10_1
def p_10_2 := refine p_10 (2,true) (some ⟨true,false,0⟩)
def cert_10_2 : Tree := (.side 11 33 true (-1))
theorem checked_10_2 : check 162 p_10_2 cert_10_2 = true := by decide +kernel
theorem safe_10_2 : ∀ m, compatible p_10_2 m → WeightedBound 162 m := sound 162 _ cert_10_2 (by decide) checked_10_2
def p_10_3 := refine p_10 (2,true) (some ⟨true,true,0⟩)
def cert_10_3 : Tree := (.side 52 26 true (2))
theorem checked_10_3 : check 162 p_10_3 cert_10_3 = true := by decide +kernel
theorem safe_10_3 : ∀ m, compatible p_10_3 m → WeightedBound 162 m := sound 162 _ cert_10_3 (by decide) checked_10_3
def p_10_4 := refine p_10 (2,true) (some ⟨false,false,1⟩)
def cert_10_4 : Tree := (.side 11 37 true (-1))
theorem checked_10_4 : check 162 p_10_4 cert_10_4 = true := by decide +kernel
theorem safe_10_4 : ∀ m, compatible p_10_4 m → WeightedBound 162 m := sound 162 _ cert_10_4 (by decide) checked_10_4
def p_10_5 := refine p_10 (2,true) (some ⟨false,true,1⟩)
def cert_10_5 : Tree := (.side 11 43 true (-1))
theorem checked_10_5 : check 162 p_10_5 cert_10_5 = true := by decide +kernel
theorem safe_10_5 : ∀ m, compatible p_10_5 m → WeightedBound 162 m := sound 162 _ cert_10_5 (by decide) checked_10_5
def p_10_6 := refine p_10 (2,true) (some ⟨true,false,1⟩)
def cert_10_6 : Tree := (.side 13 19 true (1))
theorem checked_10_6 : check 162 p_10_6 cert_10_6 = true := by decide +kernel
theorem safe_10_6 : ∀ m, compatible p_10_6 m → WeightedBound 162 m := sound 162 _ cert_10_6 (by decide) checked_10_6
def p_10_7 := refine p_10 (2,true) (some ⟨true,true,1⟩)
def cert_10_7 : Tree := (.side 11 41 true (-1))
theorem checked_10_7 : check 162 p_10_7 cert_10_7 = true := by decide +kernel
theorem safe_10_7 : ∀ m, compatible p_10_7 m → WeightedBound 162 m := sound 162 _ cert_10_7 (by decide) checked_10_7
def p_10_8 := refine p_10 (2,true) (some ⟨false,false,2⟩)
def cert_10_8 : Tree := (.side 2 50 false (5))
theorem checked_10_8 : check 162 p_10_8 cert_10_8 = true := by decide +kernel
theorem safe_10_8 : ∀ m, compatible p_10_8 m → WeightedBound 162 m := sound 162 _ cert_10_8 (by decide) checked_10_8
def p_10_9 := refine p_10 (2,true) (some ⟨false,true,2⟩)
def cert_10_9 : Tree := (.side 11 43 true (-1))
theorem checked_10_9 : check 162 p_10_9 cert_10_9 = true := by decide +kernel
theorem safe_10_9 : ∀ m, compatible p_10_9 m → WeightedBound 162 m := sound 162 _ cert_10_9 (by decide) checked_10_9
def p_10_10 := refine p_10 (2,true) (some ⟨true,false,2⟩)
def cert_10_10 : Tree := (.side 11 33 true (-1))
theorem checked_10_10 : check 162 p_10_10 cert_10_10 = true := by decide +kernel
theorem safe_10_10 : ∀ m, compatible p_10_10 m → WeightedBound 162 m := sound 162 _ cert_10_10 (by decide) checked_10_10
def p_10_11 := refine p_10 (2,true) (some ⟨true,true,2⟩)
def cert_10_11 : Tree := (.side 48 20 true (2))
theorem checked_10_11 : check 162 p_10_11 cert_10_11 = true := by decide +kernel
theorem safe_10_11 : ∀ m, compatible p_10_11 m → WeightedBound 162 m := sound 162 _ cert_10_11 (by decide) checked_10_11
def p_10_12 := refine p_10 (2,true) (some ⟨false,false,3⟩)
def cert_10_12 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_10_12 : check 162 p_10_12 cert_10_12 = true := by decide +kernel
theorem safe_10_12 : ∀ m, compatible p_10_12 m → WeightedBound 162 m := sound 162 _ cert_10_12 (by decide) checked_10_12
def p_10_13 := refine p_10 (2,true) (some ⟨false,true,3⟩)
def cert_10_13 : Tree := (.side 11 43 true (-1))
theorem checked_10_13 : check 162 p_10_13 cert_10_13 = true := by decide +kernel
theorem safe_10_13 : ∀ m, compatible p_10_13 m → WeightedBound 162 m := sound 162 _ cert_10_13 (by decide) checked_10_13
def p_10_14 := refine p_10 (2,true) (some ⟨true,false,3⟩)
def cert_10_14 : Tree := (.side 11 31 true (-1))
theorem checked_10_14 : check 162 p_10_14 cert_10_14 = true := by decide +kernel
theorem safe_10_14 : ∀ m, compatible p_10_14 m → WeightedBound 162 m := sound 162 _ cert_10_14 (by decide) checked_10_14
def p_10_15 := refine p_10 (2,true) (some ⟨true,true,3⟩)
def cert_10_15 : Tree := (.side 46 18 true (2))
theorem checked_10_15 : check 162 p_10_15 cert_10_15 = true := by decide +kernel
theorem safe_10_15 : ∀ m, compatible p_10_15 m → WeightedBound 162 m := sound 162 _ cert_10_15 (by decide) checked_10_15
def p_10_16 := refine p_10 (2,true) (some ⟨false,false,4⟩)
def cert_10_16 : Tree := (.side 52 24 true (2))
theorem checked_10_16 : check 162 p_10_16 cert_10_16 = true := by decide +kernel
theorem safe_10_16 : ∀ m, compatible p_10_16 m → WeightedBound 162 m := sound 162 _ cert_10_16 (by decide) checked_10_16
def p_10_17 := refine p_10 (2,true) (some ⟨false,true,4⟩)
def cert_10_17 : Tree := (.side 48 20 true (2))
theorem checked_10_17 : check 162 p_10_17 cert_10_17 = true := by decide +kernel
theorem safe_10_17 : ∀ m, compatible p_10_17 m → WeightedBound 162 m := sound 162 _ cert_10_17 (by decide) checked_10_17
def p_10_18 := refine p_10 (2,true) (some ⟨true,false,4⟩)
def cert_10_18 : Tree := (.side 25 7 true (3))
theorem checked_10_18 : check 162 p_10_18 cert_10_18 = true := by decide +kernel
theorem safe_10_18 : ∀ m, compatible p_10_18 m → WeightedBound 162 m := sound 162 _ cert_10_18 (by decide) checked_10_18
def p_10_19 := refine p_10 (2,true) (some ⟨true,true,4⟩)
def cert_10_19 : Tree := (.side 56 30 true (2))
theorem checked_10_19 : check 162 p_10_19 cert_10_19 = true := by decide +kernel
theorem safe_10_19 : ∀ m, compatible p_10_19 m → WeightedBound 162 m := sound 162 _ cert_10_19 (by decide) checked_10_19
def p_10_20 := refine p_10 (2,true) (some ⟨false,false,5⟩)
def cert_10_20 : Tree := (split 32 (5,true) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 11 45 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 11 43 true (-1)),
(.side 7 39 true (-2)),
(.side 52 24 true (2)),
(.side 13 20 true (1)),
(.side 50 22 true (2)),
(.last 34 (5,false)),
(.side 52 24 true (2)),
(.last 34 (5,false)),
(.side 11 37 true (-1)),
(.side 7 29 true (-2)),
(.side 52 24 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 11 35 true (-1)),
(.side 14 19 true (1)),
(.side 11 37 true (-1)),
(.side 25 8 true (3)),
(.last 38 (5,false)),
(.last 34 (5,false)),
(.last 33 (5,false)),
(.last 34 (5,false)),
(.last 33 (5,false))])
theorem checked_10_20 : check 162 p_10_20 cert_10_20 = true := by decide +kernel
theorem safe_10_20 : ∀ m, compatible p_10_20 m → WeightedBound 162 m := sound 162 _ cert_10_20 (by decide) checked_10_20
def p_10_21 := refine p_10 (2,true) (some ⟨false,true,5⟩)
def cert_10_21 : Tree := (split 32 (5,false) 6 #[
(.side 11 43 true (-1)),
(.side 0 33 true (-2)),
(.side 11 43 true (-1)),
(.side 11 49 true (-1)),
(.side 50 22 true (2)),
(.side 15 18 true (1)),
(.side 30 3 true (4)),
(.side 54 28 true (2)),
(.side 11 37 true (-1)),
(.side 56 30 true (2)),
(.side 48 20 true (2)),
(.side 11 43 true (-1)),
(.side 11 35 true (-1)),
(.side 56 30 true (2)),
(.side 46 18 true (2)),
(.side 11 41 true (-1)),
(.last 35 (5,true)),
(.side 27 6 true (3)),
(.last 35 (5,true)),
(.last 35 (5,true)),
(.last 34 (5,true)),
(.side 32 1 true (6)),
(.last 34 (5,true)),
(.side 32 1 true (6))])
theorem checked_10_21 : check 162 p_10_21 cert_10_21 = true := by decide +kernel
theorem safe_10_21 : ∀ m, compatible p_10_21 m → WeightedBound 162 m := sound 162 _ cert_10_21 (by decide) checked_10_21
def p_10_22 := refine p_10 (2,true) (some ⟨true,false,5⟩)
def cert_10_22 : Tree := (split 32 (5,true) 6 #[
(.side 11 35 true (-1)),
(.side 50 22 true (2)),
(.side 11 33 true (-1)),
(.side 48 20 true (2)),
(.side 11 41 true (-1)),
(.side 26 7 true (3)),
(.side 24 9 true (2)),
(.side 50 22 true (2)),
(.last 34 (5,false)),
(.last 34 (5,false)),
(.last 34 (5,false)),
(.side 31 2 true (4)),
(.side 101 123 true (1)),
(.side 11 35 true (-1)),
(.side 11 31 true (-1)),
(.side 11 33 true (-1)),
(.side 84 26 false (2)),
(.side 14 19 true (1)),
(.side 12 21 true (0)),
(.side 11 45 true (-1)),
(.last 34 (5,false)),
(.last 34 (5,false)),
(.last 34 (5,false)),
(.last 34 (5,false))])
theorem checked_10_22 : check 162 p_10_22 cert_10_22 = true := by decide +kernel
theorem safe_10_22 : ∀ m, compatible p_10_22 m → WeightedBound 162 m := sound 162 _ cert_10_22 (by decide) checked_10_22
def p_10_23 := refine p_10 (2,true) (some ⟨true,true,5⟩)
def cert_10_23 : Tree := (split 32 (5,false) 6 #[
(.side 48 20 true (2)),
(.side 11 49 true (-1)),
(.side 46 18 true (2)),
(.side 11 47 true (-1)),
(.side 50 22 true (2)),
(.side 54 28 true (2)),
(.side 13 20 true (1)),
(.side 52 26 true (2)),
(.side 31 2 true (5)),
(.side 54 28 true (2)),
(.last 34 (5,true)),
(.side 11 41 true (-1)),
(.side 11 33 true (-1)),
(.side 54 28 true (2)),
(.side 44 16 true (2)),
(.side 11 39 true (-1)),
(.side 11 45 true (-1)),
(.side 11 41 true (-1)),
(.side 25 8 true (3)),
(.last 35 (5,true)),
(.last 33 (5,true)),
(.side 32 1 true (6)),
(.last 33 (5,true)),
(.side 32 1 true (6))])
theorem checked_10_23 : check 162 p_10_23 cert_10_23 = true := by decide +kernel
theorem safe_10_23 : ∀ m, compatible p_10_23 m → WeightedBound 162 m := sound 162 _ cert_10_23 (by decide) checked_10_23
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 162 m := by
  apply split_safe 162 p_10 31 (2,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_10_0 | exact safe_10_1 | exact safe_10_2 | exact safe_10_3 | exact safe_10_4 | exact safe_10_5 | exact safe_10_6 | exact safe_10_7 | exact safe_10_8 | exact safe_10_9 | exact safe_10_10 | exact safe_10_11 | exact safe_10_12 | exact safe_10_13 | exact safe_10_14 | exact safe_10_15 | exact safe_10_16 | exact safe_10_17 | exact safe_10_18 | exact safe_10_19 | exact safe_10_20 | exact safe_10_21 | exact safe_10_22 | exact safe_10_23 | omega
def p_11 := refine parent (4,false) (some ⟨true,true,2⟩)
def cert_11 : Tree := (.side 16 12 true (1))
theorem checked_11 : check 162 p_11 cert_11 = true := by decide +kernel
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 162 m := sound 162 _ cert_11 (by decide) checked_11
def p_12 := refine parent (4,false) (some ⟨false,false,3⟩)
def cert_12 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_12 : check 162 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 162 m := sound 162 _ cert_12 (by decide) checked_12
def p_13 := refine parent (4,false) (some ⟨false,true,3⟩)
def cert_13 : Tree := (.side 26 4 true (4))
theorem checked_13 : check 162 p_13 cert_13 = true := by decide +kernel
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 162 m := sound 162 _ cert_13 (by decide) checked_13
def p_14 := refine parent (4,false) (some ⟨true,false,3⟩)
def cert_14 : Tree := (.side 13 17 true (1))
theorem checked_14 : check 162 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 162 m := sound 162 _ cert_14 (by decide) checked_14
def p_15 := refine parent (4,false) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 18 10 true (1))
theorem checked_15 : check 162 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 162 m := sound 162 _ cert_15 (by decide) checked_15
def p_16 := refine parent (4,false) (some ⟨false,false,4⟩)
def cert_16 : Tree := (.side 86 17 false (0))
theorem checked_16 : check 162 p_16 cert_16 = true := by decide +kernel
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 162 m := sound 162 _ cert_16 (by decide) checked_16
def p_17 := refine parent (4,false) (some ⟨false,true,4⟩)
def cert_17 : Tree := (.side 27 1 true (5))
theorem checked_17 : check 162 p_17 cert_17 = true := by decide +kernel
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 162 m := sound 162 _ cert_17 (by decide) checked_17
def p_18 := refine parent (4,false) (some ⟨true,false,4⟩)
def cert_18 : Tree := (.side 11 21 true (-1))
theorem checked_18 : check 162 p_18 cert_18 = true := by decide +kernel
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 162 m := sound 162 _ cert_18 (by decide) checked_18
def p_19 := refine parent (4,false) (some ⟨true,true,4⟩)
def cert_19 : Tree := (.side 27 1 true (5))
theorem checked_19 : check 162 p_19 cert_19 = true := by decide +kernel
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 162 m := sound 162 _ cert_19 (by decide) checked_19
def p_20 := refine parent (4,false) (some ⟨false,false,5⟩)
def p_20_0 := refine p_20 (5,false) (some ⟨false,false,0⟩)
def cert_20_0 : Tree := (.side 11 35 true (-1))
theorem checked_20_0 : check 162 p_20_0 cert_20_0 = true := by decide +kernel
theorem safe_20_0 : ∀ m, compatible p_20_0 m → WeightedBound 162 m := sound 162 _ cert_20_0 (by decide) checked_20_0
def p_20_1 := refine p_20 (5,false) (some ⟨false,true,0⟩)
def cert_20_1 : Tree := (.side 0 29 true (-2))
theorem checked_20_1 : check 162 p_20_1 cert_20_1 = true := by decide +kernel
theorem safe_20_1 : ∀ m, compatible p_20_1 m → WeightedBound 162 m := sound 162 _ cert_20_1 (by decide) checked_20_1
def p_20_2 := refine p_20 (5,false) (some ⟨true,false,0⟩)
def cert_20_2 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty]⟩)
theorem checked_20_2 : check 162 p_20_2 cert_20_2 = true := by decide +kernel
theorem safe_20_2 : ∀ m, compatible p_20_2 m → WeightedBound 162 m := sound 162 _ cert_20_2 (by decide) checked_20_2
def p_20_3 := refine p_20 (5,false) (some ⟨true,true,0⟩)
def cert_20_3 : Tree := (.side 24 19 true (2))
theorem checked_20_3 : check 162 p_20_3 cert_20_3 = true := by decide +kernel
theorem safe_20_3 : ∀ m, compatible p_20_3 m → WeightedBound 162 m := sound 162 _ cert_20_3 (by decide) checked_20_3
def p_20_4 := refine p_20 (5,false) (some ⟨false,false,1⟩)
def cert_20_4 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),.empty]⟩)
theorem checked_20_4 : check 162 p_20_4 cert_20_4 = true := by decide +kernel
theorem safe_20_4 : ∀ m, compatible p_20_4 m → WeightedBound 162 m := sound 162 _ cert_20_4 (by decide) checked_20_4
def p_20_5 := refine p_20 (5,false) (some ⟨false,true,1⟩)
def cert_20_5 : Tree := (.side 15 14 true (1))
theorem checked_20_5 : check 162 p_20_5 cert_20_5 = true := by decide +kernel
theorem safe_20_5 : ∀ m, compatible p_20_5 m → WeightedBound 162 m := sound 162 _ cert_20_5 (by decide) checked_20_5
def p_20_6 := refine p_20 (5,false) (some ⟨true,false,1⟩)
def cert_20_6 : Tree := (split 30 (2,true) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),.empty]⟩),
(.side 11 43 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),.empty]⟩),
(.side 11 41 true (-1)),
(.side 13 26 true (1)),
(.side 50 22 true (2)),
(.side 13 18 true (1)),
(.side 48 20 true (2)),
(.side 2 46 false (5)),
(.side 50 22 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),.empty]⟩),
(.side 11 35 true (-1)),
(.side 7 27 true (-2)),
(.side 13 23 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),.empty]⟩),
(.side 11 33 true (-1)),
(.side 14 17 true (1)),
(.side 13 20 true (1)),
(.side 25 6 true (3)),
(.last 32 (5,true)),
(.last 31 (5,true)),
(.side 28 3 true (3)),
(.last 31 (5,true)),
(.side 13 19 true (1))])
theorem checked_20_6 : check 162 p_20_6 cert_20_6 = true := by decide +kernel
theorem safe_20_6 : ∀ m, compatible p_20_6 m → WeightedBound 162 m := sound 162 _ cert_20_6 (by decide) checked_20_6
def p_20_7 := refine p_20 (5,false) (some ⟨true,true,1⟩)
def cert_20_7 : Tree := (.side 1 28 true (-2))
theorem checked_20_7 : check 162 p_20_7 cert_20_7 = true := by decide +kernel
theorem safe_20_7 : ∀ m, compatible p_20_7 m → WeightedBound 162 m := sound 162 _ cert_20_7 (by decide) checked_20_7
def p_20_8 := refine p_20 (5,false) (some ⟨false,false,2⟩)
def cert_20_8 : Tree := (.side 0 50 true (-2))
theorem checked_20_8 : check 162 p_20_8 cert_20_8 = true := by decide +kernel
theorem safe_20_8 : ∀ m, compatible p_20_8 m → WeightedBound 162 m := sound 162 _ cert_20_8 (by decide) checked_20_8
def p_20_9 := refine p_20 (5,false) (some ⟨false,true,2⟩)
def cert_20_9 : Tree := (.side 0 30 true (-2))
theorem checked_20_9 : check 162 p_20_9 cert_20_9 = true := by decide +kernel
theorem safe_20_9 : ∀ m, compatible p_20_9 m → WeightedBound 162 m := sound 162 _ cert_20_9 (by decide) checked_20_9
def p_20_10 := refine p_20 (5,false) (some ⟨true,false,2⟩)
def cert_20_10 : Tree := (split 32 (2,true) 6 #[
(.side 3 50 true (-2)),
(.side 11 43 true (-1)),
(.side 5 46 true (-2)),
(.side 11 41 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 11 66 true (-1)),
(.side 13 20 true (1)),
(.side 11 62 true (-1)),
(.side 33 26 false (3)),
(.side 11 66 true (-1)),
(.side 40 6 false (0)),
(.side 11 35 true (-1)),
(.side 6 27 true (-2)),
(.side 11 39 true (-1)),
(.side 7 42 true (-2)),
(.side 11 33 true (-1)),
(.side 11 39 true (-1)),
(.side 14 22 true (1)),
(.side 7 58 true (-2)),
(.last 34 (5,true)),
(.last 33 (5,true)),
(.side 11 35 true (-1)),
(.last 33 (5,true)),
(.last 35 (5,true))])
theorem checked_20_10 : check 162 p_20_10 cert_20_10 = true := by decide +kernel
theorem safe_20_10 : ∀ m, compatible p_20_10 m → WeightedBound 162 m := sound 162 _ cert_20_10 (by decide) checked_20_10
def p_20_11 := refine p_20 (5,false) (some ⟨true,true,2⟩)
def cert_20_11 : Tree := (.side 16 13 true (1))
theorem checked_20_11 : check 162 p_20_11 cert_20_11 = true := by decide +kernel
theorem safe_20_11 : ∀ m, compatible p_20_11 m → WeightedBound 162 m := sound 162 _ cert_20_11 (by decide) checked_20_11
def p_20_12 := refine p_20 (5,false) (some ⟨false,false,3⟩)
def cert_20_12 : Tree := (.side 6 42 false (5))
theorem checked_20_12 : check 162 p_20_12 cert_20_12 = true := by decide +kernel
theorem safe_20_12 : ∀ m, compatible p_20_12 m → WeightedBound 162 m := sound 162 _ cert_20_12 (by decide) checked_20_12
def p_20_13 := refine p_20 (5,false) (some ⟨false,true,3⟩)
def cert_20_13 : Tree := (.side 26 5 true (4))
theorem checked_20_13 : check 162 p_20_13 cert_20_13 = true := by decide +kernel
theorem safe_20_13 : ∀ m, compatible p_20_13 m → WeightedBound 162 m := sound 162 _ cert_20_13 (by decide) checked_20_13
def p_20_14 := refine p_20 (5,false) (some ⟨true,false,3⟩)
def cert_20_14 : Tree := (.side 13 18 true (1))
theorem checked_20_14 : check 162 p_20_14 cert_20_14 = true := by decide +kernel
theorem safe_20_14 : ∀ m, compatible p_20_14 m → WeightedBound 162 m := sound 162 _ cert_20_14 (by decide) checked_20_14
def p_20_15 := refine p_20 (5,false) (some ⟨true,true,3⟩)
def cert_20_15 : Tree := (.side 18 11 true (1))
theorem checked_20_15 : check 162 p_20_15 cert_20_15 = true := by decide +kernel
theorem safe_20_15 : ∀ m, compatible p_20_15 m → WeightedBound 162 m := sound 162 _ cert_20_15 (by decide) checked_20_15
def p_20_16 := refine p_20 (5,false) (some ⟨false,false,4⟩)
def cert_20_16 : Tree := (.side 86 17 false (0))
theorem checked_20_16 : check 162 p_20_16 cert_20_16 = true := by decide +kernel
theorem safe_20_16 : ∀ m, compatible p_20_16 m → WeightedBound 162 m := sound 162 _ cert_20_16 (by decide) checked_20_16
def p_20_17 := refine p_20 (5,false) (some ⟨false,true,4⟩)
def cert_20_17 : Tree := (.side 27 2 true (4))
theorem checked_20_17 : check 162 p_20_17 cert_20_17 = true := by decide +kernel
theorem safe_20_17 : ∀ m, compatible p_20_17 m → WeightedBound 162 m := sound 162 _ cert_20_17 (by decide) checked_20_17
def p_20_18 := refine p_20 (5,false) (some ⟨true,false,4⟩)
def cert_20_18 : Tree := (split 38 (5,true) 6 #[
(.side 63 2 false (-3)),
(.side 45 2 false (1)),
(.side 45 2 false (-1)),
(.side 35 10 true (-2)),
(.side 57 2 false (-3)),
(.last 40 (2,true)),
(.last 40 (2,true)),
(.last 40 (2,true)),
(.last 56 (2,true)),
(.last 42 (2,true)),
(.last 42 (2,true)),
(.last 52 (2,true)),
(.side 46 2 false (-2)),
(.last 44 (2,true)),
(.last 44 (2,true)),
(.last 50 (2,true)),
(.side 39 2 false (-3)),
(.side 39 2 false (-1)),
(.side 39 2 false (-3)),
(.side 37 2 true (-2)),
(.side 39 2 false (-3)),
(.side 39 2 false (-1)),
(.side 39 2 false (-3)),
(.last 44 (2,true))])
theorem checked_20_18 : check 162 p_20_18 cert_20_18 = true := by decide +kernel
theorem safe_20_18 : ∀ m, compatible p_20_18 m → WeightedBound 162 m := sound 162 _ cert_20_18 (by decide) checked_20_18
def p_20_19 := refine p_20 (5,false) (some ⟨true,true,4⟩)
def cert_20_19 : Tree := (split 30 (5,true) 6 #[
(.side 11 37 true (-1)),
(.side 0 31 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))]⟩),
(.side 24 21 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))]⟩),
(.side 15 16 true (1)),
(.last 32 (2,true)),
(.side 1 30 true (-2)),
(.side 0 54 true (-2)),
(.side 0 32 true (-2)),
(.last 34 (2,true)),
(.side 16 15 true (1)),
(.side 6 50 false (5)),
(.side 26 7 true (4)),
(.side 13 20 true (1)),
(.side 18 13 true (1)),
(.side 100 21 false (0)),
(.side 27 4 true (4)),
(.side 45 4 false (-1)),
(.side 29 2 true (4)),
(.side 44 3 false (-2)),
(.side 28 3 true (4)),
(.side 52 24 true (2)),
(.side 28 3 true (4))])
theorem checked_20_19 : check 162 p_20_19 cert_20_19 = true := by decide +kernel
theorem safe_20_19 : ∀ m, compatible p_20_19 m → WeightedBound 162 m := sound 162 _ cert_20_19 (by decide) checked_20_19
def p_20_20 := refine p_20 (5,false) (some ⟨false,false,5⟩)
def cert_20_20 : Tree := (split 31 (5,true) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))]⟩),
(.side 0 32 true (-2)),
(.side 53 5 false (-3)),
(.side 28 84 false (5)),
(.side 53 17 false (-1)),
(.side 87 17 false (-1)),
(.last 33 (2,true)),
(.side 1 31 true (-2)),
(.side 0 58 false (5)),
(.side 0 33 true (-2)),
(.last 35 (2,true)),
(.side 2 46 false (5)),
(.side 36 22 false (1)),
(.side 30 6 true (1)),
(.side 7 46 false (5)),
(.side 4 42 false (5)),
(.side 36 1 false (-4)),
(.side 38 1 false (-2)),
(.side 36 1 false (-4)),
(.side 31 2 true (1)),
(.side 35 1 false (-3)),
(.side 37 1 false (-1)),
(.side 35 1 false (-3)),
(.side 30 2 true (1))])
theorem checked_20_20 : check 162 p_20_20 cert_20_20 = true := by decide +kernel
theorem safe_20_20 : ∀ m, compatible p_20_20 m → WeightedBound 162 m := sound 162 _ cert_20_20 (by decide) checked_20_20
def p_20_21 := refine p_20 (5,false) (some ⟨false,true,5⟩)
def cert_20_21 : Tree := (.side 28 1 true (4))
theorem checked_20_21 : check 162 p_20_21 cert_20_21 = true := by decide +kernel
theorem safe_20_21 : ∀ m, compatible p_20_21 m → WeightedBound 162 m := sound 162 _ cert_20_21 (by decide) checked_20_21
def p_20_22 := refine p_20 (5,false) (some ⟨true,false,5⟩)
def cert_20_22 : Tree := (split 31 (5,true) 6 #[
(.last 34 (2,true)),
(.side 7 26 true (-2)),
(.side 10 22 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.side 47 32 true (-1)),
(.side 70 1 false (6)),
(.last 33 (2,true)),
(.side 24 8 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(false,8)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[(false,3)],[(true,3)],[(false,4)],[(true,4)],[(false,5),(true,5),(false,6),(true,6),(false,10),(true,10),(false,11),(true,11),(false,12),(true,12),(false,13),(true,13),(false,15),(true,15),(false,17),(true,17),(false,19),(true,19),(false,21),(true,21)],[(false,7)],[(true,7)],[(true,8)],[(false,9),(false,20)],[(true,9),(true,20)],[(false,14)],[(true,14)],[(false,16)],[(true,16)],[(false,18)],[(true,18)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,10),(10,10),(11,12),(1,13),(14,15),(10,10),(10,10),(10,10),(10,10),(16,17),(10,10),(18,19),(10,10),(20,21),(10,10),(14,15),(10,10)]⟩,⟨#[[(false,0)],[(true,0)],[(true,1),(true,7)],[(true,2)],[(true,3)],[(false,3)],[(false,5)],[(true,4)]],#[(0,1),(0,2),(0,3),(5,4),(0,7),(6,0),(0,0),(0,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)))),(.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))]⟩),
(.last 32 (2,true)),
(.last 35 (2,true)),
(.last 32 (2,true)),
(.last 44 (2,true)),
(.side 8 24 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.side 36 1 false (-4)),
(.side 12 20 true (0)),
(.side 36 1 false (-4)),
(.side 12 20 true (0)),
(.side 35 1 false (-3)),
(.side 50 1 false (6)),
(.side 35 1 false (-3)),
(.side 33 3 true (3))])
theorem checked_20_22 : check 162 p_20_22 cert_20_22 = true := by decide +kernel
theorem safe_20_22 : ∀ m, compatible p_20_22 m → WeightedBound 162 m := sound 162 _ cert_20_22 (by decide) checked_20_22
def p_20_23 := refine p_20 (5,false) (some ⟨true,true,5⟩)
def cert_20_23 : Tree := (.side 28 1 true (4))
theorem checked_20_23 : check 162 p_20_23 cert_20_23 = true := by decide +kernel
theorem safe_20_23 : ∀ m, compatible p_20_23 m → WeightedBound 162 m := sound 162 _ cert_20_23 (by decide) checked_20_23
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 162 m := by
  apply split_safe 162 p_20 28 (5,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_20_0 | exact safe_20_1 | exact safe_20_2 | exact safe_20_3 | exact safe_20_4 | exact safe_20_5 | exact safe_20_6 | exact safe_20_7 | exact safe_20_8 | exact safe_20_9 | exact safe_20_10 | exact safe_20_11 | exact safe_20_12 | exact safe_20_13 | exact safe_20_14 | exact safe_20_15 | exact safe_20_16 | exact safe_20_17 | exact safe_20_18 | exact safe_20_19 | exact safe_20_20 | exact safe_20_21 | exact safe_20_22 | exact safe_20_23 | omega
def p_21 := refine parent (4,false) (some ⟨false,true,5⟩)
def p_21_0 := refine p_21 (5,false) (some ⟨false,false,0⟩)
def cert_21_0 : Tree := (.side 0 29 true (-2))
theorem checked_21_0 : check 162 p_21_0 cert_21_0 = true := by decide +kernel
theorem safe_21_0 : ∀ m, compatible p_21_0 m → WeightedBound 162 m := sound 162 _ cert_21_0 (by decide) checked_21_0
def p_21_1 := refine p_21 (5,false) (some ⟨false,true,0⟩)
def cert_21_1 : Tree := (.side 0 29 true (-2))
theorem checked_21_1 : check 162 p_21_1 cert_21_1 = true := by decide +kernel
theorem safe_21_1 : ∀ m, compatible p_21_1 m → WeightedBound 162 m := sound 162 _ cert_21_1 (by decide) checked_21_1
def p_21_2 := refine p_21 (5,false) (some ⟨true,false,0⟩)
def cert_21_2 : Tree := (.side 26 4 true (4))
theorem checked_21_2 : check 162 p_21_2 cert_21_2 = true := by decide +kernel
theorem safe_21_2 : ∀ m, compatible p_21_2 m → WeightedBound 162 m := sound 162 _ cert_21_2 (by decide) checked_21_2
def p_21_3 := refine p_21 (5,false) (some ⟨true,true,0⟩)
def cert_21_3 : Tree := (.side 24 19 true (2))
theorem checked_21_3 : check 162 p_21_3 cert_21_3 = true := by decide +kernel
theorem safe_21_3 : ∀ m, compatible p_21_3 m → WeightedBound 162 m := sound 162 _ cert_21_3 (by decide) checked_21_3
def p_21_4 := refine p_21 (5,false) (some ⟨false,false,1⟩)
def cert_21_4 : Tree := (.side 15 14 true (1))
theorem checked_21_4 : check 162 p_21_4 cert_21_4 = true := by decide +kernel
theorem safe_21_4 : ∀ m, compatible p_21_4 m → WeightedBound 162 m := sound 162 _ cert_21_4 (by decide) checked_21_4
def p_21_5 := refine p_21 (5,false) (some ⟨false,true,1⟩)
def cert_21_5 : Tree := (.side 15 14 true (1))
theorem checked_21_5 : check 162 p_21_5 cert_21_5 = true := by decide +kernel
theorem safe_21_5 : ∀ m, compatible p_21_5 m → WeightedBound 162 m := sound 162 _ cert_21_5 (by decide) checked_21_5
def p_21_6 := refine p_21 (5,false) (some ⟨true,false,1⟩)
def cert_21_6 : Tree := (split 30 (2,true) 6 #[
(.side 17 14 true (1)),
(.side 11 37 true (-1)),
(.side 19 12 true (1)),
(.side 11 35 true (-1)),
(.side 26 5 true (4)),
(.side 24 22 true (2)),
(.side 13 18 true (1)),
(.side 24 20 true (2)),
(.side 11 39 true (-1)),
(.side 24 22 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),.empty]⟩),
(.side 2 29 true (-2)),
(.side 13 21 true (1)),
(.side 26 7 true (4)),
(.side 21 10 true (1)),
(.side 4 27 true (-2)),
(.side 14 17 true (1)),
(.side 27 4 true (5)),
(.side 25 6 true (3)),
(.side 27 4 true (5)),
(.last 31 (5,true)),
(.side 28 3 true (5)),
(.last 31 (5,true)),
(.side 13 19 true (1))])
theorem checked_21_6 : check 162 p_21_6 cert_21_6 = true := by decide +kernel
theorem safe_21_6 : ∀ m, compatible p_21_6 m → WeightedBound 162 m := sound 162 _ cert_21_6 (by decide) checked_21_6
def p_21_7 := refine p_21 (5,false) (some ⟨true,true,1⟩)
def cert_21_7 : Tree := (.side 1 28 true (-2))
theorem checked_21_7 : check 162 p_21_7 cert_21_7 = true := by decide +kernel
theorem safe_21_7 : ∀ m, compatible p_21_7 m → WeightedBound 162 m := sound 162 _ cert_21_7 (by decide) checked_21_7
def p_21_8 := refine p_21 (5,false) (some ⟨false,false,2⟩)
def cert_21_8 : Tree := (.side 0 30 true (-2))
theorem checked_21_8 : check 162 p_21_8 cert_21_8 = true := by decide +kernel
theorem safe_21_8 : ∀ m, compatible p_21_8 m → WeightedBound 162 m := sound 162 _ cert_21_8 (by decide) checked_21_8
def p_21_9 := refine p_21 (5,false) (some ⟨false,true,2⟩)
def cert_21_9 : Tree := (.side 0 30 true (-2))
theorem checked_21_9 : check 162 p_21_9 cert_21_9 = true := by decide +kernel
theorem safe_21_9 : ∀ m, compatible p_21_9 m → WeightedBound 162 m := sound 162 _ cert_21_9 (by decide) checked_21_9
def p_21_10 := refine p_21 (5,false) (some ⟨true,false,2⟩)
def cert_21_10 : Tree := (split 32 (2,true) 6 #[
(.side 3 30 true (-2)),
(.side 24 29 true (2)),
(.side 5 28 true (-2)),
(.side 24 27 true (2)),
(.side 26 7 true (4)),
(.side 11 38 true (-1)),
(.side 13 20 true (1)),
(.side 11 36 true (-1)),
(.side 0 62 true (-2)),
(.side 11 38 true (-1)),
(.side 46 6 false (0)),
(.side 24 21 true (2)),
(.side 20 13 true (1)),
(.side 26 9 true (4)),
(.side 7 26 true (-2)),
(.side 24 19 true (2)),
(.side 24 25 true (2)),
(.side 27 6 true (4)),
(.side 25 8 true (3)),
(.side 11 36 true (-1)),
(.last 33 (5,true)),
(.side 24 21 true (2)),
(.last 33 (5,true)),
(.last 35 (5,true))])
theorem checked_21_10 : check 162 p_21_10 cert_21_10 = true := by decide +kernel
theorem safe_21_10 : ∀ m, compatible p_21_10 m → WeightedBound 162 m := sound 162 _ cert_21_10 (by decide) checked_21_10
def p_21_11 := refine p_21 (5,false) (some ⟨true,true,2⟩)
def cert_21_11 : Tree := (.side 16 13 true (1))
theorem checked_21_11 : check 162 p_21_11 cert_21_11 = true := by decide +kernel
theorem safe_21_11 : ∀ m, compatible p_21_11 m → WeightedBound 162 m := sound 162 _ cert_21_11 (by decide) checked_21_11
def p_21_12 := refine p_21 (5,false) (some ⟨false,false,3⟩)
def cert_21_12 : Tree := (.side 26 5 true (4))
theorem checked_21_12 : check 162 p_21_12 cert_21_12 = true := by decide +kernel
theorem safe_21_12 : ∀ m, compatible p_21_12 m → WeightedBound 162 m := sound 162 _ cert_21_12 (by decide) checked_21_12
def p_21_13 := refine p_21 (5,false) (some ⟨false,true,3⟩)
def cert_21_13 : Tree := (.side 26 5 true (4))
theorem checked_21_13 : check 162 p_21_13 cert_21_13 = true := by decide +kernel
theorem safe_21_13 : ∀ m, compatible p_21_13 m → WeightedBound 162 m := sound 162 _ cert_21_13 (by decide) checked_21_13
def p_21_14 := refine p_21 (5,false) (some ⟨true,false,3⟩)
def cert_21_14 : Tree := (.side 13 18 true (1))
theorem checked_21_14 : check 162 p_21_14 cert_21_14 = true := by decide +kernel
theorem safe_21_14 : ∀ m, compatible p_21_14 m → WeightedBound 162 m := sound 162 _ cert_21_14 (by decide) checked_21_14
def p_21_15 := refine p_21 (5,false) (some ⟨true,true,3⟩)
def cert_21_15 : Tree := (.side 18 11 true (1))
theorem checked_21_15 : check 162 p_21_15 cert_21_15 = true := by decide +kernel
theorem safe_21_15 : ∀ m, compatible p_21_15 m → WeightedBound 162 m := sound 162 _ cert_21_15 (by decide) checked_21_15
def p_21_16 := refine p_21 (5,false) (some ⟨false,false,4⟩)
def cert_21_16 : Tree := (.side 27 2 true (5))
theorem checked_21_16 : check 162 p_21_16 cert_21_16 = true := by decide +kernel
theorem safe_21_16 : ∀ m, compatible p_21_16 m → WeightedBound 162 m := sound 162 _ cert_21_16 (by decide) checked_21_16
def p_21_17 := refine p_21 (5,false) (some ⟨false,true,4⟩)
def cert_21_17 : Tree := (.side 27 2 true (5))
theorem checked_21_17 : check 162 p_21_17 cert_21_17 = true := by decide +kernel
theorem safe_21_17 : ∀ m, compatible p_21_17 m → WeightedBound 162 m := sound 162 _ cert_21_17 (by decide) checked_21_17
def p_21_18 := refine p_21 (5,false) (some ⟨true,false,4⟩)
def cert_21_18 : Tree := (split 30 (5,true) 6 #[
(.side 0 31 true (-2)),
(.side 0 31 true (-2)),
(.side 26 6 true (4)),
(.side 24 21 true (2)),
(.side 15 16 true (1)),
(.side 15 16 true (1)),
(.last 32 (2,true)),
(.side 1 30 true (-2)),
(.side 0 32 true (-2)),
(.side 0 32 true (-2)),
(.last 34 (2,true)),
(.side 16 15 true (1)),
(.side 26 7 true (4)),
(.side 26 7 true (4)),
(.side 13 20 true (1)),
(.side 18 13 true (1)),
(.side 27 4 true (5)),
(.side 27 4 true (5)),
(.side 29 2 true (5)),
(.side 27 4 true (5)),
(.side 63 3 false (1)),
(.side 28 3 true (5)),
(.side 120 3 false (14)),
(.side 25 7 true (3))])
theorem checked_21_18 : check 162 p_21_18 cert_21_18 = true := by decide +kernel
theorem safe_21_18 : ∀ m, compatible p_21_18 m → WeightedBound 162 m := sound 162 _ cert_21_18 (by decide) checked_21_18
def p_21_19 := refine p_21 (5,false) (some ⟨true,true,4⟩)
def cert_21_19 : Tree := (.side 27 2 true (5))
theorem checked_21_19 : check 162 p_21_19 cert_21_19 = true := by decide +kernel
theorem safe_21_19 : ∀ m, compatible p_21_19 m → WeightedBound 162 m := sound 162 _ cert_21_19 (by decide) checked_21_19
def p_21_20 := refine p_21 (5,false) (some ⟨false,false,5⟩)
def cert_21_20 : Tree := (split 33 (5,true) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))]⟩),
(.side 0 34 true (-2)),
(.side 59 7 false (-1)),
(.side 28 90 false (6)),
(.side 55 19 false (1)),
(.side 93 19 false (1)),
(.last 35 (2,true)),
(.side 1 33 true (-2)),
(.side 0 62 false (6)),
(.side 0 35 true (-2)),
(.last 37 (2,true)),
(.side 2 50 false (6)),
(.side 38 24 false (2)),
(.side 30 8 true (1)),
(.side 7 50 false (6)),
(.side 4 46 false (6)),
(.side 40 1 false (-2)),
(.side 42 1 false (0)),
(.side 33 2 true (0)),
(.side 31 4 true (1)),
(.side 37 1 false (-3)),
(.side 39 1 false (-1)),
(.side 37 1 false (-3)),
(.side 32 2 true (1))])
theorem checked_21_20 : check 162 p_21_20 cert_21_20 = true := by decide +kernel
theorem safe_21_20 : ∀ m, compatible p_21_20 m → WeightedBound 162 m := sound 162 _ cert_21_20 (by decide) checked_21_20
def p_21_21 := refine p_21 (5,false) (some ⟨false,true,5⟩)
def cert_21_21 : Tree := (.side 28 1 true (6))
theorem checked_21_21 : check 162 p_21_21 cert_21_21 = true := by decide +kernel
theorem safe_21_21 : ∀ m, compatible p_21_21 m → WeightedBound 162 m := sound 162 _ cert_21_21 (by decide) checked_21_21
def p_21_22 := refine p_21 (5,false) (some ⟨true,false,5⟩)
def cert_21_22 : Tree := (split 33 (5,true) 6 #[
(.last 36 (2,true)),
(.side 11 30 true (-1)),
(.side 11 26 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.side 49 36 true (-1)),
(.side 86 1 false (14)),
(.last 35 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.last 156 (2,true)),
(.last 34 (2,true)),
(.last 37 (2,true)),
(.last 34 (2,true)),
(.side 79 27 true (1)),
(.side 11 28 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.side 40 1 false (-2)),
(.side 11 24 true (-1)),
(.side 33 2 true (0)),
(.side 11 24 true (-1)),
(.side 37 1 false (-3)),
(.side 58 1 false (8)),
(.side 37 1 false (-3)),
(.side 37 3 true (5))])
theorem checked_21_22 : check 162 p_21_22 cert_21_22 = true := by decide +kernel
theorem safe_21_22 : ∀ m, compatible p_21_22 m → WeightedBound 162 m := sound 162 _ cert_21_22 (by decide) checked_21_22
def p_21_23 := refine p_21 (5,false) (some ⟨true,true,5⟩)
def cert_21_23 : Tree := (.side 28 1 true (6))
theorem checked_21_23 : check 162 p_21_23 cert_21_23 = true := by decide +kernel
theorem safe_21_23 : ∀ m, compatible p_21_23 m → WeightedBound 162 m := sound 162 _ cert_21_23 (by decide) checked_21_23
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 162 m := by
  apply split_safe 162 p_21 28 (5,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_21_0 | exact safe_21_1 | exact safe_21_2 | exact safe_21_3 | exact safe_21_4 | exact safe_21_5 | exact safe_21_6 | exact safe_21_7 | exact safe_21_8 | exact safe_21_9 | exact safe_21_10 | exact safe_21_11 | exact safe_21_12 | exact safe_21_13 | exact safe_21_14 | exact safe_21_15 | exact safe_21_16 | exact safe_21_17 | exact safe_21_18 | exact safe_21_19 | exact safe_21_20 | exact safe_21_21 | exact safe_21_22 | exact safe_21_23 | omega
def p_22 := refine parent (4,false) (some ⟨true,false,5⟩)
def p_22_0 := refine p_22 (5,false) (some ⟨false,false,0⟩)
def cert_22_0 : Tree := (split 31 (2,true) 6 #[
(.side 11 35 true (-1)),
(.side 54 28 true (2)),
(.side 11 33 true (-1)),
(.side 52 26 true (2)),
(.side 11 37 true (-1)),
(.side 11 43 true (-1)),
(.side 13 19 true (1)),
(.side 11 41 true (-1)),
(.side 2 50 false (5)),
(.side 11 43 true (-1)),
(.side 11 33 true (-1)),
(.side 48 20 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.side 11 43 true (-1)),
(.side 11 31 true (-1)),
(.side 46 18 true (2)),
(.side 52 24 true (2)),
(.side 48 20 true (2)),
(.side 25 7 true (3)),
(.last 33 (5,true)),
(.last 32 (5,true)),
(.side 11 43 true (-1)),
(.last 32 (5,true)),
(.side 48 20 true (2))])
theorem checked_22_0 : check 162 p_22_0 cert_22_0 = true := by decide +kernel
theorem safe_22_0 : ∀ m, compatible p_22_0 m → WeightedBound 162 m := sound 162 _ cert_22_0 (by decide) checked_22_0
def p_22_1 := refine p_22 (5,false) (some ⟨false,true,0⟩)
def cert_22_1 : Tree := (.side 17 12 true (1))
theorem checked_22_1 : check 162 p_22_1 cert_22_1 = true := by decide +kernel
theorem safe_22_1 : ∀ m, compatible p_22_1 m → WeightedBound 162 m := sound 162 _ cert_22_1 (by decide) checked_22_1
def p_22_2 := refine p_22 (5,false) (some ⟨true,false,0⟩)
def cert_22_2 : Tree := (.side 13 17 true (1))
theorem checked_22_2 : check 162 p_22_2 cert_22_2 = true := by decide +kernel
theorem safe_22_2 : ∀ m, compatible p_22_2 m → WeightedBound 162 m := sound 162 _ cert_22_2 (by decide) checked_22_2
def p_22_3 := refine p_22 (5,false) (some ⟨true,true,0⟩)
def cert_22_3 : Tree := (.side 3 26 true (-2))
theorem checked_22_3 : check 162 p_22_3 cert_22_3 = true := by decide +kernel
theorem safe_22_3 : ∀ m, compatible p_22_3 m → WeightedBound 162 m := sound 162 _ cert_22_3 (by decide) checked_22_3
def p_22_4 := refine p_22 (5,false) (some ⟨false,false,1⟩)
def cert_22_4 : Tree := (.side 11 33 true (-1))
theorem checked_22_4 : check 162 p_22_4 cert_22_4 = true := by decide +kernel
theorem safe_22_4 : ∀ m, compatible p_22_4 m → WeightedBound 162 m := sound 162 _ cert_22_4 (by decide) checked_22_4
def p_22_5 := refine p_22 (5,false) (some ⟨false,true,1⟩)
def cert_22_5 : Tree := (.side 26 3 true (4))
theorem checked_22_5 : check 162 p_22_5 cert_22_5 = true := by decide +kernel
theorem safe_22_5 : ∀ m, compatible p_22_5 m → WeightedBound 162 m := sound 162 _ cert_22_5 (by decide) checked_22_5
def p_22_6 := refine p_22 (5,false) (some ⟨true,false,1⟩)
def cert_22_6 : Tree := (split 30 (2,true) 6 #[
(.side 11 33 true (-1)),
(.side 48 20 true (2)),
(.side 11 31 true (-1)),
(.side 46 18 true (2)),
(.side 84 5 false (7)),
(.side 26 5 true (3)),
(.side 24 7 true (2)),
(.side 24 10 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),.empty]⟩),
(.side 11 45 true (-1)),
(.side 11 31 true (-1)),
(.side 48 20 true (2)),
(.side 137 56 true (1)),
(.side 11 33 true (-1)),
(.side 11 29 true (-1)),
(.side 11 31 true (-1)),
(.side 14 20 true (1)),
(.side 14 17 true (1)),
(.side 12 19 true (0)),
(.side 11 43 true (-1)),
(.last 31 (5,true)),
(.last 31 (5,true)),
(.last 31 (5,true)),
(.last 31 (5,true))])
theorem checked_22_6 : check 162 p_22_6 cert_22_6 = true := by decide +kernel
theorem safe_22_6 : ∀ m, compatible p_22_6 m → WeightedBound 162 m := sound 162 _ cert_22_6 (by decide) checked_22_6
def p_22_7 := refine p_22 (5,false) (some ⟨true,true,1⟩)
def cert_22_7 : Tree := (.side 26 3 true (4))
theorem checked_22_7 : check 162 p_22_7 cert_22_7 = true := by decide +kernel
theorem safe_22_7 : ∀ m, compatible p_22_7 m → WeightedBound 162 m := sound 162 _ cert_22_7 (by decide) checked_22_7
def p_22_8 := refine p_22 (5,false) (some ⟨false,false,2⟩)
def cert_22_8 : Tree := (.side 11 33 true (-1))
theorem checked_22_8 : check 162 p_22_8 cert_22_8 = true := by decide +kernel
theorem safe_22_8 : ∀ m, compatible p_22_8 m → WeightedBound 162 m := sound 162 _ cert_22_8 (by decide) checked_22_8
def p_22_9 := refine p_22 (5,false) (some ⟨false,true,2⟩)
def cert_22_9 : Tree := (split 29 (2,true) 6 #[
(.side 0 30 true (-2)),
(.side 0 30 true (-2)),
(.side 26 5 true (4)),
(.side 24 20 true (2)),
(.side 15 15 true (1)),
(.side 15 15 true (1)),
(.side 13 19 true (1)),
(.side 1 29 true (-2)),
(.side 11 37 true (-1)),
(.side 0 31 true (-2)),
(.side 11 35 true (-1)),
(.side 16 14 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.side 26 6 true (4)),
(.side 13 19 true (1)),
(.side 18 12 true (1)),
(.last 37 (5,true)),
(.side 27 3 true (4)),
(.last 37 (5,true)),
(.last 31 (5,true)),
(.side 0 32 true (-2)),
(.side 0 32 true (-2)),
(.side 28 2 true (4)),
(.side 24 22 true (2))])
theorem checked_22_9 : check 162 p_22_9 cert_22_9 = true := by decide +kernel
theorem safe_22_9 : ∀ m, compatible p_22_9 m → WeightedBound 162 m := sound 162 _ cert_22_9 (by decide) checked_22_9
def p_22_10 := refine p_22 (5,false) (some ⟨true,false,2⟩)
def cert_22_10 : Tree := (split 32 (2,true) 6 #[
(.side 11 33 true (-1)),
(.side 11 62 true (-1)),
(.side 11 31 true (-1)),
(.side 11 58 true (-1)),
(.side 122 82 true (0)),
(.side 11 62 true (-1)),
(.side 24 9 true (2)),
(.side 13 24 true (1)),
(.side 33 26 false (3)),
(.side 11 45 true (-1)),
(.side 40 6 false (0)),
(.side 11 62 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.side 11 33 true (-1)),
(.side 11 29 true (-1)),
(.side 11 31 true (-1)),
(.side 14 22 true (1)),
(.side 14 19 true (1)),
(.side 12 21 true (0)),
(.side 11 43 true (-1)),
(.last 33 (5,true)),
(.last 33 (5,true)),
(.last 33 (5,true)),
(.last 33 (5,true))])
theorem checked_22_10 : check 162 p_22_10 cert_22_10 = true := by decide +kernel
theorem safe_22_10 : ∀ m, compatible p_22_10 m → WeightedBound 162 m := sound 162 _ cert_22_10 (by decide) checked_22_10
def p_22_11 := refine p_22 (5,false) (some ⟨true,true,2⟩)
def cert_22_11 : Tree := (split 29 (2,true) 6 #[
(.side 17 13 true (1)),
(.side 11 36 true (-1)),
(.side 19 11 true (1)),
(.side 11 34 true (-1)),
(.side 26 4 true (4)),
(.side 24 21 true (2)),
(.side 13 17 true (1)),
(.side 24 19 true (2)),
(.side 0 54 true (-2)),
(.side 24 21 true (2)),
(.side 42 6 false (0)),
(.side 2 28 true (-2)),
(.side 13 20 true (1)),
(.side 26 6 true (4)),
(.side 21 9 true (1)),
(.side 4 26 true (-2)),
(.side 14 16 true (1)),
(.side 27 3 true (4)),
(.side 25 5 true (3)),
(.last 31 (5,true)),
(.last 30 (5,true)),
(.side 24 21 true (2)),
(.last 30 (5,true)),
(.side 24 19 true (2))])
theorem checked_22_11 : check 162 p_22_11 cert_22_11 = true := by decide +kernel
theorem safe_22_11 : ∀ m, compatible p_22_11 m → WeightedBound 162 m := sound 162 _ cert_22_11 (by decide) checked_22_11
def p_22_12 := refine p_22 (5,false) (some ⟨false,false,3⟩)
def cert_22_12 : Tree := (split 58 (2,true) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.side 40 34 false (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.side 61 17 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.side 53 69 true (-3)),
(.side 70 6 false (-2)),
(.side 76 30 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.side 12 47 true (-4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),.empty]⟩),
(.side 53 173 true (-3)),
(.last 59 (5,true)),
(.last 59 (5,true)),
(.last 59 (5,true)),
(.last 59 (5,true))])
theorem checked_22_12 : check 162 p_22_12 cert_22_12 = true := by decide +kernel
theorem safe_22_12 : ∀ m, compatible p_22_12 m → WeightedBound 162 m := sound 162 _ cert_22_12 (by decide) checked_22_12
def p_22_13 := refine p_22 (5,false) (some ⟨false,true,3⟩)
def cert_22_13 : Tree := (.side 13 19 true (1))
theorem checked_22_13 : check 162 p_22_13 cert_22_13 = true := by decide +kernel
theorem safe_22_13 : ∀ m, compatible p_22_13 m → WeightedBound 162 m := sound 162 _ cert_22_13 (by decide) checked_22_13
def p_22_14 := refine p_22 (5,false) (some ⟨true,false,3⟩)
def cert_22_14 : Tree := (.side 22 7 true (1))
theorem checked_22_14 : check 162 p_22_14 cert_22_14 = true := by decide +kernel
theorem safe_22_14 : ∀ m, compatible p_22_14 m → WeightedBound 162 m := sound 162 _ cert_22_14 (by decide) checked_22_14
def p_22_15 := refine p_22 (5,false) (some ⟨true,true,3⟩)
def cert_22_15 : Tree := (.side 20 9 true (1))
theorem checked_22_15 : check 162 p_22_15 cert_22_15 = true := by decide +kernel
theorem safe_22_15 : ∀ m, compatible p_22_15 m → WeightedBound 162 m := sound 162 _ cert_22_15 (by decide) checked_22_15
def p_22_16 := refine p_22 (5,false) (some ⟨false,false,4⟩)
def cert_22_16 : Tree := (split 33 (2,true) 6 #[
(.side 86 17 false (0)),
(.side 11 47 true (-1)),
(.side 80 15 false (0)),
(.side 162 43 false (6)),
(.last 40 (5,true)),
(.automata ⟨⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,5),(true,1),(true,3),(true,4)],[(false,2),(false,5),(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2),(true,6)],[(false,5)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))) .empty)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty))) .empty)),.empty]⟩),
(.side 13 25 true (1)),
(.automata ⟨⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,5),(true,1),(true,3),(true,4)],[(false,2),(false,5),(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf))),.empty]⟩),
(.side 7 55 true (-4)),
(.automata ⟨⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,5),(true,1),(true,3),(true,4)],[(false,2),(false,5),(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf))),.empty]⟩),
(.side 66 6 false (-2)),
(.side 102 23 false (2)),
(.side 7 37 true (-2)),
(.side 13 23 true (1)),
(.side 74 13 false (0)),
(.side 96 21 false (2)),
(.side 7 33 true (-2)),
(.side 14 25 true (1)),
(.side 47 2 false (1)),
(.last 35 (5,true)),
(.last 34 (5,true)),
(.last 36 (5,true)),
(.last 34 (5,true)),
(.automata ⟨⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,5),(true,1),(true,3),(true,4)],[(false,2),(false,5),(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2),(true,6)],[(false,5)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))) .empty)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty))) .empty)),.empty]⟩)])
theorem checked_22_16 : check 162 p_22_16 cert_22_16 = true := by decide +kernel
theorem safe_22_16 : ∀ m, compatible p_22_16 m → WeightedBound 162 m := sound 162 _ cert_22_16 (by decide) checked_22_16
def p_22_17 := refine p_22 (5,false) (some ⟨false,true,4⟩)
def cert_22_17 : Tree := (.side 14 15 true (1))
theorem checked_22_17 : check 162 p_22_17 cert_22_17 = true := by decide +kernel
theorem safe_22_17 : ∀ m, compatible p_22_17 m → WeightedBound 162 m := sound 162 _ cert_22_17 (by decide) checked_22_17
def p_22_18 := refine p_22 (5,false) (some ⟨true,false,4⟩)
def cert_22_18 : Tree := (.side 11 21 true (-1))
theorem checked_22_18 : check 162 p_22_18 cert_22_18 = true := by decide +kernel
theorem safe_22_18 : ∀ m, compatible p_22_18 m → WeightedBound 162 m := sound 162 _ cert_22_18 (by decide) checked_22_18
def p_22_19 := refine p_22 (5,false) (some ⟨true,true,4⟩)
def cert_22_19 : Tree := (.side 24 21 true (2))
theorem checked_22_19 : check 162 p_22_19 cert_22_19 = true := by decide +kernel
theorem safe_22_19 : ∀ m, compatible p_22_19 m → WeightedBound 162 m := sound 162 _ cert_22_19 (by decide) checked_22_19
def p_22_20 := refine p_22 (5,false) (some ⟨false,false,5⟩)
def cert_22_20 : Tree := (split 31 (5,true) 6 #[
(.side 7 51 true (-4)),
(.side 7 68 true (-2)),
(.side 53 5 false (-3)),
(.side 11 35 true (-1)),
(.side 53 17 false (-1)),
(.side 87 17 false (-1)),
(.last 33 (2,true)),
(.last 47 (2,true)),
(.side 0 58 false (5)),
(.last 49 (2,true)),
(.last 35 (2,true)),
(.last 75 (2,true)),
(.side 89 6 false (-5)),
(.last 43 (2,true)),
(.side 7 46 false (5)),
(.last 71 (2,true)),
(.side 36 1 false (-4)),
(.side 38 1 false (-2)),
(.side 36 1 false (-4)),
(.side 11 39 true (-1)),
(.side 35 1 false (-3)),
(.side 37 1 false (-1)),
(.side 35 1 false (-3)),
(.side 30 2 true (1))])
theorem checked_22_20 : check 162 p_22_20 cert_22_20 = true := by decide +kernel
theorem safe_22_20 : ∀ m, compatible p_22_20 m → WeightedBound 162 m := sound 162 _ cert_22_20 (by decide) checked_22_20
def p_22_21 := refine p_22 (5,false) (some ⟨false,true,5⟩)
def cert_22_21 : Tree := (split 29 (5,true) 6 #[
(.side 0 30 true (-2)),
(.side 0 30 true (-2)),
(.side 26 5 true (4)),
(.side 24 20 true (2)),
(.side 15 15 true (1)),
(.side 15 15 true (1)),
(.last 31 (2,true)),
(.side 1 29 true (-2)),
(.side 11 37 true (-1)),
(.side 0 31 true (-2)),
(.last 33 (2,true)),
(.side 16 14 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch .empty (.branch (.branch (.branch .empty .leaf) .leaf) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)]⟩),
(.side 26 6 true (4)),
(.side 13 19 true (1)),
(.side 18 12 true (1)),
(.side 42 3 false (-2)),
(.side 27 3 true (4)),
(.side 42 3 false (-2)),
(.side 24 24 true (2)),
(.side 30 1 true (4)),
(.side 30 1 true (6)),
(.side 28 2 true (4)),
(.side 30 1 true (6))])
theorem checked_22_21 : check 162 p_22_21 cert_22_21 = true := by decide +kernel
theorem safe_22_21 : ∀ m, compatible p_22_21 m → WeightedBound 162 m := sound 162 _ cert_22_21 (by decide) checked_22_21
def p_22_22 := refine p_22 (5,false) (some ⟨true,false,5⟩)
def cert_22_22 : Tree := (split 31 (5,true) 6 #[
(.last 34 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.side 11 29 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.side 11 21 true (-1)),
(.last 33 (2,true)),
(.side 11 21 true (-1)),
(.side 83 37 true (-1)),
(.last 32 (2,true)),
(.last 35 (2,true)),
(.last 32 (2,true)),
(.last 44 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.side 11 25 true (-1)),
(.side 11 27 true (-1)),
(.side 36 1 false (-4)),
(.side 54 1 false (6)),
(.side 36 1 false (-4)),
(.side 11 32 true (-1)),
(.side 35 1 false (-3)),
(.side 53 1 false (7)),
(.side 35 1 false (-3)),
(.side 34 3 true (4))])
theorem checked_22_22 : check 162 p_22_22 cert_22_22 = true := by decide +kernel
theorem safe_22_22 : ∀ m, compatible p_22_22 m → WeightedBound 162 m := sound 162 _ cert_22_22 (by decide) checked_22_22
def p_22_23 := refine p_22 (5,false) (some ⟨true,true,5⟩)
def cert_22_23 : Tree := (split 29 (5,true) 6 #[
(.side 17 13 true (1)),
(.side 11 36 true (-1)),
(.side 19 11 true (1)),
(.side 11 34 true (-1)),
(.side 26 4 true (4)),
(.side 24 21 true (2)),
(.side 13 17 true (1)),
(.side 24 19 true (2)),
(.last 30 (2,true)),
(.side 24 21 true (2)),
(.last 30 (2,true)),
(.side 2 28 true (-2)),
(.side 13 20 true (1)),
(.side 26 6 true (4)),
(.side 21 9 true (1)),
(.side 4 26 true (-2)),
(.side 14 16 true (1)),
(.side 27 3 true (4)),
(.side 25 5 true (3)),
(.side 11 38 true (-1)),
(.side 31 1 true (3)),
(.side 30 1 true (6)),
(.side 43 3 false (-1)),
(.side 30 1 true (6))])
theorem checked_22_23 : check 162 p_22_23 cert_22_23 = true := by decide +kernel
theorem safe_22_23 : ∀ m, compatible p_22_23 m → WeightedBound 162 m := sound 162 _ cert_22_23 (by decide) checked_22_23
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 162 m := by
  apply split_safe 162 p_22 28 (5,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_22_0 | exact safe_22_1 | exact safe_22_2 | exact safe_22_3 | exact safe_22_4 | exact safe_22_5 | exact safe_22_6 | exact safe_22_7 | exact safe_22_8 | exact safe_22_9 | exact safe_22_10 | exact safe_22_11 | exact safe_22_12 | exact safe_22_13 | exact safe_22_14 | exact safe_22_15 | exact safe_22_16 | exact safe_22_17 | exact safe_22_18 | exact safe_22_19 | exact safe_22_20 | exact safe_22_21 | exact safe_22_22 | exact safe_22_23 | omega
def p_23 := refine parent (4,false) (some ⟨true,true,5⟩)
def p_23_0 := refine p_23 (5,false) (some ⟨false,false,0⟩)
def cert_23_0 : Tree := (.side 17 12 true (1))
theorem checked_23_0 : check 162 p_23_0 cert_23_0 = true := by decide +kernel
theorem safe_23_0 : ∀ m, compatible p_23_0 m → WeightedBound 162 m := sound 162 _ cert_23_0 (by decide) checked_23_0
def p_23_1 := refine p_23 (5,false) (some ⟨false,true,0⟩)
def cert_23_1 : Tree := (.side 11 35 true (-1))
theorem checked_23_1 : check 162 p_23_1 cert_23_1 = true := by decide +kernel
theorem safe_23_1 : ∀ m, compatible p_23_1 m → WeightedBound 162 m := sound 162 _ cert_23_1 (by decide) checked_23_1
def p_23_2 := refine p_23 (5,false) (some ⟨true,false,0⟩)
def cert_23_2 : Tree := (.side 19 10 true (1))
theorem checked_23_2 : check 162 p_23_2 cert_23_2 = true := by decide +kernel
theorem safe_23_2 : ∀ m, compatible p_23_2 m → WeightedBound 162 m := sound 162 _ cert_23_2 (by decide) checked_23_2
def p_23_3 := refine p_23 (5,false) (some ⟨true,true,0⟩)
def cert_23_3 : Tree := (.side 11 33 true (-1))
theorem checked_23_3 : check 162 p_23_3 cert_23_3 = true := by decide +kernel
theorem safe_23_3 : ∀ m, compatible p_23_3 m → WeightedBound 162 m := sound 162 _ cert_23_3 (by decide) checked_23_3
def p_23_4 := refine p_23 (5,false) (some ⟨false,false,1⟩)
def cert_23_4 : Tree := (.side 26 3 true (4))
theorem checked_23_4 : check 162 p_23_4 cert_23_4 = true := by decide +kernel
theorem safe_23_4 : ∀ m, compatible p_23_4 m → WeightedBound 162 m := sound 162 _ cert_23_4 (by decide) checked_23_4
def p_23_5 := refine p_23 (5,false) (some ⟨false,true,1⟩)
def cert_23_5 : Tree := (.side 24 20 true (2))
theorem checked_23_5 : check 162 p_23_5 cert_23_5 = true := by decide +kernel
theorem safe_23_5 : ∀ m, compatible p_23_5 m → WeightedBound 162 m := sound 162 _ cert_23_5 (by decide) checked_23_5
def p_23_6 := refine p_23 (5,false) (some ⟨true,false,1⟩)
def cert_23_6 : Tree := (.side 13 16 true (1))
theorem checked_23_6 : check 162 p_23_6 cert_23_6 = true := by decide +kernel
theorem safe_23_6 : ∀ m, compatible p_23_6 m → WeightedBound 162 m := sound 162 _ cert_23_6 (by decide) checked_23_6
def p_23_7 := refine p_23 (5,false) (some ⟨true,true,1⟩)
def cert_23_7 : Tree := (.side 24 18 true (2))
theorem checked_23_7 : check 162 p_23_7 cert_23_7 = true := by decide +kernel
theorem safe_23_7 : ∀ m, compatible p_23_7 m → WeightedBound 162 m := sound 162 _ cert_23_7 (by decide) checked_23_7
def p_23_8 := refine p_23 (5,false) (some ⟨false,false,2⟩)
def cert_23_8 : Tree := (split 29 (2,true) 6 #[
(.side 0 30 true (-2)),
(.side 0 30 true (-2)),
(.side 26 5 true (4)),
(.side 24 20 true (2)),
(.side 15 15 true (1)),
(.side 15 15 true (1)),
(.side 13 19 true (1)),
(.side 1 29 true (-2)),
(.side 11 37 true (-1)),
(.side 0 31 true (-2)),
(.side 11 35 true (-1)),
(.side 16 14 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),.empty]⟩),
(.side 26 6 true (4)),
(.side 13 19 true (1)),
(.side 18 12 true (1)),
(.side 114 25 false (1)),
(.side 27 3 true (5)),
(.last 31 (5,true)),
(.side 27 3 true (5)),
(.side 0 54 true (-2)),
(.side 0 32 true (-2)),
(.side 11 35 true (-1)),
(.side 28 2 true (5))])
theorem checked_23_8 : check 162 p_23_8 cert_23_8 = true := by decide +kernel
theorem safe_23_8 : ∀ m, compatible p_23_8 m → WeightedBound 162 m := sound 162 _ cert_23_8 (by decide) checked_23_8
def p_23_9 := refine p_23 (5,false) (some ⟨false,true,2⟩)
def cert_23_9 : Tree := (.side 24 20 true (2))
theorem checked_23_9 : check 162 p_23_9 cert_23_9 = true := by decide +kernel
theorem safe_23_9 : ∀ m, compatible p_23_9 m → WeightedBound 162 m := sound 162 _ cert_23_9 (by decide) checked_23_9
def p_23_10 := refine p_23 (5,false) (some ⟨true,false,2⟩)
def cert_23_10 : Tree := (split 29 (2,true) 6 #[
(.side 3 30 true (-2)),
(.side 17 13 true (1)),
(.side 13 18 true (1)),
(.side 3 27 true (-2)),
(.side 7 28 true (-2)),
(.side 26 4 true (4)),
(.side 24 8 true (2)),
(.side 26 4 true (4)),
(.side 48 20 true (2)),
(.side 0 32 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),.empty]⟩),
(.side 2 29 true (-2)),
(.last 34 (5,true)),
(.side 13 20 true (1)),
(.side 22 8 true (1)),
(.side 20 10 true (1)),
(.side 14 37 true (1)),
(.side 14 16 true (1)),
(.last 31 (5,true)),
(.side 24 22 true (2)),
(.last 35 (5,true)),
(.last 30 (5,true)),
(.last 35 (5,true)),
(.last 30 (5,true))])
theorem checked_23_10 : check 162 p_23_10 cert_23_10 = true := by decide +kernel
theorem safe_23_10 : ∀ m, compatible p_23_10 m → WeightedBound 162 m := sound 162 _ cert_23_10 (by decide) checked_23_10
def p_23_11 := refine p_23 (5,false) (some ⟨true,true,2⟩)
def cert_23_11 : Tree := (.side 2 27 true (-2))
theorem checked_23_11 : check 162 p_23_11 cert_23_11 = true := by decide +kernel
theorem safe_23_11 : ∀ m, compatible p_23_11 m → WeightedBound 162 m := sound 162 _ cert_23_11 (by decide) checked_23_11
def p_23_12 := refine p_23 (5,false) (some ⟨false,false,3⟩)
def cert_23_12 : Tree := (.side 13 19 true (1))
theorem checked_23_12 : check 162 p_23_12 cert_23_12 = true := by decide +kernel
theorem safe_23_12 : ∀ m, compatible p_23_12 m → WeightedBound 162 m := sound 162 _ cert_23_12 (by decide) checked_23_12
def p_23_13 := refine p_23 (5,false) (some ⟨false,true,3⟩)
def cert_23_13 : Tree := (.side 26 5 true (4))
theorem checked_23_13 : check 162 p_23_13 cert_23_13 = true := by decide +kernel
theorem safe_23_13 : ∀ m, compatible p_23_13 m → WeightedBound 162 m := sound 162 _ cert_23_13 (by decide) checked_23_13
def p_23_14 := refine p_23 (5,false) (some ⟨true,false,3⟩)
def cert_23_14 : Tree := (.side 21 8 true (1))
theorem checked_23_14 : check 162 p_23_14 cert_23_14 = true := by decide +kernel
theorem safe_23_14 : ∀ m, compatible p_23_14 m → WeightedBound 162 m := sound 162 _ cert_23_14 (by decide) checked_23_14
def p_23_15 := refine p_23 (5,false) (some ⟨true,true,3⟩)
def cert_23_15 : Tree := (.side 4 25 true (-2))
theorem checked_23_15 : check 162 p_23_15 cert_23_15 = true := by decide +kernel
theorem safe_23_15 : ∀ m, compatible p_23_15 m → WeightedBound 162 m := sound 162 _ cert_23_15 (by decide) checked_23_15
def p_23_16 := refine p_23 (5,false) (some ⟨false,false,4⟩)
def cert_23_16 : Tree := (.side 14 15 true (1))
theorem checked_23_16 : check 162 p_23_16 cert_23_16 = true := by decide +kernel
theorem safe_23_16 : ∀ m, compatible p_23_16 m → WeightedBound 162 m := sound 162 _ cert_23_16 (by decide) checked_23_16
def p_23_17 := refine p_23 (5,false) (some ⟨false,true,4⟩)
def cert_23_17 : Tree := (.side 27 2 true (5))
theorem checked_23_17 : check 162 p_23_17 cert_23_17 = true := by decide +kernel
theorem safe_23_17 : ∀ m, compatible p_23_17 m → WeightedBound 162 m := sound 162 _ cert_23_17 (by decide) checked_23_17
def p_23_18 := refine p_23 (5,false) (some ⟨true,false,4⟩)
def cert_23_18 : Tree := (.side 25 4 true (3))
theorem checked_23_18 : check 162 p_23_18 cert_23_18 = true := by decide +kernel
theorem safe_23_18 : ∀ m, compatible p_23_18 m → WeightedBound 162 m := sound 162 _ cert_23_18 (by decide) checked_23_18
def p_23_19 := refine p_23 (5,false) (some ⟨true,true,4⟩)
def cert_23_19 : Tree := (.side 27 2 true (5))
theorem checked_23_19 : check 162 p_23_19 cert_23_19 = true := by decide +kernel
theorem safe_23_19 : ∀ m, compatible p_23_19 m → WeightedBound 162 m := sound 162 _ cert_23_19 (by decide) checked_23_19
def p_23_20 := refine p_23 (5,false) (some ⟨false,false,5⟩)
def cert_23_20 : Tree := (split 29 (5,true) 6 #[
(.side 0 30 true (-2)),
(.side 0 30 true (-2)),
(.side 26 5 true (4)),
(.side 24 20 true (2)),
(.side 15 15 true (1)),
(.side 15 15 true (1)),
(.last 31 (2,true)),
(.side 1 29 true (-2)),
(.side 11 37 true (-1)),
(.side 0 31 true (-2)),
(.last 33 (2,true)),
(.side 16 14 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))]⟩),
(.side 26 6 true (4)),
(.side 13 19 true (1)),
(.side 18 12 true (1)),
(.side 114 25 false (1)),
(.side 27 3 true (5)),
(.side 25 7 true (3)),
(.side 27 3 true (5)),
(.side 37 1 false (-3)),
(.side 41 1 false (-1)),
(.side 37 1 false (-3)),
(.side 28 2 true (5))])
theorem checked_23_20 : check 162 p_23_20 cert_23_20 = true := by decide +kernel
theorem safe_23_20 : ∀ m, compatible p_23_20 m → WeightedBound 162 m := sound 162 _ cert_23_20 (by decide) checked_23_20
def p_23_21 := refine p_23 (5,false) (some ⟨false,true,5⟩)
def cert_23_21 : Tree := (.side 28 1 true (6))
theorem checked_23_21 : check 162 p_23_21 cert_23_21 = true := by decide +kernel
theorem safe_23_21 : ∀ m, compatible p_23_21 m → WeightedBound 162 m := sound 162 _ cert_23_21 (by decide) checked_23_21
def p_23_22 := refine p_23 (5,false) (some ⟨true,false,5⟩)
def cert_23_22 : Tree := (split 29 (5,true) 6 #[
(.last 32 (2,true)),
(.side 17 13 true (1)),
(.side 13 18 true (1)),
(.side 3 27 true (-2)),
(.side 7 28 true (-2)),
(.side 26 4 true (4)),
(.last 31 (2,true)),
(.side 26 4 true (4)),
(.side 48 20 true (2)),
(.last 30 (2,true)),
(.last 33 (2,true)),
(.last 30 (2,true)),
(.side 11 37 true (-1)),
(.side 13 20 true (1)),
(.side 22 8 true (1)),
(.side 20 10 true (1)),
(.last 41 (2,true)),
(.side 14 16 true (1)),
(.side 12 20 true (0)),
(.side 24 22 true (2)),
(.side 37 1 false (-3)),
(.side 65 1 false (9)),
(.side 37 1 false (-3)),
(.side 28 3 true (5))])
theorem checked_23_22 : check 162 p_23_22 cert_23_22 = true := by decide +kernel
theorem safe_23_22 : ∀ m, compatible p_23_22 m → WeightedBound 162 m := sound 162 _ cert_23_22 (by decide) checked_23_22
def p_23_23 := refine p_23 (5,false) (some ⟨true,true,5⟩)
def cert_23_23 : Tree := (.side 28 1 true (6))
theorem checked_23_23 : check 162 p_23_23 cert_23_23 = true := by decide +kernel
theorem safe_23_23 : ∀ m, compatible p_23_23 m → WeightedBound 162 m := sound 162 _ cert_23_23 (by decide) checked_23_23
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 162 m := by
  apply split_safe 162 p_23 28 (5,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_23_0 | exact safe_23_1 | exact safe_23_2 | exact safe_23_3 | exact safe_23_4 | exact safe_23_5 | exact safe_23_6 | exact safe_23_7 | exact safe_23_8 | exact safe_23_9 | exact safe_23_10 | exact safe_23_11 | exact safe_23_12 | exact safe_23_13 | exact safe_23_14 | exact safe_23_15 | exact safe_23_16 | exact safe_23_17 | exact safe_23_18 | exact safe_23_19 | exact safe_23_20 | exact safe_23_21 | exact safe_23_22 | exact safe_23_23 | omega
theorem safe : ∀ m, compatible parent m → WeightedBound 162 m := by
  apply split_safe 162 parent 27 (4,false) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23 | omega
theorem cover : Cover (WeightedBound 162) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Root33
