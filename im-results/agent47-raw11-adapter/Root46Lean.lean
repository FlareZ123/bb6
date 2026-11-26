import PhaseTree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent47Root46
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨true,false,4⟩)
  | _,_ => none)
def p_0 := refine parent (4,false) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.side 7 10 false (1))
theorem checked_0 : check 64 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 64 m := sound 64 _ cert_0 (by decide) checked_0
def p_1 := refine parent (4,false) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 7 12 false (1))
theorem checked_1 : check 64 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 64 m := sound 64 _ cert_1 (by decide) checked_1
def p_2 := refine parent (4,false) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 7 8 false (1))
theorem checked_2 : check 64 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 64 m := sound 64 _ cert_2 (by decide) checked_2
def p_3 := refine parent (4,false) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 6 10 false (2))
theorem checked_3 : check 64 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 64 m := sound 64 _ cert_3 (by decide) checked_3
def p_4 := refine parent (4,false) (some ⟨false,false,1⟩)
def cert_4 : Tree := (.side 7 14 false (1))
theorem checked_4 : check 64 p_4 cert_4 = true := by decide +kernel
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 64 m := sound 64 _ cert_4 (by decide) checked_4
def p_5 := refine parent (4,false) (some ⟨false,true,1⟩)
def cert_5 : Tree := (.side 14 17 true (0))
theorem checked_5 : check 64 p_5 cert_5 = true := by decide +kernel
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 64 m := sound 64 _ cert_5 (by decide) checked_5
def p_6 := refine parent (4,false) (some ⟨true,false,1⟩)
def p_6_0 := refine p_6 (2,true) (some ⟨false,false,0⟩)
def cert_6_0 : Tree := (.side 7 15 false (1))
theorem checked_6_0 : check 64 p_6_0 cert_6_0 = true := by decide +kernel
theorem safe_6_0 : ∀ m, compatible p_6_0 m → WeightedBound 64 m := sound 64 _ cert_6_0 (by decide) checked_6_0
def p_6_1 := refine p_6 (2,true) (some ⟨false,true,0⟩)
def cert_6_1 : Tree := (.side 7 17 false (1))
theorem checked_6_1 : check 64 p_6_1 cert_6_1 = true := by decide +kernel
theorem safe_6_1 : ∀ m, compatible p_6_1 m → WeightedBound 64 m := sound 64 _ cert_6_1 (by decide) checked_6_1
def p_6_2 := refine p_6 (2,true) (some ⟨true,false,0⟩)
def cert_6_2 : Tree := (.side 7 13 false (1))
theorem checked_6_2 : check 64 p_6_2 cert_6_2 = true := by decide +kernel
theorem safe_6_2 : ∀ m, compatible p_6_2 m → WeightedBound 64 m := sound 64 _ cert_6_2 (by decide) checked_6_2
def p_6_3 := refine p_6 (2,true) (some ⟨true,true,0⟩)
def cert_6_3 : Tree := (.side 6 15 false (2))
theorem checked_6_3 : check 64 p_6_3 cert_6_3 = true := by decide +kernel
theorem safe_6_3 : ∀ m, compatible p_6_3 m → WeightedBound 64 m := sound 64 _ cert_6_3 (by decide) checked_6_3
def p_6_4 := refine p_6 (2,true) (some ⟨false,false,1⟩)
def cert_6_4 : Tree := (.side 16 4 true (-3))
theorem checked_6_4 : check 64 p_6_4 cert_6_4 = true := by decide +kernel
theorem safe_6_4 : ∀ m, compatible p_6_4 m → WeightedBound 64 m := sound 64 _ cert_6_4 (by decide) checked_6_4
def p_6_5 := refine p_6 (2,true) (some ⟨false,true,1⟩)
def cert_6_5 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_6_5 : check 64 p_6_5 cert_6_5 = true := by decide +kernel
theorem safe_6_5 : ∀ m, compatible p_6_5 m → WeightedBound 64 m := sound 64 _ cert_6_5 (by decide) checked_6_5
def p_6_6 := refine p_6 (2,true) (some ⟨true,false,1⟩)
def cert_6_6 : Tree := (.side 14 5 false (-1))
theorem checked_6_6 : check 64 p_6_6 cert_6_6 = true := by decide +kernel
theorem safe_6_6 : ∀ m, compatible p_6_6 m → WeightedBound 64 m := sound 64 _ cert_6_6 (by decide) checked_6_6
def p_6_7 := refine p_6 (2,true) (some ⟨true,true,1⟩)
def cert_6_7 : Tree := (.side 11 11 false (0))
theorem checked_6_7 : check 64 p_6_7 cert_6_7 = true := by decide +kernel
theorem safe_6_7 : ∀ m, compatible p_6_7 m → WeightedBound 64 m := sound 64 _ cert_6_7 (by decide) checked_6_7
def p_6_8 := refine p_6 (2,true) (some ⟨false,false,2⟩)
def cert_6_8 : Tree := (.side 0 21 false (2))
theorem checked_6_8 : check 64 p_6_8 cert_6_8 = true := by decide +kernel
theorem safe_6_8 : ∀ m, compatible p_6_8 m → WeightedBound 64 m := sound 64 _ cert_6_8 (by decide) checked_6_8
def p_6_9 := refine p_6 (2,true) (some ⟨false,true,2⟩)
def cert_6_9 : Tree := (.side 0 24 true (-3))
theorem checked_6_9 : check 64 p_6_9 cert_6_9 = true := by decide +kernel
theorem safe_6_9 : ∀ m, compatible p_6_9 m → WeightedBound 64 m := sound 64 _ cert_6_9 (by decide) checked_6_9
def p_6_10 := refine p_6 (2,true) (some ⟨true,false,2⟩)
def cert_6_10 : Tree := (.side 18 6 false (-2))
theorem checked_6_10 : check 64 p_6_10 cert_6_10 = true := by decide +kernel
theorem safe_6_10 : ∀ m, compatible p_6_10 m → WeightedBound 64 m := sound 64 _ cert_6_10 (by decide) checked_6_10
def p_6_11 := refine p_6 (2,true) (some ⟨true,true,2⟩)
def cert_6_11 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .leaf),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_6_11 : check 64 p_6_11 cert_6_11 = true := by decide +kernel
theorem safe_6_11 : ∀ m, compatible p_6_11 m → WeightedBound 64 m := sound 64 _ cert_6_11 (by decide) checked_6_11
def p_6_12 := refine p_6 (2,true) (some ⟨false,false,3⟩)
def cert_6_12 : Tree := (.side 8 11 false (0))
theorem checked_6_12 : check 64 p_6_12 cert_6_12 = true := by decide +kernel
theorem safe_6_12 : ∀ m, compatible p_6_12 m → WeightedBound 64 m := sound 64 _ cert_6_12 (by decide) checked_6_12
def p_6_13 := refine p_6 (2,true) (some ⟨false,true,3⟩)
def cert_6_13 : Tree := (.side 7 15 false (1))
theorem checked_6_13 : check 64 p_6_13 cert_6_13 = true := by decide +kernel
theorem safe_6_13 : ∀ m, compatible p_6_13 m → WeightedBound 64 m := sound 64 _ cert_6_13 (by decide) checked_6_13
def p_6_14 := refine p_6 (2,true) (some ⟨true,false,3⟩)
def cert_6_14 : Tree := (.side 8 11 false (0))
theorem checked_6_14 : check 64 p_6_14 cert_6_14 = true := by decide +kernel
theorem safe_6_14 : ∀ m, compatible p_6_14 m → WeightedBound 64 m := sound 64 _ cert_6_14 (by decide) checked_6_14
def p_6_15 := refine p_6 (2,true) (some ⟨true,true,3⟩)
def cert_6_15 : Tree := (.side 6 13 false (2))
theorem checked_6_15 : check 64 p_6_15 cert_6_15 = true := by decide +kernel
theorem safe_6_15 : ∀ m, compatible p_6_15 m → WeightedBound 64 m := sound 64 _ cert_6_15 (by decide) checked_6_15
def p_6_16 := refine p_6 (2,true) (some ⟨false,false,4⟩)
def cert_6_16 : Tree := (.side 15 4 false (-1))
theorem checked_6_16 : check 64 p_6_16 cert_6_16 = true := by decide +kernel
theorem safe_6_16 : ∀ m, compatible p_6_16 m → WeightedBound 64 m := sound 64 _ cert_6_16 (by decide) checked_6_16
def p_6_17 := refine p_6 (2,true) (some ⟨false,true,4⟩)
def cert_6_17 : Tree := (.side 12 7 false (0))
theorem checked_6_17 : check 64 p_6_17 cert_6_17 = true := by decide +kernel
theorem safe_6_17 : ∀ m, compatible p_6_17 m → WeightedBound 64 m := sound 64 _ cert_6_17 (by decide) checked_6_17
def p_6_18 := refine p_6 (2,true) (some ⟨true,false,4⟩)
def cert_6_18 : Tree := (.side 15 4 false (-1))
theorem checked_6_18 : check 64 p_6_18 cert_6_18 = true := by decide +kernel
theorem safe_6_18 : ∀ m, compatible p_6_18 m → WeightedBound 64 m := sound 64 _ cert_6_18 (by decide) checked_6_18
def p_6_19 := refine p_6 (2,true) (some ⟨true,true,4⟩)
def cert_6_19 : Tree := (.side 15 6 false (-1))
theorem checked_6_19 : check 64 p_6_19 cert_6_19 = true := by decide +kernel
theorem safe_6_19 : ∀ m, compatible p_6_19 m → WeightedBound 64 m := sound 64 _ cert_6_19 (by decide) checked_6_19
def p_6_20 := refine p_6 (2,true) (some ⟨false,false,5⟩)
def cert_6_20 : Tree := (split 19 (5,true) 6 #[
(.side 0 20 false (2)),
(.side 10 10 true (-3)),
(.side 7 20 false (1)),
(.side 11 13 false (0)),
(.side 7 18 false (1)),
(.side 20 27 true (-2)),
(.side 17 3 false (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .leaf),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),.empty,(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 0 21 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .leaf),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),.empty,(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.last 26 (5,false)),
(.side 7 17 false (1)),
(.side 8 19 false (0)),
(.side 9 11 false (0)),
(.side 9 11 false (0)),
(.side 7 15 false (1)),
(.side 16 4 false (-2)),
(.side 16 4 true (-3)),
(.side 16 4 false (-2)),
(.side 13 7 false (-1)),
(.last 20 (5,false)),
(.last 20 (5,false)),
(.last 20 (5,false)),
(.last 20 (5,false))])
theorem checked_6_20 : check 64 p_6_20 cert_6_20 = true := by decide +kernel
theorem safe_6_20 : ∀ m, compatible p_6_20 m → WeightedBound 64 m := sound 64 _ cert_6_20 (by decide) checked_6_20
def p_6_21 := refine p_6 (2,true) (some ⟨false,true,5⟩)
def cert_6_21 : Tree := (split 19 (5,true) 6 #[
(.last 27 (5,false)),
(.side 11 17 false (1)),
(.side 11 13 false (0)),
(.side 7 19 false (1)),
(.side 1 19 false (2)),
(.last 30 (5,false)),
(.last 31 (5,false)),
(.last 42 (5,false)),
(.side 7 17 false (1)),
(.last 23 (5,false)),
(.side 7 17 false (1)),
(.last 23 (5,false)),
(.side 7 15 false (1)),
(.side 11 15 false (0)),
(.side 7 15 false (1)),
(.side 7 17 false (1)),
(.side 13 7 false (-1)),
(.last 38 (5,false)),
(.side 13 7 false (-1)),
(.side 12 9 false (0)),
(.last 20 (5,false)),
(.last 23 (5,false)),
(.last 20 (5,false)),
(.last 23 (5,false))])
theorem checked_6_21 : check 64 p_6_21 cert_6_21 = true := by decide +kernel
theorem safe_6_21 : ∀ m, compatible p_6_21 m → WeightedBound 64 m := sound 64 _ cert_6_21 (by decide) checked_6_21
def p_6_22 := refine p_6 (2,true) (some ⟨true,false,5⟩)
def cert_6_22 : Tree := (split 19 (5,true) 6 #[
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 10 10 false (0)),
(.side 5 15 false (2)),
(.side 7 18 false (1)),
(.side 14 6 true (-3)),
(.side 17 3 false (-2)),
(.side 11 9 false (0)),
(.side 0 21 false (2)),
(.last 21 (5,false)),
(.last 26 (5,false)),
(.side 18 2 true (-3)),
(.side 8 19 false (0)),
(.side 8 12 false (0)),
(.side 9 11 false (0)),
(.side 7 13 false (1)),
(.side 16 4 false (-2)),
(.side 15 5 false (-1)),
(.side 16 4 false (-2)),
(.side 15 6 false (-1)),
(.last 20 (5,false)),
(.last 25 (5,false)),
(.last 20 (5,false)),
(.last 25 (5,false))])
theorem checked_6_22 : check 64 p_6_22 cert_6_22 = true := by decide +kernel
theorem safe_6_22 : ∀ m, compatible p_6_22 m → WeightedBound 64 m := sound 64 _ cert_6_22 (by decide) checked_6_22
def p_6_23 := refine p_6 (2,true) (some ⟨true,true,5⟩)
def cert_6_23 : Tree := (split 19 (5,true) 6 #[
(.side 3 17 false (2)),
(.side 4 19 false (2)),
(.side 5 15 false (2)),
(.side 6 17 false (2)),
(.last 39 (5,false)),
(.last 30 (5,false)),
(.side 11 9 false (0)),
(.side 11 15 false (1)),
(.last 21 (5,false)),
(.last 23 (5,false)),
(.side 18 2 true (-2)),
(.last 23 (5,false)),
(.side 7 13 false (1)),
(.side 4 17 false (2)),
(.side 7 13 false (1)),
(.side 6 15 false (2)),
(.side 15 6 false (-1)),
(.side 11 11 false (0)),
(.side 15 6 false (-1)),
(.side 15 8 false (0)),
(.last 22 (5,false)),
(.last 23 (5,false)),
(.last 22 (5,false)),
(.last 23 (5,false))])
theorem checked_6_23 : check 64 p_6_23 cert_6_23 = true := by decide +kernel
theorem safe_6_23 : ∀ m, compatible p_6_23 m → WeightedBound 64 m := sound 64 _ cert_6_23 (by decide) checked_6_23
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 64 m := by
  apply split_safe 64 p_6 18 (2,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_6_0 | exact safe_6_1 | exact safe_6_2 | exact safe_6_3 | exact safe_6_4 | exact safe_6_5 | exact safe_6_6 | exact safe_6_7 | exact safe_6_8 | exact safe_6_9 | exact safe_6_10 | exact safe_6_11 | exact safe_6_12 | exact safe_6_13 | exact safe_6_14 | exact safe_6_15 | exact safe_6_16 | exact safe_6_17 | exact safe_6_18 | exact safe_6_19 | exact safe_6_20 | exact safe_6_21 | exact safe_6_22 | exact safe_6_23
def p_7 := refine parent (4,false) (some ⟨true,true,1⟩)
def cert_7 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_7 : check 64 p_7 cert_7 = true := by decide +kernel
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 64 m := sound 64 _ cert_7 (by decide) checked_7
def p_8 := refine parent (4,false) (some ⟨false,false,2⟩)
def p_8_0 := refine p_8 (2,true) (some ⟨false,false,0⟩)
def cert_8_0 : Tree := (.side 0 15 false (2))
theorem checked_8_0 : check 64 p_8_0 cert_8_0 = true := by decide +kernel
theorem safe_8_0 : ∀ m, compatible p_8_0 m → WeightedBound 64 m := sound 64 _ cert_8_0 (by decide) checked_8_0
def p_8_1 := refine p_8 (2,true) (some ⟨false,true,0⟩)
def cert_8_1 : Tree := (.side 15 20 true (-1))
theorem checked_8_1 : check 64 p_8_1 cert_8_1 = true := by decide +kernel
theorem safe_8_1 : ∀ m, compatible p_8_1 m → WeightedBound 64 m := sound 64 _ cert_8_1 (by decide) checked_8_1
def p_8_2 := refine p_8 (2,true) (some ⟨true,false,0⟩)
def cert_8_2 : Tree := (.side 7 15 false (1))
theorem checked_8_2 : check 64 p_8_2 cert_8_2 = true := by decide +kernel
theorem safe_8_2 : ∀ m, compatible p_8_2 m → WeightedBound 64 m := sound 64 _ cert_8_2 (by decide) checked_8_2
def p_8_3 := refine p_8 (2,true) (some ⟨true,true,0⟩)
def cert_8_3 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_8_3 : check 64 p_8_3 cert_8_3 = true := by decide +kernel
theorem safe_8_3 : ∀ m, compatible p_8_3 m → WeightedBound 64 m := sound 64 _ cert_8_3 (by decide) checked_8_3
def p_8_4 := refine p_8 (2,true) (some ⟨false,false,1⟩)
def cert_8_4 : Tree := (.side 7 13 false (1))
theorem checked_8_4 : check 64 p_8_4 cert_8_4 = true := by decide +kernel
theorem safe_8_4 : ∀ m, compatible p_8_4 m → WeightedBound 64 m := sound 64 _ cert_8_4 (by decide) checked_8_4
def p_8_5 := refine p_8 (2,true) (some ⟨false,true,1⟩)
def cert_8_5 : Tree := (.side 6 38 false (2))
theorem checked_8_5 : check 64 p_8_5 cert_8_5 = true := by decide +kernel
theorem safe_8_5 : ∀ m, compatible p_8_5 m → WeightedBound 64 m := sound 64 _ cert_8_5 (by decide) checked_8_5
def p_8_6 := refine p_8 (2,true) (some ⟨true,false,1⟩)
def cert_8_6 : Tree := (.side 0 21 false (2))
theorem checked_8_6 : check 64 p_8_6 cert_8_6 = true := by decide +kernel
theorem safe_8_6 : ∀ m, compatible p_8_6 m → WeightedBound 64 m := sound 64 _ cert_8_6 (by decide) checked_8_6
def p_8_7 := refine p_8 (2,true) (some ⟨true,true,1⟩)
def cert_8_7 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_8_7 : check 64 p_8_7 cert_8_7 = true := by decide +kernel
theorem safe_8_7 : ∀ m, compatible p_8_7 m → WeightedBound 64 m := sound 64 _ cert_8_7 (by decide) checked_8_7
def p_8_8 := refine p_8 (2,true) (some ⟨false,false,2⟩)
def cert_8_8 : Tree := (.side 0 16 false (2))
theorem checked_8_8 : check 64 p_8_8 cert_8_8 = true := by decide +kernel
theorem safe_8_8 : ∀ m, compatible p_8_8 m → WeightedBound 64 m := sound 64 _ cert_8_8 (by decide) checked_8_8
def p_8_9 := refine p_8 (2,true) (some ⟨false,true,2⟩)
def cert_8_9 : Tree := (.side 0 22 true (-2))
theorem checked_8_9 : check 64 p_8_9 cert_8_9 = true := by decide +kernel
theorem safe_8_9 : ∀ m, compatible p_8_9 m → WeightedBound 64 m := sound 64 _ cert_8_9 (by decide) checked_8_9
def p_8_10 := refine p_8 (2,true) (some ⟨true,false,2⟩)
def cert_8_10 : Tree := (.side 14 6 false (-2))
theorem checked_8_10 : check 64 p_8_10 cert_8_10 = true := by decide +kernel
theorem safe_8_10 : ∀ m, compatible p_8_10 m → WeightedBound 64 m := sound 64 _ cert_8_10 (by decide) checked_8_10
def p_8_11 := refine p_8 (2,true) (some ⟨true,true,2⟩)
def cert_8_11 : Tree := (.side 7 12 false (1))
theorem checked_8_11 : check 64 p_8_11 cert_8_11 = true := by decide +kernel
theorem safe_8_11 : ∀ m, compatible p_8_11 m → WeightedBound 64 m := sound 64 _ cert_8_11 (by decide) checked_8_11
def p_8_12 := refine p_8 (2,true) (some ⟨false,false,3⟩)
def cert_8_12 : Tree := (.side 7 16 false (1))
theorem checked_8_12 : check 64 p_8_12 cert_8_12 = true := by decide +kernel
theorem safe_8_12 : ∀ m, compatible p_8_12 m → WeightedBound 64 m := sound 64 _ cert_8_12 (by decide) checked_8_12
def p_8_13 := refine p_8 (2,true) (some ⟨false,true,3⟩)
def cert_8_13 : Tree := (.side 9 6 true (-2))
theorem checked_8_13 : check 64 p_8_13 cert_8_13 = true := by decide +kernel
theorem safe_8_13 : ∀ m, compatible p_8_13 m → WeightedBound 64 m := sound 64 _ cert_8_13 (by decide) checked_8_13
def p_8_14 := refine p_8 (2,true) (some ⟨true,false,3⟩)
def cert_8_14 : Tree := (.side 9 6 false (0))
theorem checked_8_14 : check 64 p_8_14 cert_8_14 = true := by decide +kernel
theorem safe_8_14 : ∀ m, compatible p_8_14 m → WeightedBound 64 m := sound 64 _ cert_8_14 (by decide) checked_8_14
def p_8_15 := refine p_8 (2,true) (some ⟨true,true,3⟩)
def cert_8_15 : Tree := (.side 7 10 false (1))
theorem checked_8_15 : check 64 p_8_15 cert_8_15 = true := by decide +kernel
theorem safe_8_15 : ∀ m, compatible p_8_15 m → WeightedBound 64 m := sound 64 _ cert_8_15 (by decide) checked_8_15
def p_8_16 := refine p_8 (2,true) (some ⟨false,false,4⟩)
def cert_8_16 : Tree := (.side 0 17 false (2))
theorem checked_8_16 : check 64 p_8_16 cert_8_16 = true := by decide +kernel
theorem safe_8_16 : ∀ m, compatible p_8_16 m → WeightedBound 64 m := sound 64 _ cert_8_16 (by decide) checked_8_16
def p_8_17 := refine p_8 (2,true) (some ⟨false,true,4⟩)
def cert_8_17 : Tree := (.side 0 17 false (2))
theorem checked_8_17 : check 64 p_8_17 cert_8_17 = true := by decide +kernel
theorem safe_8_17 : ∀ m, compatible p_8_17 m → WeightedBound 64 m := sound 64 _ cert_8_17 (by decide) checked_8_17
def p_8_18 := refine p_8 (2,true) (some ⟨true,false,4⟩)
def cert_8_18 : Tree := (.side 0 17 false (2))
theorem checked_8_18 : check 64 p_8_18 cert_8_18 = true := by decide +kernel
theorem safe_8_18 : ∀ m, compatible p_8_18 m → WeightedBound 64 m := sound 64 _ cert_8_18 (by decide) checked_8_18
def p_8_19 := refine p_8 (2,true) (some ⟨true,true,4⟩)
def cert_8_19 : Tree := (.side 13 2 true (-2))
theorem checked_8_19 : check 64 p_8_19 cert_8_19 = true := by decide +kernel
theorem safe_8_19 : ∀ m, compatible p_8_19 m → WeightedBound 64 m := sound 64 _ cert_8_19 (by decide) checked_8_19
def p_8_20 := refine p_8 (2,true) (some ⟨false,false,5⟩)
def cert_8_20 : Tree := (split 15 (5,false) 6 #[
(.side 0 16 false (2)),
(.last 19 (5,true)),
(.side 7 16 false (1)),
(.last 19 (5,true)),
(.side 7 14 false (1)),
(.side 7 14 false (1)),
(.last 18 (5,true)),
(.side 1 15 false (2)),
(.side 0 17 false (2)),
(.side 0 17 false (2)),
(.last 20 (5,true)),
(.side 7 13 false (1)),
(.side 7 17 false (1)),
(.side 7 17 false (1)),
(.side 9 7 false (0)),
(.side 7 11 false (1)),
(.side 0 18 false (2)),
(.side 0 18 false (2)),
(.side 0 18 false (2)),
(.side 13 3 false (-1)),
(.side 15 1 false (-3)),
(.last 18 (5,true)),
(.side 15 1 false (-3)),
(.last 18 (5,true))])
theorem checked_8_20 : check 64 p_8_20 cert_8_20 = true := by decide +kernel
theorem safe_8_20 : ∀ m, compatible p_8_20 m → WeightedBound 64 m := sound 64 _ cert_8_20 (by decide) checked_8_20
def p_8_21 := refine p_8 (2,true) (some ⟨false,true,5⟩)
def cert_8_21 : Tree := (split 15 (5,false) 6 #[
(.last 19 (5,true)),
(.side 7 10 true (-2)),
(.side 10 6 true (-2)),
(.side 5 11 false (2)),
(.side 7 14 false (1)),
(.side 0 20 false (2)),
(.last 18 (5,true)),
(.side 16 20 true (-1)),
(.side 0 17 false (2)),
(.last 17 (5,true)),
(.last 20 (5,true)),
(.last 17 (5,true)),
(.side 7 17 false (1)),
(.side 8 8 true (-2)),
(.side 9 7 false (0)),
(.side 7 9 false (1)),
(.side 0 18 false (2)),
(.side 0 19 false (2)),
(.side 0 18 false (2)),
(.side 0 20 false (2)),
(.side 15 1 false (-1)),
(.last 16 (5,true)),
(.side 15 1 false (-1)),
(.last 16 (5,true))])
theorem checked_8_21 : check 64 p_8_21 cert_8_21 = true := by decide +kernel
theorem safe_8_21 : ∀ m, compatible p_8_21 m → WeightedBound 64 m := sound 64 _ cert_8_21 (by decide) checked_8_21
def p_8_22 := refine p_8 (2,true) (some ⟨true,false,5⟩)
def cert_8_22 : Tree := (split 15 (5,false) 6 #[
(.last 19 (5,true)),
(.side 7 12 false (1)),
(.side 10 6 false (0)),
(.side 3 13 false (2)),
(.side 7 14 false (1)),
(.side 0 19 false (2)),
(.last 18 (5,true)),
(.side 7 15 false (1)),
(.side 0 17 false (2)),
(.side 14 2 true (-3)),
(.last 20 (5,true)),
(.last 17 (5,true)),
(.side 7 17 false (1)),
(.side 8 8 false (0)),
(.side 9 7 false (0)),
(.side 7 9 false (1)),
(.side 0 18 false (2)),
(.side 0 19 false (2)),
(.side 0 18 false (2)),
(.side 0 20 false (2)),
(.side 15 1 false (-3)),
(.last 16 (5,true)),
(.side 15 1 false (-3)),
(.last 16 (5,true))])
theorem checked_8_22 : check 64 p_8_22 cert_8_22 = true := by decide +kernel
theorem safe_8_22 : ∀ m, compatible p_8_22 m → WeightedBound 64 m := sound 64 _ cert_8_22 (by decide) checked_8_22
def p_8_23 := refine p_8 (2,true) (some ⟨true,true,5⟩)
def cert_8_23 : Tree := (split 15 (5,false) 6 #[
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.side 0 19 false (2)),
(.side 7 16 false (1)),
(.side 0 20 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),.empty]⟩),
(.side 14 2 true (-2)),
(.last 17 (5,true)),
(.last 17 (5,true)),
(.last 17 (5,true)),
(.side 8 8 false (0)),
(.side 7 12 false (1)),
(.side 8 8 false (0)),
(.side 6 10 false (2)),
(.side 0 19 false (2)),
(.side 12 4 true (-2)),
(.side 0 19 false (2)),
(.side 0 21 false (2)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true))])
theorem checked_8_23 : check 64 p_8_23 cert_8_23 = true := by decide +kernel
theorem safe_8_23 : ∀ m, compatible p_8_23 m → WeightedBound 64 m := sound 64 _ cert_8_23 (by decide) checked_8_23
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 64 m := by
  apply split_safe 64 p_8 14 (2,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_8_0 | exact safe_8_1 | exact safe_8_2 | exact safe_8_3 | exact safe_8_4 | exact safe_8_5 | exact safe_8_6 | exact safe_8_7 | exact safe_8_8 | exact safe_8_9 | exact safe_8_10 | exact safe_8_11 | exact safe_8_12 | exact safe_8_13 | exact safe_8_14 | exact safe_8_15 | exact safe_8_16 | exact safe_8_17 | exact safe_8_18 | exact safe_8_19 | exact safe_8_20 | exact safe_8_21 | exact safe_8_22 | exact safe_8_23
def p_9 := refine parent (4,false) (some ⟨false,true,2⟩)
def p_9_0 := refine p_9 (2,true) (some ⟨false,false,0⟩)
def cert_9_0 : Tree := (.side 6 16 false (2))
theorem checked_9_0 : check 64 p_9_0 cert_9_0 = true := by decide +kernel
theorem safe_9_0 : ∀ m, compatible p_9_0 m → WeightedBound 64 m := sound 64 _ cert_9_0 (by decide) checked_9_0
def p_9_1 := refine p_9 (2,true) (some ⟨false,true,0⟩)
def cert_9_1 : Tree := (.side 15 11 true (-1))
theorem checked_9_1 : check 64 p_9_1 cert_9_1 = true := by decide +kernel
theorem safe_9_1 : ∀ m, compatible p_9_1 m → WeightedBound 64 m := sound 64 _ cert_9_1 (by decide) checked_9_1
def p_9_2 := refine p_9 (2,true) (some ⟨true,false,0⟩)
def cert_9_2 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_9_2 : check 64 p_9_2 cert_9_2 = true := by decide +kernel
theorem safe_9_2 : ∀ m, compatible p_9_2 m → WeightedBound 64 m := sound 64 _ cert_9_2 (by decide) checked_9_2
def p_9_3 := refine p_9 (2,true) (some ⟨true,true,0⟩)
def cert_9_3 : Tree := (.side 7 14 false (2))
theorem checked_9_3 : check 64 p_9_3 cert_9_3 = true := by decide +kernel
theorem safe_9_3 : ∀ m, compatible p_9_3 m → WeightedBound 64 m := sound 64 _ cert_9_3 (by decide) checked_9_3
def p_9_4 := refine p_9 (2,true) (some ⟨false,false,1⟩)
def cert_9_4 : Tree := (.side 1 14 false (2))
theorem checked_9_4 : check 64 p_9_4 cert_9_4 = true := by decide +kernel
theorem safe_9_4 : ∀ m, compatible p_9_4 m → WeightedBound 64 m := sound 64 _ cert_9_4 (by decide) checked_9_4
def p_9_5 := refine p_9 (2,true) (some ⟨false,true,1⟩)
def cert_9_5 : Tree := (.side 0 35 true (-2))
theorem checked_9_5 : check 64 p_9_5 cert_9_5 = true := by decide +kernel
theorem safe_9_5 : ∀ m, compatible p_9_5 m → WeightedBound 64 m := sound 64 _ cert_9_5 (by decide) checked_9_5
def p_9_6 := refine p_9 (2,true) (some ⟨true,false,1⟩)
def cert_9_6 : Tree := (.side 11 6 true (-1))
theorem checked_9_6 : check 64 p_9_6 cert_9_6 = true := by decide +kernel
theorem safe_9_6 : ∀ m, compatible p_9_6 m → WeightedBound 64 m := sound 64 _ cert_9_6 (by decide) checked_9_6
def p_9_7 := refine p_9 (2,true) (some ⟨true,true,1⟩)
def cert_9_7 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_9_7 : check 64 p_9_7 cert_9_7 = true := by decide +kernel
theorem safe_9_7 : ∀ m, compatible p_9_7 m → WeightedBound 64 m := sound 64 _ cert_9_7 (by decide) checked_9_7
def p_9_8 := refine p_9 (2,true) (some ⟨false,false,2⟩)
def cert_9_8 : Tree := (.side 7 12 false (1))
theorem checked_9_8 : check 64 p_9_8 cert_9_8 = true := by decide +kernel
theorem safe_9_8 : ∀ m, compatible p_9_8 m → WeightedBound 64 m := sound 64 _ cert_9_8 (by decide) checked_9_8
def p_9_9 := refine p_9 (2,true) (some ⟨false,true,2⟩)
def cert_9_9 : Tree := (.side 0 18 true (-2))
theorem checked_9_9 : check 64 p_9_9 cert_9_9 = true := by decide +kernel
theorem safe_9_9 : ∀ m, compatible p_9_9 m → WeightedBound 64 m := sound 64 _ cert_9_9 (by decide) checked_9_9
def p_9_10 := refine p_9 (2,true) (some ⟨true,false,2⟩)
def cert_9_10 : Tree := (.side 7 12 false (1))
theorem checked_9_10 : check 64 p_9_10 cert_9_10 = true := by decide +kernel
theorem safe_9_10 : ∀ m, compatible p_9_10 m → WeightedBound 64 m := sound 64 _ cert_9_10 (by decide) checked_9_10
def p_9_11 := refine p_9 (2,true) (some ⟨true,true,2⟩)
def cert_9_11 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_9_11 : check 64 p_9_11 cert_9_11 = true := by decide +kernel
theorem safe_9_11 : ∀ m, compatible p_9_11 m → WeightedBound 64 m := sound 64 _ cert_9_11 (by decide) checked_9_11
def p_9_12 := refine p_9 (2,true) (some ⟨false,false,3⟩)
def cert_9_12 : Tree := (.side 7 10 false (1))
theorem checked_9_12 : check 64 p_9_12 cert_9_12 = true := by decide +kernel
theorem safe_9_12 : ∀ m, compatible p_9_12 m → WeightedBound 64 m := sound 64 _ cert_9_12 (by decide) checked_9_12
def p_9_13 := refine p_9 (2,true) (some ⟨false,true,3⟩)
def cert_9_13 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_9_13 : check 64 p_9_13 cert_9_13 = true := by decide +kernel
theorem safe_9_13 : ∀ m, compatible p_9_13 m → WeightedBound 64 m := sound 64 _ cert_9_13 (by decide) checked_9_13
def p_9_14 := refine p_9 (2,true) (some ⟨true,false,3⟩)
def cert_9_14 : Tree := (.side 7 10 false (1))
theorem checked_9_14 : check 64 p_9_14 cert_9_14 = true := by decide +kernel
theorem safe_9_14 : ∀ m, compatible p_9_14 m → WeightedBound 64 m := sound 64 _ cert_9_14 (by decide) checked_9_14
def p_9_15 := refine p_9 (2,true) (some ⟨true,true,3⟩)
def cert_9_15 : Tree := (.side 7 12 false (1))
theorem checked_9_15 : check 64 p_9_15 cert_9_15 = true := by decide +kernel
theorem safe_9_15 : ∀ m, compatible p_9_15 m → WeightedBound 64 m := sound 64 _ cert_9_15 (by decide) checked_9_15
def p_9_16 := refine p_9 (2,true) (some ⟨false,false,4⟩)
def cert_9_16 : Tree := (.side 21 9 false (-1))
theorem checked_9_16 : check 64 p_9_16 cert_9_16 = true := by decide +kernel
theorem safe_9_16 : ∀ m, compatible p_9_16 m → WeightedBound 64 m := sound 64 _ cert_9_16 (by decide) checked_9_16
def p_9_17 := refine p_9 (2,true) (some ⟨false,true,4⟩)
def cert_9_17 : Tree := (.side 0 23 true (-2))
theorem checked_9_17 : check 64 p_9_17 cert_9_17 = true := by decide +kernel
theorem safe_9_17 : ∀ m, compatible p_9_17 m → WeightedBound 64 m := sound 64 _ cert_9_17 (by decide) checked_9_17
def p_9_18 := refine p_9 (2,true) (some ⟨true,false,4⟩)
def cert_9_18 : Tree := (.side 13 2 true (-1))
theorem checked_9_18 : check 64 p_9_18 cert_9_18 = true := by decide +kernel
theorem safe_9_18 : ∀ m, compatible p_9_18 m → WeightedBound 64 m := sound 64 _ cert_9_18 (by decide) checked_9_18
def p_9_19 := refine p_9 (2,true) (some ⟨true,true,4⟩)
def cert_9_19 : Tree := (.side 12 4 true (-1))
theorem checked_9_19 : check 64 p_9_19 cert_9_19 = true := by decide +kernel
theorem safe_9_19 : ∀ m, compatible p_9_19 m → WeightedBound 64 m := sound 64 _ cert_9_19 (by decide) checked_9_19
def p_9_20 := refine p_9 (2,true) (some ⟨false,false,5⟩)
def cert_9_20 : Tree := (split 15 (5,false) 6 #[
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 22 (5,true)),
(.last 18 (5,true)),
(.last 23 (5,true)),
(.last 18 (5,true)),
(.side 0 19 false (2)),
(.last 20 (5,true)),
(.last 22 (5,true)),
(.side 2 14 false (2)),
(.side 8 8 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 8 8 false (0)),
(.side 4 12 false (2)),
(.side 0 22 false (2)),
(.side 0 24 true (-2)),
(.side 17 3 false (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 16 (5,true)),
(.last 17 (5,true)),
(.last 16 (5,true)),
(.last 17 (5,true))])
theorem checked_9_20 : check 64 p_9_20 cert_9_20 = true := by decide +kernel
theorem safe_9_20 : ∀ m, compatible p_9_20 m → WeightedBound 64 m := sound 64 _ cert_9_20 (by decide) checked_9_20
def p_9_21 := refine p_9 (2,true) (some ⟨false,true,5⟩)
def cert_9_21 : Tree := (split 15 (5,true) 6 #[
(.last 19 (5,false)),
(.side 0 28 true (-2)),
(.last 21 (5,false)),
(.side 3 13 true (-2)),
(.side 7 18 false (1)),
(.side 0 19 true (-2)),
(.last 21 (5,false)),
(.side 1 43 true (-2)),
(.side 6 18 false (2)),
(.last 17 (5,false)),
(.side 6 20 false (2)),
(.last 17 (5,false)),
(.last 21 (5,false)),
(.last 23 (5,false)),
(.last 29 (5,false)),
(.side 16 11 true (-1)),
(.last 21 (5,false)),
(.last 19 (5,false)),
(.last 21 (5,false)),
(.side 12 29 true (-1)),
(.last 16 (5,false)),
(.last 17 (5,false)),
(.last 16 (5,false)),
(.last 17 (5,false))])
theorem checked_9_21 : check 64 p_9_21 cert_9_21 = true := by decide +kernel
theorem safe_9_21 : ∀ m, compatible p_9_21 m → WeightedBound 64 m := sound 64 _ cert_9_21 (by decide) checked_9_21
def p_9_22 := refine p_9 (2,true) (some ⟨true,false,5⟩)
def cert_9_22 : Tree := (split 15 (5,false) 6 #[
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.side 7 18 false (1)),
(.side 0 29 true (-2)),
(.last 23 (5,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.side 0 19 false (2)),
(.side 14 2 true (-1)),
(.last 22 (5,true)),
(.last 17 (5,true)),
(.side 8 8 false (0)),
(.side 7 12 false (1)),
(.side 8 8 false (0)),
(.side 6 10 false (2)),
(.last 25 (5,true)),
(.side 12 4 true (-1)),
(.side 17 3 false (-2)),
(.side 17 5 false (-1)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true))])
theorem checked_9_22 : check 64 p_9_22 cert_9_22 = true := by decide +kernel
theorem safe_9_22 : ∀ m, compatible p_9_22 m → WeightedBound 64 m := sound 64 _ cert_9_22 (by decide) checked_9_22
def p_9_23 := refine p_9 (2,true) (some ⟨true,true,5⟩)
def cert_9_23 : Tree := (split 15 (5,true) 6 #[
(.side 7 16 false (1)),
(.side 18 18 false (3)),
(.side 7 14 false (1)),
(.side 18 16 false (3)),
(.last 19 (5,false)),
(.side 0 19 true (-2)),
(.last 25 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[],[],[],[],[],[(true,5),(true,13)],[(false,14)],[(true,14)],[(false,11)],[(true,11)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,6)],[],[(true,2)],[],[(true,4)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,2),(3,2)]⟩,#[(.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty) .empty)),(.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) (.branch (.branch .leaf (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .empty))) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .empty))) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty))))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .empty .leaf)))) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) (.branch .empty .leaf)))) .leaf) (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty))) (.branch .leaf (.branch .leaf (.branch (.branch .empty .leaf) .empty))))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .empty .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) (.branch (.branch .leaf (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) (.branch .leaf (.branch (.branch .leaf .leaf) (.branch .empty .leaf)))))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty))))) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty)) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty)))) .empty)]⟩),
(.last 17 (5,false)),
(.last 17 (5,false)),
(.side 14 2 true (0)),
(.last 17 (5,false)),
(.side 7 12 false (1)),
(.side 7 16 false (2)),
(.side 7 12 false (1)),
(.side 7 14 false (2)),
(.last 19 (5,false)),
(.last 19 (5,false)),
(.side 12 4 true (-1)),
(.side 12 6 true (-1)),
(.last 17 (5,false)),
(.last 17 (5,false)),
(.last 17 (5,false)),
(.last 17 (5,false))])
theorem checked_9_23 : check 64 p_9_23 cert_9_23 = true := by decide +kernel
theorem safe_9_23 : ∀ m, compatible p_9_23 m → WeightedBound 64 m := sound 64 _ cert_9_23 (by decide) checked_9_23
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 64 m := by
  apply split_safe 64 p_9 14 (2,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_9_0 | exact safe_9_1 | exact safe_9_2 | exact safe_9_3 | exact safe_9_4 | exact safe_9_5 | exact safe_9_6 | exact safe_9_7 | exact safe_9_8 | exact safe_9_9 | exact safe_9_10 | exact safe_9_11 | exact safe_9_12 | exact safe_9_13 | exact safe_9_14 | exact safe_9_15 | exact safe_9_16 | exact safe_9_17 | exact safe_9_18 | exact safe_9_19 | exact safe_9_20 | exact safe_9_21 | exact safe_9_22 | exact safe_9_23
def p_10 := refine parent (4,false) (some ⟨true,false,2⟩)
def p_10_0 := refine p_10 (2,true) (some ⟨false,false,0⟩)
def cert_10_0 : Tree := (.side 3 15 false (2))
theorem checked_10_0 : check 64 p_10_0 cert_10_0 = true := by decide +kernel
theorem safe_10_0 : ∀ m, compatible p_10_0 m → WeightedBound 64 m := sound 64 _ cert_10_0 (by decide) checked_10_0
def p_10_1 := refine p_10 (2,true) (some ⟨false,true,0⟩)
def cert_10_1 : Tree := (.side 7 9 false (1))
theorem checked_10_1 : check 64 p_10_1 cert_10_1 = true := by decide +kernel
theorem safe_10_1 : ∀ m, compatible p_10_1 m → WeightedBound 64 m := sound 64 _ cert_10_1 (by decide) checked_10_1
def p_10_2 := refine p_10 (2,true) (some ⟨true,false,0⟩)
def cert_10_2 : Tree := (.side 10 5 false (0))
theorem checked_10_2 : check 64 p_10_2 cert_10_2 = true := by decide +kernel
theorem safe_10_2 : ∀ m, compatible p_10_2 m → WeightedBound 64 m := sound 64 _ cert_10_2 (by decide) checked_10_2
def p_10_3 := refine p_10 (2,true) (some ⟨true,true,0⟩)
def cert_10_3 : Tree := (.side 5 10 false (2))
theorem checked_10_3 : check 64 p_10_3 cert_10_3 = true := by decide +kernel
theorem safe_10_3 : ∀ m, compatible p_10_3 m → WeightedBound 64 m := sound 64 _ cert_10_3 (by decide) checked_10_3
def p_10_4 := refine p_10 (2,true) (some ⟨false,false,1⟩)
def cert_10_4 : Tree := (.side 7 13 false (1))
theorem checked_10_4 : check 64 p_10_4 cert_10_4 = true := by decide +kernel
theorem safe_10_4 : ∀ m, compatible p_10_4 m → WeightedBound 64 m := sound 64 _ cert_10_4 (by decide) checked_10_4
def p_10_5 := refine p_10 (2,true) (some ⟨false,true,1⟩)
def cert_10_5 : Tree := (.side 2 23 false (2))
theorem checked_10_5 : check 64 p_10_5 cert_10_5 = true := by decide +kernel
theorem safe_10_5 : ∀ m, compatible p_10_5 m → WeightedBound 64 m := sound 64 _ cert_10_5 (by decide) checked_10_5
def p_10_6 := refine p_10 (2,true) (some ⟨true,false,1⟩)
def cert_10_6 : Tree := (.side 11 13 false (0))
theorem checked_10_6 : check 64 p_10_6 cert_10_6 = true := by decide +kernel
theorem safe_10_6 : ∀ m, compatible p_10_6 m → WeightedBound 64 m := sound 64 _ cert_10_6 (by decide) checked_10_6
def p_10_7 := refine p_10 (2,true) (some ⟨true,true,1⟩)
def cert_10_7 : Tree := (.side 11 4 true (-2))
theorem checked_10_7 : check 64 p_10_7 cert_10_7 = true := by decide +kernel
theorem safe_10_7 : ∀ m, compatible p_10_7 m → WeightedBound 64 m := sound 64 _ cert_10_7 (by decide) checked_10_7
def p_10_8 := refine p_10 (2,true) (some ⟨false,false,2⟩)
def cert_10_8 : Tree := (.side 0 16 false (2))
theorem checked_10_8 : check 64 p_10_8 cert_10_8 = true := by decide +kernel
theorem safe_10_8 : ∀ m, compatible p_10_8 m → WeightedBound 64 m := sound 64 _ cert_10_8 (by decide) checked_10_8
def p_10_9 := refine p_10 (2,true) (some ⟨false,true,2⟩)
def cert_10_9 : Tree := (.side 0 20 true (-2))
theorem checked_10_9 : check 64 p_10_9 cert_10_9 = true := by decide +kernel
theorem safe_10_9 : ∀ m, compatible p_10_9 m → WeightedBound 64 m := sound 64 _ cert_10_9 (by decide) checked_10_9
def p_10_10 := refine p_10 (2,true) (some ⟨true,false,2⟩)
def cert_10_10 : Tree := (.side 14 6 false (-2))
theorem checked_10_10 : check 64 p_10_10 cert_10_10 = true := by decide +kernel
theorem safe_10_10 : ∀ m, compatible p_10_10 m → WeightedBound 64 m := sound 64 _ cert_10_10 (by decide) checked_10_10
def p_10_11 := refine p_10 (2,true) (some ⟨true,true,2⟩)
def cert_10_11 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_10_11 : check 64 p_10_11 cert_10_11 = true := by decide +kernel
theorem safe_10_11 : ∀ m, compatible p_10_11 m → WeightedBound 64 m := sound 64 _ cert_10_11 (by decide) checked_10_11
def p_10_12 := refine p_10 (2,true) (some ⟨false,false,3⟩)
def cert_10_12 : Tree := (.side 7 16 false (1))
theorem checked_10_12 : check 64 p_10_12 cert_10_12 = true := by decide +kernel
theorem safe_10_12 : ∀ m, compatible p_10_12 m → WeightedBound 64 m := sound 64 _ cert_10_12 (by decide) checked_10_12
def p_10_13 := refine p_10 (2,true) (some ⟨false,true,3⟩)
def cert_10_13 : Tree := (.side 8 7 false (0))
theorem checked_10_13 : check 64 p_10_13 cert_10_13 = true := by decide +kernel
theorem safe_10_13 : ∀ m, compatible p_10_13 m → WeightedBound 64 m := sound 64 _ cert_10_13 (by decide) checked_10_13
def p_10_14 := refine p_10 (2,true) (some ⟨true,false,3⟩)
def cert_10_14 : Tree := (.side 9 6 false (0))
theorem checked_10_14 : check 64 p_10_14 cert_10_14 = true := by decide +kernel
theorem safe_10_14 : ∀ m, compatible p_10_14 m → WeightedBound 64 m := sound 64 _ cert_10_14 (by decide) checked_10_14
def p_10_15 := refine p_10 (2,true) (some ⟨true,true,3⟩)
def cert_10_15 : Tree := (.side 7 8 false (1))
theorem checked_10_15 : check 64 p_10_15 cert_10_15 = true := by decide +kernel
theorem safe_10_15 : ∀ m, compatible p_10_15 m → WeightedBound 64 m := sound 64 _ cert_10_15 (by decide) checked_10_15
def p_10_16 := refine p_10 (2,true) (some ⟨false,false,4⟩)
def cert_10_16 : Tree := (.side 15 7 false (-3))
theorem checked_10_16 : check 64 p_10_16 cert_10_16 = true := by decide +kernel
theorem safe_10_16 : ∀ m, compatible p_10_16 m → WeightedBound 64 m := sound 64 _ cert_10_16 (by decide) checked_10_16
def p_10_17 := refine p_10 (2,true) (some ⟨false,true,4⟩)
def cert_10_17 : Tree := (.side 12 12 false (0))
theorem checked_10_17 : check 64 p_10_17 cert_10_17 = true := by decide +kernel
theorem safe_10_17 : ∀ m, compatible p_10_17 m → WeightedBound 64 m := sound 64 _ cert_10_17 (by decide) checked_10_17
def p_10_18 := refine p_10 (2,true) (some ⟨true,false,4⟩)
def cert_10_18 : Tree := (.side 15 7 false (-3))
theorem checked_10_18 : check 64 p_10_18 cert_10_18 = true := by decide +kernel
theorem safe_10_18 : ∀ m, compatible p_10_18 m → WeightedBound 64 m := sound 64 _ cert_10_18 (by decide) checked_10_18
def p_10_19 := refine p_10 (2,true) (some ⟨true,true,4⟩)
def cert_10_19 : Tree := (.side 15 9 false (-1))
theorem checked_10_19 : check 64 p_10_19 cert_10_19 = true := by decide +kernel
theorem safe_10_19 : ∀ m, compatible p_10_19 m → WeightedBound 64 m := sound 64 _ cert_10_19 (by decide) checked_10_19
def p_10_20 := refine p_10 (2,true) (some ⟨false,false,5⟩)
def cert_10_20 : Tree := (split 15 (5,false) 6 #[
(.side 0 16 false (2)),
(.side 10 6 true (-3)),
(.side 7 16 false (1)),
(.last 21 (5,true)),
(.side 7 14 false (1)),
(.last 18 (5,true)),
(.last 18 (5,true)),
(.last 18 (5,true)),
(.side 0 17 false (2)),
(.last 20 (5,true)),
(.last 20 (5,true)),
(.side 7 13 false (1)),
(.side 7 17 false (1)),
(.side 9 7 false (0)),
(.side 9 7 false (0)),
(.side 7 11 false (1)),
(.last 21 (5,true)),
(.last 21 (5,true)),
(.last 21 (5,true)),
(.side 13 3 false (-1)),
(.side 15 1 false (-3)),
(.last 17 (5,true)),
(.side 15 1 false (-3)),
(.last 17 (5,true))])
theorem checked_10_20 : check 64 p_10_20 cert_10_20 = true := by decide +kernel
theorem safe_10_20 : ∀ m, compatible p_10_20 m → WeightedBound 64 m := sound 64 _ cert_10_20 (by decide) checked_10_20
def p_10_21 := refine p_10 (2,true) (some ⟨false,true,5⟩)
def cert_10_21 : Tree := (split 15 (5,true) 6 #[
(.last 23 (5,false)),
(.side 7 10 true (-2)),
(.side 10 6 true (-2)),
(.side 5 11 false (2)),
(.side 7 14 false (1)),
(.last 30 (5,false)),
(.last 27 (5,false)),
(.side 7 25 true (-2)),
(.side 0 17 false (2)),
(.last 19 (5,false)),
(.side 2 19 false (2)),
(.last 19 (5,false)),
(.side 7 17 false (1)),
(.side 8 8 true (-2)),
(.side 9 7 false (0)),
(.side 7 9 false (1)),
(.last 21 (5,false)),
(.side 2 23 false (2)),
(.side 13 12 false (-1)),
(.side 12 18 false (0)),
(.last 16 (5,false)),
(.last 19 (5,false)),
(.last 16 (5,false)),
(.last 19 (5,false))])
theorem checked_10_21 : check 64 p_10_21 cert_10_21 = true := by decide +kernel
theorem safe_10_21 : ∀ m, compatible p_10_21 m → WeightedBound 64 m := sound 64 _ cert_10_21 (by decide) checked_10_21
def p_10_22 := refine p_10 (2,true) (some ⟨true,false,5⟩)
def cert_10_22 : Tree := (split 15 (5,false) 6 #[
(.last 19 (5,true)),
(.side 7 10 false (1)),
(.side 10 6 false (0)),
(.side 5 11 false (2)),
(.side 7 14 false (1)),
(.last 23 (5,true)),
(.last 18 (5,true)),
(.side 11 5 false (0)),
(.side 0 17 false (2)),
(.side 14 2 true (-3)),
(.last 20 (5,true)),
(.last 17 (5,true)),
(.side 7 17 false (1)),
(.side 8 8 false (0)),
(.side 9 7 false (0)),
(.side 7 9 false (1)),
(.last 21 (5,true)),
(.last 22 (5,true)),
(.last 21 (5,true)),
(.last 23 (5,true)),
(.side 15 1 false (-3)),
(.last 16 (5,true)),
(.side 15 1 false (-3)),
(.last 16 (5,true))])
theorem checked_10_22 : check 64 p_10_22 cert_10_22 = true := by decide +kernel
theorem safe_10_22 : ∀ m, compatible p_10_22 m → WeightedBound 64 m := sound 64 _ cert_10_22 (by decide) checked_10_22
def p_10_23 := refine p_10 (2,true) (some ⟨true,true,5⟩)
def cert_10_23 : Tree := (split 15 (5,true) 6 #[
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.side 2 23 false (2)),
(.side 7 16 false (1)),
(.side 11 18 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) .leaf),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.last 17 (5,false)),
(.last 19 (5,false)),
(.side 14 2 true (-2)),
(.last 19 (5,false)),
(.side 8 8 false (0)),
(.side 7 12 false (1)),
(.side 8 8 false (0)),
(.side 6 10 false (2)),
(.side 16 9 false (-2)),
(.side 12 4 true (-2)),
(.side 16 9 false (-2)),
(.side 16 11 false (0)),
(.last 17 (5,false)),
(.last 19 (5,false)),
(.last 17 (5,false)),
(.last 19 (5,false))])
theorem checked_10_23 : check 64 p_10_23 cert_10_23 = true := by decide +kernel
theorem safe_10_23 : ∀ m, compatible p_10_23 m → WeightedBound 64 m := sound 64 _ cert_10_23 (by decide) checked_10_23
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 64 m := by
  apply split_safe 64 p_10 14 (2,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_10_0 | exact safe_10_1 | exact safe_10_2 | exact safe_10_3 | exact safe_10_4 | exact safe_10_5 | exact safe_10_6 | exact safe_10_7 | exact safe_10_8 | exact safe_10_9 | exact safe_10_10 | exact safe_10_11 | exact safe_10_12 | exact safe_10_13 | exact safe_10_14 | exact safe_10_15 | exact safe_10_16 | exact safe_10_17 | exact safe_10_18 | exact safe_10_19 | exact safe_10_20 | exact safe_10_21 | exact safe_10_22 | exact safe_10_23
def p_11 := refine parent (4,false) (some ⟨true,true,2⟩)
def p_11_0 := refine p_11 (2,true) (some ⟨false,false,0⟩)
def cert_11_0 : Tree := (.side 3 12 false (2))
theorem checked_11_0 : check 64 p_11_0 cert_11_0 = true := by decide +kernel
theorem safe_11_0 : ∀ m, compatible p_11_0 m → WeightedBound 64 m := sound 64 _ cert_11_0 (by decide) checked_11_0
def p_11_1 := refine p_11 (2,true) (some ⟨false,true,0⟩)
def cert_11_1 : Tree := (.side 4 14 false (2))
theorem checked_11_1 : check 64 p_11_1 cert_11_1 = true := by decide +kernel
theorem safe_11_1 : ∀ m, compatible p_11_1 m → WeightedBound 64 m := sound 64 _ cert_11_1 (by decide) checked_11_1
def p_11_2 := refine p_11 (2,true) (some ⟨true,false,0⟩)
def cert_11_2 : Tree := (.side 5 10 false (2))
theorem checked_11_2 : check 64 p_11_2 cert_11_2 = true := by decide +kernel
theorem safe_11_2 : ∀ m, compatible p_11_2 m → WeightedBound 64 m := sound 64 _ cert_11_2 (by decide) checked_11_2
def p_11_3 := refine p_11 (2,true) (some ⟨true,true,0⟩)
def cert_11_3 : Tree := (.side 6 12 false (2))
theorem checked_11_3 : check 64 p_11_3 cert_11_3 = true := by decide +kernel
theorem safe_11_3 : ∀ m, compatible p_11_3 m → WeightedBound 64 m := sound 64 _ cert_11_3 (by decide) checked_11_3
def p_11_4 := refine p_11 (2,true) (some ⟨false,false,1⟩)
def cert_11_4 : Tree := (.side 16 17 true (0))
theorem checked_11_4 : check 64 p_11_4 cert_11_4 = true := by decide +kernel
theorem safe_11_4 : ∀ m, compatible p_11_4 m → WeightedBound 64 m := sound 64 _ cert_11_4 (by decide) checked_11_4
def p_11_5 := refine p_11 (2,true) (some ⟨false,true,1⟩)
def cert_11_5 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_11_5 : check 64 p_11_5 cert_11_5 = true := by decide +kernel
theorem safe_11_5 : ∀ m, compatible p_11_5 m → WeightedBound 64 m := sound 64 _ cert_11_5 (by decide) checked_11_5
def p_11_6 := refine p_11 (2,true) (some ⟨true,false,1⟩)
def cert_11_6 : Tree := (.side 11 4 true (-1))
theorem checked_11_6 : check 64 p_11_6 cert_11_6 = true := by decide +kernel
theorem safe_11_6 : ∀ m, compatible p_11_6 m → WeightedBound 64 m := sound 64 _ cert_11_6 (by decide) checked_11_6
def p_11_7 := refine p_11 (2,true) (some ⟨true,true,1⟩)
def cert_11_7 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_11_7 : check 64 p_11_7 cert_11_7 = true := by decide +kernel
theorem safe_11_7 : ∀ m, compatible p_11_7 m → WeightedBound 64 m := sound 64 _ cert_11_7 (by decide) checked_11_7
def p_11_8 := refine p_11 (2,true) (some ⟨false,false,2⟩)
def cert_11_8 : Tree := (.side 0 18 false (2))
theorem checked_11_8 : check 64 p_11_8 cert_11_8 = true := by decide +kernel
theorem safe_11_8 : ∀ m, compatible p_11_8 m → WeightedBound 64 m := sound 64 _ cert_11_8 (by decide) checked_11_8
def p_11_9 := refine p_11 (2,true) (some ⟨false,true,2⟩)
def cert_11_9 : Tree := (.side 0 18 true (-2))
theorem checked_11_9 : check 64 p_11_9 cert_11_9 = true := by decide +kernel
theorem safe_11_9 : ∀ m, compatible p_11_9 m → WeightedBound 64 m := sound 64 _ cert_11_9 (by decide) checked_11_9
def p_11_10 := refine p_11 (2,true) (some ⟨true,false,2⟩)
def cert_11_10 : Tree := (.side 14 6 false (0))
theorem checked_11_10 : check 64 p_11_10 cert_11_10 = true := by decide +kernel
theorem safe_11_10 : ∀ m, compatible p_11_10 m → WeightedBound 64 m := sound 64 _ cert_11_10 (by decide) checked_11_10
def p_11_11 := refine p_11 (2,true) (some ⟨true,true,2⟩)
def cert_11_11 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_11_11 : check 64 p_11_11 cert_11_11 = true := by decide +kernel
theorem safe_11_11 : ∀ m, compatible p_11_11 m → WeightedBound 64 m := sound 64 _ cert_11_11 (by decide) checked_11_11
def p_11_12 := refine p_11 (2,true) (some ⟨false,false,3⟩)
def cert_11_12 : Tree := (.side 7 8 false (1))
theorem checked_11_12 : check 64 p_11_12 cert_11_12 = true := by decide +kernel
theorem safe_11_12 : ∀ m, compatible p_11_12 m → WeightedBound 64 m := sound 64 _ cert_11_12 (by decide) checked_11_12
def p_11_13 := refine p_11 (2,true) (some ⟨false,true,3⟩)
def cert_11_13 : Tree := (.side 4 12 false (2))
theorem checked_11_13 : check 64 p_11_13 cert_11_13 = true := by decide +kernel
theorem safe_11_13 : ∀ m, compatible p_11_13 m → WeightedBound 64 m := sound 64 _ cert_11_13 (by decide) checked_11_13
def p_11_14 := refine p_11 (2,true) (some ⟨true,false,3⟩)
def cert_11_14 : Tree := (.side 7 8 false (1))
theorem checked_11_14 : check 64 p_11_14 cert_11_14 = true := by decide +kernel
theorem safe_11_14 : ∀ m, compatible p_11_14 m → WeightedBound 64 m := sound 64 _ cert_11_14 (by decide) checked_11_14
def p_11_15 := refine p_11 (2,true) (some ⟨true,true,3⟩)
def cert_11_15 : Tree := (.side 6 10 false (2))
theorem checked_11_15 : check 64 p_11_15 cert_11_15 = true := by decide +kernel
theorem safe_11_15 : ∀ m, compatible p_11_15 m → WeightedBound 64 m := sound 64 _ cert_11_15 (by decide) checked_11_15
def p_11_16 := refine p_11 (2,true) (some ⟨false,false,4⟩)
def cert_11_16 : Tree := (.side 16 3 false (-2))
theorem checked_11_16 : check 64 p_11_16 cert_11_16 = true := by decide +kernel
theorem safe_11_16 : ∀ m, compatible p_11_16 m → WeightedBound 64 m := sound 64 _ cert_11_16 (by decide) checked_11_16
def p_11_17 := refine p_11 (2,true) (some ⟨false,true,4⟩)
def cert_11_17 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_11_17 : check 64 p_11_17 cert_11_17 = true := by decide +kernel
theorem safe_11_17 : ∀ m, compatible p_11_17 m → WeightedBound 64 m := sound 64 _ cert_11_17 (by decide) checked_11_17
def p_11_18 := refine p_11 (2,true) (some ⟨true,false,4⟩)
def cert_11_18 : Tree := (.side 16 3 false (-2))
theorem checked_11_18 : check 64 p_11_18 cert_11_18 = true := by decide +kernel
theorem safe_11_18 : ∀ m, compatible p_11_18 m → WeightedBound 64 m := sound 64 _ cert_11_18 (by decide) checked_11_18
def p_11_19 := refine p_11 (2,true) (some ⟨true,true,4⟩)
def cert_11_19 : Tree := (.side 16 5 false (0))
theorem checked_11_19 : check 64 p_11_19 cert_11_19 = true := by decide +kernel
theorem safe_11_19 : ∀ m, compatible p_11_19 m → WeightedBound 64 m := sound 64 _ cert_11_19 (by decide) checked_11_19
def p_11_20 := refine p_11 (2,true) (some ⟨false,false,5⟩)
def cert_11_20 : Tree := (split 15 (5,true) 6 #[
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 7 15 false (1)),
(.side 17 17 true (0)),
(.side 19 3 false (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.last 17 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.last 17 (5,false)),
(.side 2 14 false (2)),
(.side 8 8 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 8 8 false (0)),
(.side 4 12 false (2)),
(.side 7 18 false (1)),
(.side 16 17 true (0)),
(.side 17 3 false (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.last 17 (5,false)),
(.last 16 (5,false)),
(.last 17 (5,false)),
(.last 16 (5,false))])
theorem checked_11_20 : check 64 p_11_20 cert_11_20 = true := by decide +kernel
theorem safe_11_20 : ∀ m, compatible p_11_20 m → WeightedBound 64 m := sound 64 _ cert_11_20 (by decide) checked_11_20
def p_11_21 := refine p_11 (2,true) (some ⟨false,true,5⟩)
def cert_11_21 : Tree := (split 15 (5,true) 6 #[
(.last 19 (5,false)),
(.side 0 28 true (-2)),
(.last 21 (5,false)),
(.side 18 16 false (3)),
(.side 6 16 false (2)),
(.side 18 14 true (1)),
(.last 21 (5,false)),
(.last 49 (5,false)),
(.side 2 14 false (2)),
(.last 17 (5,false)),
(.side 2 14 false (2)),
(.last 17 (5,false)),
(.side 4 12 false (2)),
(.last 23 (5,false)),
(.side 4 12 false (2)),
(.side 4 14 false (2)),
(.side 6 16 false (2)),
(.last 19 (5,false)),
(.last 21 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1)],[],[],[],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))))]⟩),
(.last 16 (5,false)),
(.last 17 (5,false)),
(.last 16 (5,false)),
(.last 17 (5,false))])
theorem checked_11_21 : check 64 p_11_21 cert_11_21 = true := by decide +kernel
theorem safe_11_21 : ∀ m, compatible p_11_21 m → WeightedBound 64 m := sound 64 _ cert_11_21 (by decide) checked_11_21
def p_11_22 := refine p_11 (2,true) (some ⟨true,false,5⟩)
def cert_11_22 : Tree := (split 15 (5,true) 6 #[
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.side 7 18 false (1)),
(.side 16 20 true (0)),
(.side 19 3 false (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.last 17 (5,false)),
(.last 17 (5,false)),
(.last 17 (5,false)),
(.side 14 2 true (-1)),
(.side 8 8 false (0)),
(.side 7 12 false (1)),
(.side 8 8 false (0)),
(.side 6 10 false (2)),
(.side 7 18 false (1)),
(.side 12 4 true (-1)),
(.side 17 3 false (-2)),
(.side 17 5 false (-1)),
(.last 17 (5,false)),
(.last 19 (5,false)),
(.last 17 (5,false)),
(.last 19 (5,false))])
theorem checked_11_22 : check 64 p_11_22 cert_11_22 = true := by decide +kernel
theorem safe_11_22 : ∀ m, compatible p_11_22 m → WeightedBound 64 m := sound 64 _ cert_11_22 (by decide) checked_11_22
def p_11_23 := refine p_11 (2,true) (some ⟨true,true,5⟩)
def cert_11_23 : Tree := (split 15 (5,true) 6 #[
(.side 6 14 false (2)),
(.side 18 16 false (3)),
(.side 6 12 false (2)),
(.side 18 14 false (3)),
(.last 19 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,2)],[(false,4)],[(false,5)],[(true,6)],[(true,4)],[(false,8)],[(true,8)],[(true,10)],[(false,11),(false,24)],[(true,12)],[(true,5)],[(true,14)],[(false,15),(false,19)],[(false,16)],[(true,16)],[(true,18)],[(true,17)],[(true,15),(true,19)],[(false,21)],[(true,21)],[(true,23)]],#[(0,1),(3,2),(0,4),(0,0),(5,8),(6,14),(0,7),(0,0),(9,10),(0,0),(0,11),(12,0),(0,13),(0,0),(0,15),(16,21),(17,18),(0,20),(0,19),(16,21),(0,0),(22,23),(0,0),(0,24),(12,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,2),(true,2),(false,4),(true,4),(false,6),(true,6),(false,8),(true,8),(false,9),(false,11),(true,11),(false,12),(false,14),(true,14),(false,16),(true,16)],[(true,1)],[(false,3)],[(true,3)],[(false,5)],[(true,5)],[(false,7),(false,17)],[(true,7)],[(true,9)],[(false,10)],[(true,10)],[(true,12),(true,17)],[(false,13)],[(true,13)],[(false,15)],[(true,15)]],#[(0,1),(2,3),(2,2),(4,5),(2,2),(6,7),(2,2),(8,9),(2,2),(2,10),(11,12),(2,2),(2,13),(14,15),(2,2),(16,17),(2,2),(8,13)]⟩,#[(.branch .leaf (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) .leaf))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))) .empty),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf) (.branch .leaf (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty)) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))))),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))))),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))))]⟩),
(.last 25 (5,false)),
(.last 47 (5,false)),
(.last 17 (5,false)),
(.last 17 (5,false)),
(.side 14 2 true (0)),
(.last 17 (5,false)),
(.side 6 10 false (2)),
(.side 6 14 false (2)),
(.side 6 10 false (2)),
(.side 6 12 false (2)),
(.side 17 5 false (-1)),
(.last 19 (5,false)),
(.side 17 5 false (-1)),
(.side 17 7 false (1)),
(.last 19 (5,false)),
(.last 17 (5,false)),
(.last 19 (5,false)),
(.last 17 (5,false))])
theorem checked_11_23 : check 64 p_11_23 cert_11_23 = true := by decide +kernel
theorem safe_11_23 : ∀ m, compatible p_11_23 m → WeightedBound 64 m := sound 64 _ cert_11_23 (by decide) checked_11_23
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 64 m := by
  apply split_safe 64 p_11 14 (2,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_11_0 | exact safe_11_1 | exact safe_11_2 | exact safe_11_3 | exact safe_11_4 | exact safe_11_5 | exact safe_11_6 | exact safe_11_7 | exact safe_11_8 | exact safe_11_9 | exact safe_11_10 | exact safe_11_11 | exact safe_11_12 | exact safe_11_13 | exact safe_11_14 | exact safe_11_15 | exact safe_11_16 | exact safe_11_17 | exact safe_11_18 | exact safe_11_19 | exact safe_11_20 | exact safe_11_21 | exact safe_11_22 | exact safe_11_23
def p_12 := refine parent (4,false) (some ⟨false,false,3⟩)
def cert_12 : Tree := (.side 8 6 false (0))
theorem checked_12 : check 64 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 64 m := sound 64 _ cert_12 (by decide) checked_12
def p_13 := refine parent (4,false) (some ⟨false,true,3⟩)
def cert_13 : Tree := (.side 7 10 false (1))
theorem checked_13 : check 64 p_13 cert_13 = true := by decide +kernel
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 64 m := sound 64 _ cert_13 (by decide) checked_13
def p_14 := refine parent (4,false) (some ⟨true,false,3⟩)
def cert_14 : Tree := (.side 8 6 false (0))
theorem checked_14 : check 64 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 64 m := sound 64 _ cert_14 (by decide) checked_14
def p_15 := refine parent (4,false) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 6 8 false (2))
theorem checked_15 : check 64 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 64 m := sound 64 _ cert_15 (by decide) checked_15
def p_16 := refine parent (4,false) (some ⟨false,false,4⟩)
def cert_16 : Tree := (.side 15 1 false (-3))
theorem checked_16 : check 64 p_16 cert_16 = true := by decide +kernel
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 64 m := sound 64 _ cert_16 (by decide) checked_16
def p_17 := refine parent (4,false) (some ⟨false,true,4⟩)
def cert_17 : Tree := (.side 12 2 true (-1))
theorem checked_17 : check 64 p_17 cert_17 = true := by decide +kernel
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 64 m := sound 64 _ cert_17 (by decide) checked_17
def p_18 := refine parent (4,false) (some ⟨true,false,4⟩)
def cert_18 : Tree := (.side 15 1 false (-3))
theorem checked_18 : check 64 p_18 cert_18 = true := by decide +kernel
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 64 m := sound 64 _ cert_18 (by decide) checked_18
def p_19 := refine parent (4,false) (some ⟨true,true,4⟩)
def cert_19 : Tree := (.side 15 3 false (-1))
theorem checked_19 : check 64 p_19 cert_19 = true := by decide +kernel
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 64 m := sound 64 _ cert_19 (by decide) checked_19
def p_20 := refine parent (4,false) (some ⟨false,false,5⟩)
def p_20_0 := refine p_20 (5,true) (some ⟨false,false,0⟩)
def cert_20_0 : Tree := (.side 0 15 false (2))
theorem checked_20_0 : check 64 p_20_0 cert_20_0 = true := by decide +kernel
theorem safe_20_0 : ∀ m, compatible p_20_0 m → WeightedBound 64 m := sound 64 _ cert_20_0 (by decide) checked_20_0
def p_20_1 := refine p_20 (5,true) (some ⟨false,true,0⟩)
def cert_20_1 : Tree := (split 28 (5,false) 6 #[
(.side 15 20 true (-1)),
(.side 10 43 true (-2)),
(.side 15 18 true (-1)),
(.side 10 41 true (-2)),
(.side 15 25 false (3)),
(.side 10 36 true (-2)),
(.last 34 (2,true)),
(.side 10 34 true (-2)),
(.last 29 (2,true)),
(.side 10 36 true (-2)),
(.last 29 (2,true)),
(.side 2 27 true (-2)),
(.side 20 11 false (3)),
(.side 25 5 true (1)),
(.side 15 16 true (-1)),
(.side 4 25 true (-2)),
(.side 30 2 false (0)),
(.side 27 2 true (2)),
(.side 30 2 false (0)),
(.side 10 45 true (-2)),
(.side 0 30 true (-2)),
(.side 28 1 true (2)),
(.side 15 21 true (-1)),
(.side 28 1 true (2))])
theorem checked_20_1 : check 64 p_20_1 cert_20_1 = true := by decide +kernel
theorem safe_20_1 : ∀ m, compatible p_20_1 m → WeightedBound 64 m := sound 64 _ cert_20_1 (by decide) checked_20_1
def p_20_2 := refine p_20 (5,true) (some ⟨true,false,0⟩)
def cert_20_2 : Tree := (split 18 (5,false) 6 #[
(.side 7 15 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.side 7 13 false (1)),
(.side 5 19 false (2)),
(.side 7 20 false (1)),
(.last 20 (2,true)),
(.last 24 (2,true)),
(.last 20 (2,true)),
(.last 19 (2,true)),
(.last 22 (2,true)),
(.last 19 (2,true)),
(.side 2 17 false (2)),
(.side 8 11 false (0)),
(.side 7 19 false (1)),
(.side 8 11 false (0)),
(.side 4 15 false (2)),
(.side 20 2 false (-4)),
(.side 17 2 true (-2)),
(.side 20 2 false (-4)),
(.side 7 15 false (1)),
(.side 14 5 false (-1)),
(.side 46 1 true (2)),
(.side 10 10 false (0)),
(.side 6 17 false (2))])
theorem checked_20_2 : check 64 p_20_2 cert_20_2 = true := by decide +kernel
theorem safe_20_2 : ∀ m, compatible p_20_2 m → WeightedBound 64 m := sound 64 _ cert_20_2 (by decide) checked_20_2
def p_20_3 := refine p_20 (5,true) (some ⟨true,true,0⟩)
def cert_20_3 : Tree := (split 28 (5,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.side 29 31 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.side 21 8 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.last 29 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.last 29 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.side 25 5 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.side 33 2 false (-3)),
(.side 27 2 true (2)),
(.side 33 2 false (-3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 28 1 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .empty))]⟩),
(.side 28 1 true (2))])
theorem checked_20_3 : check 64 p_20_3 cert_20_3 = true := by decide +kernel
theorem safe_20_3 : ∀ m, compatible p_20_3 m → WeightedBound 64 m := sound 64 _ cert_20_3 (by decide) checked_20_3
def p_20_4 := refine p_20 (5,true) (some ⟨false,false,1⟩)
def cert_20_4 : Tree := (.side 7 13 false (1))
theorem checked_20_4 : check 64 p_20_4 cert_20_4 = true := by decide +kernel
theorem safe_20_4 : ∀ m, compatible p_20_4 m → WeightedBound 64 m := sound 64 _ cert_20_4 (by decide) checked_20_4
def p_20_5 := refine p_20 (5,true) (some ⟨false,true,1⟩)
def cert_20_5 : Tree := (split 16 (2,true) 6 #[
(.side 7 13 false (1)),
(.side 7 15 false (2)),
(.side 7 11 false (1)),
(.side 6 13 false (2)),
(.last 19 (5,false)),
(.last 20 (5,false)),
(.last 20 (5,false)),
(.last 58 (5,false)),
(.side 0 19 false (2)),
(.side 0 20 true (-2)),
(.side 16 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch .leaf .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf)))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch .empty .leaf) .empty)]⟩),
(.side 8 9 false (0)),
(.side 7 13 false (1)),
(.side 8 9 false (0)),
(.side 6 11 false (2)),
(.last 19 (5,false)),
(.last 28 (5,false)),
(.last 19 (5,false)),
(.last 21 (5,false)),
(.side 17 19 true (-1)),
(.last 20 (5,false)),
(.last 21 (5,false)),
(.last 20 (5,false))])
theorem checked_20_5 : check 64 p_20_5 cert_20_5 = true := by decide +kernel
theorem safe_20_5 : ∀ m, compatible p_20_5 m → WeightedBound 64 m := sound 64 _ cert_20_5 (by decide) checked_20_5
def p_20_6 := refine p_20 (5,true) (some ⟨true,false,1⟩)
def cert_20_6 : Tree := (split 16 (2,true) 6 #[
(.side 7 13 false (1)),
(.last 34 (5,false)),
(.side 7 11 false (1)),
(.last 31 (5,false)),
(.last 19 (5,false)),
(.last 22 (5,false)),
(.last 20 (5,false)),
(.last 30 (5,false)),
(.side 0 19 false (2)),
(.last 46 (5,false)),
(.side 16 6 false (-2)),
(.side 2 15 false (2)),
(.side 8 9 false (0)),
(.last 26 (5,false)),
(.side 8 9 false (0)),
(.side 4 13 false (2)),
(.last 19 (5,false)),
(.last 18 (5,false)),
(.last 19 (5,false)),
(.last 22 (5,false)),
(.side 14 3 false (-2)),
(.last 17 (5,false)),
(.side 14 3 false (-2)),
(.last 17 (5,false))])
theorem checked_20_6 : check 64 p_20_6 cert_20_6 = true := by decide +kernel
theorem safe_20_6 : ∀ m, compatible p_20_6 m → WeightedBound 64 m := sound 64 _ cert_20_6 (by decide) checked_20_6
def p_20_7 := refine p_20 (5,true) (some ⟨true,true,1⟩)
def cert_20_7 : Tree := (split 16 (2,true) 6 #[
(.side 3 14 false (2)),
(.side 4 16 false (2)),
(.side 5 12 false (2)),
(.side 6 14 false (2)),
(.last 19 (5,false)),
(.last 20 (5,false)),
(.side 11 6 true (-2)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch .empty (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)))]⟩),
(.side 0 20 false (2)),
(.side 0 20 true (-2)),
(.side 15 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch .empty (.branch .leaf .leaf)) .empty)]⟩),
(.side 7 10 false (1)),
(.side 4 14 false (2)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.last 20 (5,false)),
(.last 28 (5,false)),
(.last 20 (5,false)),
(.last 22 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)]⟩),
(.last 20 (5,false)),
(.last 34 (5,false)),
(.last 20 (5,false))])
theorem checked_20_7 : check 64 p_20_7 cert_20_7 = true := by decide +kernel
theorem safe_20_7 : ∀ m, compatible p_20_7 m → WeightedBound 64 m := sound 64 _ cert_20_7 (by decide) checked_20_7
def p_20_8 := refine p_20 (5,true) (some ⟨false,false,2⟩)
def cert_20_8 : Tree := (.side 0 16 false (2))
theorem checked_20_8 : check 64 p_20_8 cert_20_8 = true := by decide +kernel
theorem safe_20_8 : ∀ m, compatible p_20_8 m → WeightedBound 64 m := sound 64 _ cert_20_8 (by decide) checked_20_8
def p_20_9 := refine p_20 (5,true) (some ⟨false,true,2⟩)
def cert_20_9 : Tree := (split 18 (2,true) 6 #[
(.side 3 16 false (2)),
(.side 4 18 false (2)),
(.side 5 14 false (2)),
(.side 6 16 false (2)),
(.last 21 (5,false)),
(.last 22 (5,false)),
(.side 11 8 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,2)],[(true,2)],[],[],[(false,4)],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,2),(3,8),(3,9),(10,6),(3,11),(7,6),(7,8),(7,8)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty))),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch .empty (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)))]⟩),
(.side 0 22 false (2)),
(.side 0 22 true (-2)),
(.side 15 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch .leaf (.branch .leaf .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch .empty (.branch .leaf .leaf)) .empty)]⟩),
(.side 7 12 false (1)),
(.side 4 16 false (2)),
(.side 7 12 false (1)),
(.side 6 14 false (2)),
(.last 22 (5,false)),
(.last 34 (5,false)),
(.last 22 (5,false)),
(.last 24 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)]⟩),
(.last 21 (5,false)),
(.last 21 (5,false)),
(.last 21 (5,false))])
theorem checked_20_9 : check 64 p_20_9 cert_20_9 = true := by decide +kernel
theorem safe_20_9 : ∀ m, compatible p_20_9 m → WeightedBound 64 m := sound 64 _ cert_20_9 (by decide) checked_20_9
def p_20_10 := refine p_20 (5,true) (some ⟨true,false,2⟩)
def cert_20_10 : Tree := (split 18 (2,true) 6 #[
(.side 3 16 false (2)),
(.side 2 22 false (2)),
(.side 5 14 false (2)),
(.side 6 24 false (2)),
(.last 21 (5,false)),
(.last 24 (5,false)),
(.side 11 8 false (0)),
(.last 28 (5,false)),
(.side 0 22 false (2)),
(.side 18 24 true (-2)),
(.side 15 6 false (-2)),
(.side 6 18 false (2)),
(.side 7 12 false (1)),
(.side 7 22 false (1)),
(.side 7 12 false (1)),
(.side 6 16 false (2)),
(.last 22 (5,false)),
(.last 20 (5,false)),
(.last 22 (5,false)),
(.last 26 (5,false)),
(.last 21 (5,false)),
(.last 19 (5,false)),
(.last 21 (5,false)),
(.last 19 (5,false))])
theorem checked_20_10 : check 64 p_20_10 cert_20_10 = true := by decide +kernel
theorem safe_20_10 : ∀ m, compatible p_20_10 m → WeightedBound 64 m := sound 64 _ cert_20_10 (by decide) checked_20_10
def p_20_11 := refine p_20 (5,true) (some ⟨true,true,2⟩)
def cert_20_11 : Tree := (.side 7 12 false (1))
theorem checked_20_11 : check 64 p_20_11 cert_20_11 = true := by decide +kernel
theorem safe_20_11 : ∀ m, compatible p_20_11 m → WeightedBound 64 m := sound 64 _ cert_20_11 (by decide) checked_20_11
def p_20_12 := refine p_20 (5,true) (some ⟨false,false,3⟩)
def cert_20_12 : Tree := (split 19 (5,false) 6 #[
(.side 7 16 false (1)),
(.last 22 (2,true)),
(.side 7 14 false (1)),
(.last 22 (2,true)),
(.side 7 21 false (1)),
(.side 7 22 false (1)),
(.last 25 (2,true)),
(.side 6 20 false (2)),
(.last 20 (2,true)),
(.side 6 22 false (2)),
(.last 20 (2,true)),
(.side 2 18 false (2)),
(.side 8 12 false (0)),
(.side 7 24 false (1)),
(.side 8 12 false (0)),
(.side 4 16 false (2)),
(.side 21 2 false (-5)),
(.side 18 2 true (-3)),
(.side 21 2 false (-5)),
(.side 8 14 false (0)),
(.side 14 6 false (-2)),
(.side 41 1 true (1)),
(.side 14 6 false (-2)),
(.side 6 18 false (2))])
theorem checked_20_12 : check 64 p_20_12 cert_20_12 = true := by decide +kernel
theorem safe_20_12 : ∀ m, compatible p_20_12 m → WeightedBound 64 m := sound 64 _ cert_20_12 (by decide) checked_20_12
def p_20_13 := refine p_20 (5,true) (some ⟨false,true,3⟩)
def cert_20_13 : Tree := (.side 9 6 true (-2))
theorem checked_20_13 : check 64 p_20_13 cert_20_13 = true := by decide +kernel
theorem safe_20_13 : ∀ m, compatible p_20_13 m → WeightedBound 64 m := sound 64 _ cert_20_13 (by decide) checked_20_13
def p_20_14 := refine p_20 (5,true) (some ⟨true,false,3⟩)
def cert_20_14 : Tree := (.side 9 6 false (0))
theorem checked_20_14 : check 64 p_20_14 cert_20_14 = true := by decide +kernel
theorem safe_20_14 : ∀ m, compatible p_20_14 m → WeightedBound 64 m := sound 64 _ cert_20_14 (by decide) checked_20_14
def p_20_15 := refine p_20 (5,true) (some ⟨true,true,3⟩)
def cert_20_15 : Tree := (.side 7 10 false (1))
theorem checked_20_15 : check 64 p_20_15 cert_20_15 = true := by decide +kernel
theorem safe_20_15 : ∀ m, compatible p_20_15 m → WeightedBound 64 m := sound 64 _ cert_20_15 (by decide) checked_20_15
def p_20_16 := refine p_20 (5,true) (some ⟨false,false,4⟩)
def cert_20_16 : Tree := (split 16 (5,false) 6 #[
(.side 0 17 false (2)),
(.side 0 17 false (2)),
(.side 7 15 false (1)),
(.side 6 18 false (2)),
(.side 7 15 false (1)),
(.side 7 15 false (1)),
(.last 18 (2,true)),
(.side 1 16 false (2)),
(.side 0 18 false (2)),
(.side 0 18 false (2)),
(.last 20 (2,true)),
(.side 7 14 false (1)),
(.side 8 14 false (0)),
(.side 9 28 false (0)),
(.side 9 8 false (0)),
(.side 7 12 false (1)),
(.side 15 2 false (-3)),
(.side 15 2 true (-4)),
(.side 15 2 false (-3)),
(.side 13 4 false (-1)),
(.side 16 1 false (-4)),
(.side 32 1 true (0)),
(.side 16 1 false (-4)),
(.side 23 6 false (-3))])
theorem checked_20_16 : check 64 p_20_16 cert_20_16 = true := by decide +kernel
theorem safe_20_16 : ∀ m, compatible p_20_16 m → WeightedBound 64 m := sound 64 _ cert_20_16 (by decide) checked_20_16
def p_20_17 := refine p_20 (5,true) (some ⟨false,true,4⟩)
def cert_20_17 : Tree := (split 16 (5,false) 6 #[
(.side 0 17 false (2)),
(.side 10 53 true (-2)),
(.side 7 15 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.side 7 15 false (1)),
(.last 18 (2,true)),
(.last 18 (2,true)),
(.last 18 (2,true)),
(.side 0 18 false (2)),
(.last 20 (2,true)),
(.last 20 (2,true)),
(.side 7 14 false (1)),
(.side 8 14 false (0)),
(.side 9 8 true (-2)),
(.side 9 8 false (0)),
(.side 7 12 false (1)),
(.side 15 2 false (-1)),
(.side 15 2 true (-2)),
(.side 15 2 false (-1)),
(.side 13 4 true (-2)),
(.side 16 1 false (-2)),
(.side 30 1 true (2)),
(.side 16 1 false (-2)),
(.side 34 1 true (2))])
theorem checked_20_17 : check 64 p_20_17 cert_20_17 = true := by decide +kernel
theorem safe_20_17 : ∀ m, compatible p_20_17 m → WeightedBound 64 m := sound 64 _ cert_20_17 (by decide) checked_20_17
def p_20_18 := refine p_20 (5,true) (some ⟨true,false,4⟩)
def cert_20_18 : Tree := (split 16 (5,false) 6 #[
(.side 0 17 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.side 7 15 false (1)),
(.side 28 8 false (-3)),
(.side 7 15 false (1)),
(.last 18 (2,true)),
(.last 18 (2,true)),
(.last 18 (2,true)),
(.side 0 18 false (2)),
(.last 20 (2,true)),
(.last 20 (2,true)),
(.side 7 14 false (1)),
(.side 8 14 false (0)),
(.side 9 8 false (0)),
(.side 9 8 false (0)),
(.side 7 12 false (1)),
(.side 15 2 false (-3)),
(.side 15 2 true (-4)),
(.side 15 2 false (-3)),
(.side 13 4 false (-1)),
(.side 16 1 false (-4)),
(.side 14 4 true (-4)),
(.side 16 1 false (-4)),
(.side 15 6 false (-2))])
theorem checked_20_18 : check 64 p_20_18 cert_20_18 = true := by decide +kernel
theorem safe_20_18 : ∀ m, compatible p_20_18 m → WeightedBound 64 m := sound 64 _ cert_20_18 (by decide) checked_20_18
def p_20_19 := refine p_20 (5,true) (some ⟨true,true,4⟩)
def cert_20_19 : Tree := (.side 13 2 true (-2))
theorem checked_20_19 : check 64 p_20_19 cert_20_19 = true := by decide +kernel
theorem safe_20_19 : ∀ m, compatible p_20_19 m → WeightedBound 64 m := sound 64 _ cert_20_19 (by decide) checked_20_19
def p_20_20 := refine p_20 (5,true) (some ⟨false,false,5⟩)
def cert_20_20 : Tree := (split 15 (5,false) 6 #[
(.side 0 16 false (2)),
(.last 18 (2,true)),
(.side 7 14 false (1)),
(.last 18 (2,true)),
(.side 7 14 false (1)),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.side 1 15 false (2)),
(.side 0 17 false (2)),
(.side 0 17 false (2)),
(.last 19 (2,true)),
(.side 7 13 false (1)),
(.side 8 13 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.side 9 7 false (0)),
(.side 7 11 false (1)),
(.side 15 2 false (-3)),
(.side 15 2 true (-3)),
(.side 15 2 false (-3)),
(.side 13 3 false (-1)),
(.side 15 1 false (-3)),
(.side 25 1 true (1)),
(.side 15 1 false (-3)),
(.side 48 1 true (-6))])
theorem checked_20_20 : check 64 p_20_20 cert_20_20 = true := by decide +kernel
theorem safe_20_20 : ∀ m, compatible p_20_20 m → WeightedBound 64 m := sound 64 _ cert_20_20 (by decide) checked_20_20
def p_20_21 := refine p_20 (5,true) (some ⟨false,true,5⟩)
def cert_20_21 : Tree := (split 15 (5,false) 6 #[
(.last 18 (2,true)),
(.side 7 10 true (-2)),
(.side 10 6 true (-2)),
(.side 5 11 false (2)),
(.side 7 14 false (1)),
(.last 21 (2,true)),
(.last 17 (2,true)),
(.side 11 34 true (-2)),
(.side 0 17 false (2)),
(.last 16 (2,true)),
(.last 19 (2,true)),
(.last 16 (2,true)),
(.side 8 13 false (0)),
(.side 8 8 true (-2)),
(.side 9 7 false (0)),
(.side 7 9 false (1)),
(.side 15 2 false (-1)),
(.side 17 2 true (-2)),
(.side 15 2 false (-1)),
(.side 13 7 false (0)),
(.side 15 1 false (-1)),
(.side 19 1 true (3)),
(.side 15 1 false (-1)),
(.side 19 1 true (3))])
theorem checked_20_21 : check 64 p_20_21 cert_20_21 = true := by decide +kernel
theorem safe_20_21 : ∀ m, compatible p_20_21 m → WeightedBound 64 m := sound 64 _ cert_20_21 (by decide) checked_20_21
def p_20_22 := refine p_20 (5,true) (some ⟨true,false,5⟩)
def cert_20_22 : Tree := (split 15 (5,false) 6 #[
(.last 18 (2,true)),
(.side 7 12 false (1)),
(.side 10 6 false (0)),
(.side 3 13 false (2)),
(.side 7 14 false (1)),
(.last 20 (2,true)),
(.last 17 (2,true)),
(.last 20 (2,true)),
(.side 0 17 false (2)),
(.last 16 (2,true)),
(.last 19 (2,true)),
(.last 16 (2,true)),
(.side 8 13 false (0)),
(.side 8 8 false (0)),
(.side 9 7 false (0)),
(.side 7 9 false (1)),
(.side 15 2 false (-3)),
(.side 17 2 true (-4)),
(.side 15 2 false (-3)),
(.side 13 7 false (-1)),
(.side 15 1 false (-3)),
(.side 14 2 true (-3)),
(.side 15 1 false (-3)),
(.side 14 3 false (-2))])
theorem checked_20_22 : check 64 p_20_22 cert_20_22 = true := by decide +kernel
theorem safe_20_22 : ∀ m, compatible p_20_22 m → WeightedBound 64 m := sound 64 _ cert_20_22 (by decide) checked_20_22
def p_20_23 := refine p_20 (5,true) (some ⟨true,true,5⟩)
def cert_20_23 : Tree := (split 15 (5,false) 6 #[
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.side 7 17 false (1)),
(.last 21 (2,true)),
(.last 21 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.side 8 8 false (0)),
(.side 7 12 false (1)),
(.side 8 8 false (0)),
(.side 6 10 false (2)),
(.side 17 2 false (-3)),
(.side 12 4 true (-2)),
(.side 17 2 false (-3)),
(.side 13 8 false (0)),
(.side 14 2 true (-2)),
(.side 19 1 true (3)),
(.side 19 3 true (1)),
(.side 19 1 true (3))])
theorem checked_20_23 : check 64 p_20_23 cert_20_23 = true := by decide +kernel
theorem safe_20_23 : ∀ m, compatible p_20_23 m → WeightedBound 64 m := sound 64 _ cert_20_23 (by decide) checked_20_23
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 64 m := by
  apply split_safe 64 p_20 14 (5,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_20_0 | exact safe_20_1 | exact safe_20_2 | exact safe_20_3 | exact safe_20_4 | exact safe_20_5 | exact safe_20_6 | exact safe_20_7 | exact safe_20_8 | exact safe_20_9 | exact safe_20_10 | exact safe_20_11 | exact safe_20_12 | exact safe_20_13 | exact safe_20_14 | exact safe_20_15 | exact safe_20_16 | exact safe_20_17 | exact safe_20_18 | exact safe_20_19 | exact safe_20_20 | exact safe_20_21 | exact safe_20_22 | exact safe_20_23
def p_21 := refine parent (4,false) (some ⟨false,true,5⟩)
def p_21_0 := refine p_21 (5,true) (some ⟨false,false,0⟩)
def cert_21_0 : Tree := (split 17 (2,true) 6 #[
(.side 6 16 false (2)),
(.side 20 18 false (3)),
(.side 6 14 false (2)),
(.side 20 16 false (3)),
(.last 58 (5,false)),
(.last 20 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)))]⟩),
(.last 20 (5,false)),
(.side 0 22 false (2)),
(.side 0 50 true (-4)),
(.side 18 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 6 12 false (2)),
(.side 6 16 false (2)),
(.side 6 12 false (2)),
(.side 6 14 false (2)),
(.side 19 7 false (-1)),
(.last 55 (5,false)),
(.side 19 7 false (-1)),
(.side 19 9 false (1)),
(.side 3 16 false (2)),
(.last 48 (5,false)),
(.side 3 16 false (2)),
(.side 6 18 false (2))])
theorem checked_21_0 : check 64 p_21_0 cert_21_0 = true := by decide +kernel
theorem safe_21_0 : ∀ m, compatible p_21_0 m → WeightedBound 64 m := sound 64 _ cert_21_0 (by decide) checked_21_0
def p_21_1 := refine p_21 (5,true) (some ⟨false,true,0⟩)
def cert_21_1 : Tree := (.side 15 11 true (-1))
theorem checked_21_1 : check 64 p_21_1 cert_21_1 = true := by decide +kernel
theorem safe_21_1 : ∀ m, compatible p_21_1 m → WeightedBound 64 m := sound 64 _ cert_21_1 (by decide) checked_21_1
def p_21_2 := refine p_21 (5,true) (some ⟨true,false,0⟩)
def cert_21_2 : Tree := (split 28 (5,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))]⟩),
(.side 0 29 true (-2)),
(.side 25 4 true (1)),
(.side 10 35 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))]⟩),
(.side 15 22 true (-1)),
(.last 30 (2,true)),
(.side 1 28 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))]⟩),
(.side 0 30 true (-2)),
(.last 32 (2,true)),
(.side 15 21 true (-1)),
(.side 25 5 true (1)),
(.side 25 5 true (1)),
(.side 20 10 true (0)),
(.side 15 19 true (-1)),
(.side 27 2 true (3)),
(.side 27 2 true (3)),
(.side 23 6 true (1)),
(.side 27 2 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.side 28 1 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf)))]⟩),
(.side 28 1 true (4))])
theorem checked_21_2 : check 64 p_21_2 cert_21_2 = true := by decide +kernel
theorem safe_21_2 : ∀ m, compatible p_21_2 m → WeightedBound 64 m := sound 64 _ cert_21_2 (by decide) checked_21_2
def p_21_3 := refine p_21 (5,true) (some ⟨true,true,0⟩)
def cert_21_3 : Tree := (.side 7 14 false (2))
theorem checked_21_3 : check 64 p_21_3 cert_21_3 = true := by decide +kernel
theorem safe_21_3 : ∀ m, compatible p_21_3 m → WeightedBound 64 m := sound 64 _ cert_21_3 (by decide) checked_21_3
def p_21_4 := refine p_21 (5,true) (some ⟨false,false,1⟩)
def cert_21_4 : Tree := (.side 1 14 false (2))
theorem checked_21_4 : check 64 p_21_4 cert_21_4 = true := by decide +kernel
theorem safe_21_4 : ∀ m, compatible p_21_4 m → WeightedBound 64 m := sound 64 _ cert_21_4 (by decide) checked_21_4
def p_21_5 := refine p_21 (5,true) (some ⟨false,true,1⟩)
def cert_21_5 : Tree := (split 34 (5,false) 6 #[
(.side 0 35 true (-2)),
(.side 0 35 true (-2)),
(.side 32 4 true (4)),
(.side 28 23 true (2)),
(.side 19 16 true (1)),
(.side 19 16 true (1)),
(.last 36 (2,true)),
(.side 1 34 true (-2)),
(.side 0 36 true (-2)),
(.side 0 36 true (-2)),
(.last 38 (2,true)),
(.side 20 15 true (1)),
(.side 32 5 true (4)),
(.side 32 5 true (4)),
(.side 15 22 true (1)),
(.side 22 13 true (1)),
(.side 33 2 true (5)),
(.side 33 2 true (5)),
(.side 17 18 true (1)),
(.side 33 2 true (5)),
(.side 107 21 false (1)),
(.side 34 1 true (6)),
(.side 112 1 false (14)),
(.side 34 1 true (6))])
theorem checked_21_5 : check 64 p_21_5 cert_21_5 = true := by decide +kernel
theorem safe_21_5 : ∀ m, compatible p_21_5 m → WeightedBound 64 m := sound 64 _ cert_21_5 (by decide) checked_21_5
def p_21_6 := refine p_21 (5,true) (some ⟨true,false,1⟩)
def cert_21_6 : Tree := (split 16 (2,true) 6 #[
(.side 3 14 false (2)),
(.side 4 16 false (2)),
(.side 5 12 false (2)),
(.side 6 14 false (2)),
(.last 29 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,6)],[(true,6)],[(false,3),(false,5)],[]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty) .empty),.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty) .empty)]⟩),
(.side 11 6 true (-1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty)]⟩),
(.side 0 20 false (2)),
(.side 0 20 true (-2)),
(.side 15 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 7 10 false (1)),
(.side 4 14 false (2)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.side 18 5 false (-2)),
(.last 28 (5,false)),
(.side 18 5 false (-2)),
(.side 18 7 false (0)),
(.side 21 3 false (-1)),
(.last 23 (5,false)),
(.side 21 3 false (-1)),
(.last 31 (5,false))])
theorem checked_21_6 : check 64 p_21_6 cert_21_6 = true := by decide +kernel
theorem safe_21_6 : ∀ m, compatible p_21_6 m → WeightedBound 64 m := sound 64 _ cert_21_6 (by decide) checked_21_6
def p_21_7 := refine p_21 (5,true) (some ⟨true,true,1⟩)
def cert_21_7 : Tree := (.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty)]⟩)
theorem checked_21_7 : check 64 p_21_7 cert_21_7 = true := by decide +kernel
theorem safe_21_7 : ∀ m, compatible p_21_7 m → WeightedBound 64 m := sound 64 _ cert_21_7 (by decide) checked_21_7
def p_21_8 := refine p_21 (5,true) (some ⟨false,false,2⟩)
def cert_21_8 : Tree := (.side 7 12 false (1))
theorem checked_21_8 : check 64 p_21_8 cert_21_8 = true := by decide +kernel
theorem safe_21_8 : ∀ m, compatible p_21_8 m → WeightedBound 64 m := sound 64 _ cert_21_8 (by decide) checked_21_8
def p_21_9 := refine p_21 (5,true) (some ⟨false,true,2⟩)
def cert_21_9 : Tree := (split 15 (2,true) 6 #[
(.side 7 20 false (2)),
(.side 0 28 true (-2)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty)]⟩),
(.side 3 13 true (-2)),
(.side 7 18 false (1)),
(.last 18 (5,false)),
(.side 0 30 true (-2)),
(.last 18 (5,false)),
(.side 6 18 false (2)),
(.side 0 18 true (-2)),
(.side 20 6 false (0)),
(.side 2 15 true (-2)),
(.side 0 22 true (-2)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2),(false,5)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty)]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch .empty (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 16 11 true (-1)),
(.last 17 (5,false)),
(.side 0 20 true (-2)),
(.side 0 22 true (-2)),
(.last 22 (5,false)),
(.last 16 (5,false)),
(.side 0 18 true (-2)),
(.last 16 (5,false)),
(.last 37 (5,false))])
theorem checked_21_9 : check 64 p_21_9 cert_21_9 = true := by decide +kernel
theorem safe_21_9 : ∀ m, compatible p_21_9 m → WeightedBound 64 m := sound 64 _ cert_21_9 (by decide) checked_21_9
def p_21_10 := refine p_21 (5,true) (some ⟨true,false,2⟩)
def cert_21_10 : Tree := (.side 7 12 false (1))
theorem checked_21_10 : check 64 p_21_10 cert_21_10 = true := by decide +kernel
theorem safe_21_10 : ∀ m, compatible p_21_10 m → WeightedBound 64 m := sound 64 _ cert_21_10 (by decide) checked_21_10
def p_21_11 := refine p_21 (5,true) (some ⟨true,true,2⟩)
def cert_21_11 : Tree := (split 15 (2,true) 6 #[
(.side 7 16 false (1)),
(.side 18 18 false (3)),
(.side 7 14 false (1)),
(.side 18 16 false (3)),
(.last 34 (5,false)),
(.last 18 (5,false)),
(.side 16 17 true (0)),
(.last 18 (5,false)),
(.side 7 14 false (1)),
(.side 0 48 true (-4)),
(.side 7 14 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 7 12 false (1)),
(.side 7 16 false (2)),
(.side 7 12 false (1)),
(.side 7 14 false (2)),
(.side 7 20 false (1)),
(.last 49 (5,false)),
(.side 12 4 true (-1)),
(.side 12 6 true (-1)),
(.side 7 18 false (1)),
(.last 42 (5,false)),
(.side 14 2 true (0)),
(.last 40 (5,false))])
theorem checked_21_11 : check 64 p_21_11 cert_21_11 = true := by decide +kernel
theorem safe_21_11 : ∀ m, compatible p_21_11 m → WeightedBound 64 m := sound 64 _ cert_21_11 (by decide) checked_21_11
def p_21_12 := refine p_21 (5,true) (some ⟨false,false,3⟩)
def cert_21_12 : Tree := (.side 7 10 false (1))
theorem checked_21_12 : check 64 p_21_12 cert_21_12 = true := by decide +kernel
theorem safe_21_12 : ∀ m, compatible p_21_12 m → WeightedBound 64 m := sound 64 _ cert_21_12 (by decide) checked_21_12
def p_21_13 := refine p_21 (5,true) (some ⟨false,true,3⟩)
def cert_21_13 : Tree := (split 33 (5,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))]⟩),
(.side 0 34 true (-2)),
(.side 30 4 true (2)),
(.side 8 42 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))]⟩),
(.side 15 25 true (-1)),
(.last 35 (2,true)),
(.side 1 33 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))]⟩),
(.side 0 35 true (-2)),
(.last 37 (2,true)),
(.side 15 24 true (-1)),
(.side 29 5 true (2)),
(.side 29 5 true (2)),
(.side 23 11 true (0)),
(.side 15 22 true (-1)),
(.side 32 2 true (4)),
(.side 32 2 true (4)),
(.side 27 7 true (1)),
(.side 32 2 true (4)),
(.side 28 8 true (2)),
(.side 33 1 true (5)),
(.side 8 29 true (-2)),
(.side 33 1 true (5))])
theorem checked_21_13 : check 64 p_21_13 cert_21_13 = true := by decide +kernel
theorem safe_21_13 : ∀ m, compatible p_21_13 m → WeightedBound 64 m := sound 64 _ cert_21_13 (by decide) checked_21_13
def p_21_14 := refine p_21 (5,true) (some ⟨true,false,3⟩)
def cert_21_14 : Tree := (.side 7 10 false (1))
theorem checked_21_14 : check 64 p_21_14 cert_21_14 = true := by decide +kernel
theorem safe_21_14 : ∀ m, compatible p_21_14 m → WeightedBound 64 m := sound 64 _ cert_21_14 (by decide) checked_21_14
def p_21_15 := refine p_21 (5,true) (some ⟨true,true,3⟩)
def cert_21_15 : Tree := (.side 7 12 false (1))
theorem checked_21_15 : check 64 p_21_15 cert_21_15 = true := by decide +kernel
theorem safe_21_15 : ∀ m, compatible p_21_15 m → WeightedBound 64 m := sound 64 _ cert_21_15 (by decide) checked_21_15
def p_21_16 := refine p_21 (5,true) (some ⟨false,false,4⟩)
def cert_21_16 : Tree := (split 16 (5,false) 6 #[
(.last 19 (2,true)),
(.side 17 13 true (-1)),
(.side 29 4 true (1)),
(.side 7 16 false (2)),
(.side 1 16 false (2)),
(.side 21 18 true (1)),
(.last 18 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))]⟩),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.side 7 12 false (1)),
(.side 33 5 true (1)),
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 15 2 true (-1)),
(.side 25 2 true (1)),
(.side 13 4 true (-1)),
(.side 12 6 true (-1)),
(.side 20 1 false (-2)),
(.side 22 1 true (2)),
(.side 20 1 false (-2)),
(.side 36 1 true (0))])
theorem checked_21_16 : check 64 p_21_16 cert_21_16 = true := by decide +kernel
theorem safe_21_16 : ∀ m, compatible p_21_16 m → WeightedBound 64 m := sound 64 _ cert_21_16 (by decide) checked_21_16
def p_21_17 := refine p_21 (5,true) (some ⟨false,true,4⟩)
def cert_21_17 : Tree := (split 22 (5,false) 6 #[
(.side 0 23 true (-2)),
(.side 0 23 true (-2)),
(.side 21 4 true (3)),
(.side 12 27 true (-1)),
(.side 15 18 true (0)),
(.side 15 18 true (0)),
(.last 24 (2,true)),
(.side 1 22 true (-2)),
(.side 0 24 true (-2)),
(.side 0 24 true (-2)),
(.last 26 (2,true)),
(.side 15 17 true (0)),
(.side 21 5 true (2)),
(.side 21 5 true (3)),
(.side 18 8 true (1)),
(.side 15 15 true (0)),
(.side 21 2 true (3)),
(.side 21 2 true (3)),
(.side 19 4 true (1)),
(.side 21 2 true (3)),
(.side 30 1 false (0)),
(.side 22 1 true (4)),
(.side 48 1 false (6)),
(.side 22 1 true (4))])
theorem checked_21_17 : check 64 p_21_17 cert_21_17 = true := by decide +kernel
theorem safe_21_17 : ∀ m, compatible p_21_17 m → WeightedBound 64 m := sound 64 _ cert_21_17 (by decide) checked_21_17
def p_21_18 := refine p_21 (5,true) (some ⟨true,false,4⟩)
def cert_21_18 : Tree := (.side 13 2 true (-1))
theorem checked_21_18 : check 64 p_21_18 cert_21_18 = true := by decide +kernel
theorem safe_21_18 : ∀ m, compatible p_21_18 m → WeightedBound 64 m := sound 64 _ cert_21_18 (by decide) checked_21_18
def p_21_19 := refine p_21 (5,true) (some ⟨true,true,4⟩)
def cert_21_19 : Tree := (.side 12 4 true (-1))
theorem checked_21_19 : check 64 p_21_19 cert_21_19 = true := by decide +kernel
theorem safe_21_19 : ∀ m, compatible p_21_19 m → WeightedBound 64 m := sound 64 _ cert_21_19 (by decide) checked_21_19
def p_21_20 := refine p_21 (5,true) (some ⟨false,false,5⟩)
def cert_21_20 : Tree := (split 15 (5,false) 6 #[
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))]⟩),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))]⟩),
(.side 7 17 false (1)),
(.last 17 (2,true)),
(.last 22 (2,true)),
(.last 17 (2,true)),
(.last 16 (2,true)),
(.last 19 (2,true)),
(.last 16 (2,true)),
(.side 2 14 false (2)),
(.side 8 8 false (0)),
(.side 29 5 true (1)),
(.side 8 8 false (0)),
(.side 4 12 false (2)),
(.side 19 2 true (-4)),
(.side 21 2 true (1)),
(.side 17 3 false (-2)),
(.side 21 2 true (1)),
(.side 17 1 false (-3)),
(.side 21 1 true (1)),
(.side 17 1 false (-3)),
(.side 32 1 true (-4))])
theorem checked_21_20 : check 64 p_21_20 cert_21_20 = true := by decide +kernel
theorem safe_21_20 : ∀ m, compatible p_21_20 m → WeightedBound 64 m := sound 64 _ cert_21_20 (by decide) checked_21_20
def p_21_21 := refine p_21 (5,true) (some ⟨false,true,5⟩)
def cert_21_21 : Tree := (split 17 (5,false) 6 #[
(.side 0 18 true (-2)),
(.side 0 18 true (-2)),
(.side 17 4 true (2)),
(.side 14 20 true (0)),
(.side 15 15 true (0)),
(.side 15 15 true (1)),
(.last 19 (2,true)),
(.side 1 17 true (-2)),
(.side 0 19 true (-2)),
(.side 0 19 true (-2)),
(.last 21 (2,true)),
(.side 15 14 true (1)),
(.side 17 5 true (1)),
(.side 17 5 true (3)),
(.side 16 7 true (1)),
(.side 15 12 true (1)),
(.side 17 2 true (2)),
(.side 17 2 true (3)),
(.side 16 3 true (2)),
(.side 17 2 true (3)),
(.side 23 1 false (-1)),
(.side 17 1 true (3)),
(.side 28 1 false (4)),
(.side 17 1 true (3))])
theorem checked_21_21 : check 64 p_21_21 cert_21_21 = true := by decide +kernel
theorem safe_21_21 : ∀ m, compatible p_21_21 m → WeightedBound 64 m := sound 64 _ cert_21_21 (by decide) checked_21_21
def p_21_22 := refine p_21 (5,true) (some ⟨true,false,5⟩)
def cert_21_22 : Tree := (split 15 (5,false) 6 #[
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.side 7 18 false (1)),
(.side 16 22 true (0)),
(.last 22 (2,true)),
(.side 1 28 true (-2)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.side 8 8 false (0)),
(.side 7 12 false (1)),
(.side 8 8 false (0)),
(.side 6 10 false (2)),
(.side 19 2 true (-4)),
(.side 12 4 true (-1)),
(.side 17 3 false (-2)),
(.side 17 5 false (-1)),
(.side 17 1 false (-3)),
(.side 14 2 true (-1)),
(.side 17 1 false (-3)),
(.side 17 3 false (-1))])
theorem checked_21_22 : check 64 p_21_22 cert_21_22 = true := by decide +kernel
theorem safe_21_22 : ∀ m, compatible p_21_22 m → WeightedBound 64 m := sound 64 _ cert_21_22 (by decide) checked_21_22
def p_21_23 := refine p_21 (5,true) (some ⟨true,true,5⟩)
def cert_21_23 : Tree := (split 17 (5,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.side 16 5 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.last 18 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.last 18 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.side 17 5 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.side 12 8 true (-1)),
(.side 17 2 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))]⟩),
(.side 17 2 true (3)),
(.side 16 2 true (2)),
(.side 17 1 true (3)),
(.side 15 3 true (1)),
(.side 17 1 true (3))])
theorem checked_21_23 : check 64 p_21_23 cert_21_23 = true := by decide +kernel
theorem safe_21_23 : ∀ m, compatible p_21_23 m → WeightedBound 64 m := sound 64 _ cert_21_23 (by decide) checked_21_23
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 64 m := by
  apply split_safe 64 p_21 14 (5,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_21_0 | exact safe_21_1 | exact safe_21_2 | exact safe_21_3 | exact safe_21_4 | exact safe_21_5 | exact safe_21_6 | exact safe_21_7 | exact safe_21_8 | exact safe_21_9 | exact safe_21_10 | exact safe_21_11 | exact safe_21_12 | exact safe_21_13 | exact safe_21_14 | exact safe_21_15 | exact safe_21_16 | exact safe_21_17 | exact safe_21_18 | exact safe_21_19 | exact safe_21_20 | exact safe_21_21 | exact safe_21_22 | exact safe_21_23
def p_22 := refine parent (4,false) (some ⟨true,false,5⟩)
def p_22_0 := refine p_22 (5,true) (some ⟨false,false,0⟩)
def cert_22_0 : Tree := (split 17 (2,true) 6 #[
(.side 3 15 false (2)),
(.side 4 17 false (2)),
(.side 5 13 false (2)),
(.side 6 15 false (2)),
(.last 20 (5,false)),
(.last 21 (5,false)),
(.side 11 7 false (0)),
(.side 3 19 false (2)),
(.side 0 21 false (2)),
(.side 0 22 true (-3)),
(.side 15 6 false (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch .empty (.branch .empty (.branch .leaf .leaf)))]⟩),
(.side 7 11 false (1)),
(.side 4 15 false (2)),
(.side 7 11 false (1)),
(.side 6 13 false (2)),
(.last 21 (5,false)),
(.side 7 17 false (1)),
(.last 21 (5,false)),
(.last 23 (5,false)),
(.side 7 15 false (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[],[],[(false,4)],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,2),(3,8),(3,9),(10,6),(3,11),(7,6),(7,8),(7,8)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,4)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .leaf (.branch .empty .leaf)) .empty))),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .leaf) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)]⟩),
(.side 7 15 false (1)),
(.side 6 17 false (2))])
theorem checked_22_0 : check 64 p_22_0 cert_22_0 = true := by decide +kernel
theorem safe_22_0 : ∀ m, compatible p_22_0 m → WeightedBound 64 m := sound 64 _ cert_22_0 (by decide) checked_22_0
def p_22_1 := refine p_22 (5,true) (some ⟨false,true,0⟩)
def cert_22_1 : Tree := (.side 7 9 false (1))
theorem checked_22_1 : check 64 p_22_1 cert_22_1 = true := by decide +kernel
theorem safe_22_1 : ∀ m, compatible p_22_1 m → WeightedBound 64 m := sound 64 _ cert_22_1 (by decide) checked_22_1
def p_22_2 := refine p_22 (5,true) (some ⟨true,false,0⟩)
def cert_22_2 : Tree := (.side 10 5 false (0))
theorem checked_22_2 : check 64 p_22_2 cert_22_2 = true := by decide +kernel
theorem safe_22_2 : ∀ m, compatible p_22_2 m → WeightedBound 64 m := sound 64 _ cert_22_2 (by decide) checked_22_2
def p_22_3 := refine p_22 (5,true) (some ⟨true,true,0⟩)
def cert_22_3 : Tree := (.side 5 10 false (2))
theorem checked_22_3 : check 64 p_22_3 cert_22_3 = true := by decide +kernel
theorem safe_22_3 : ∀ m, compatible p_22_3 m → WeightedBound 64 m := sound 64 _ cert_22_3 (by decide) checked_22_3
def p_22_4 := refine p_22 (5,true) (some ⟨false,false,1⟩)
def cert_22_4 : Tree := (.side 7 13 false (1))
theorem checked_22_4 : check 64 p_22_4 cert_22_4 = true := by decide +kernel
theorem safe_22_4 : ∀ m, compatible p_22_4 m → WeightedBound 64 m := sound 64 _ cert_22_4 (by decide) checked_22_4
def p_22_5 := refine p_22 (5,true) (some ⟨false,true,1⟩)
def cert_22_5 : Tree := (split 18 (5,false) 6 #[
(.last 21 (2,true)),
(.side 7 13 false (1)),
(.side 10 9 false (0)),
(.side 5 14 false (2)),
(.side 7 17 false (1)),
(.side 15 4 true (-2)),
(.last 20 (2,true)),
(.side 11 8 true (-2)),
(.side 0 20 false (2)),
(.last 19 (2,true)),
(.last 22 (2,true)),
(.last 19 (2,true)),
(.side 8 16 false (0)),
(.side 8 11 false (0)),
(.side 9 10 false (0)),
(.side 7 12 false (1)),
(.side 17 2 false (-1)),
(.side 16 3 false (0)),
(.side 17 2 false (-1)),
(.side 16 4 false (0)),
(.side 18 1 false (-2)),
(.side 19 27 true (-1)),
(.side 18 1 false (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))]⟩)])
theorem checked_22_5 : check 64 p_22_5 cert_22_5 = true := by decide +kernel
theorem safe_22_5 : ∀ m, compatible p_22_5 m → WeightedBound 64 m := sound 64 _ cert_22_5 (by decide) checked_22_5
def p_22_6 := refine p_22 (5,true) (some ⟨true,false,1⟩)
def cert_22_6 : Tree := (split 16 (2,true) 6 #[
(.side 7 13 false (1)),
(.side 7 15 false (1)),
(.side 7 11 false (1)),
(.side 6 13 false (2)),
(.last 19 (5,false)),
(.last 20 (5,false)),
(.last 20 (5,false)),
(.last 24 (5,false)),
(.side 0 19 false (2)),
(.side 0 22 true (-3)),
(.side 16 6 false (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch .leaf .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf)))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch .empty (.branch .empty .leaf))]⟩),
(.side 8 9 false (0)),
(.side 7 13 false (1)),
(.side 8 9 false (0)),
(.side 6 11 false (2)),
(.last 19 (5,false)),
(.side 12 5 false (0)),
(.last 19 (5,false)),
(.last 21 (5,false)),
(.side 14 3 false (-2)),
(.last 29 (5,false)),
(.side 14 3 false (-2)),
(.side 11 7 false (0))])
theorem checked_22_6 : check 64 p_22_6 cert_22_6 = true := by decide +kernel
theorem safe_22_6 : ∀ m, compatible p_22_6 m → WeightedBound 64 m := sound 64 _ cert_22_6 (by decide) checked_22_6
def p_22_7 := refine p_22 (5,true) (some ⟨true,true,1⟩)
def cert_22_7 : Tree := (.side 11 4 true (-2))
theorem checked_22_7 : check 64 p_22_7 cert_22_7 = true := by decide +kernel
theorem safe_22_7 : ∀ m, compatible p_22_7 m → WeightedBound 64 m := sound 64 _ cert_22_7 (by decide) checked_22_7
def p_22_8 := refine p_22 (5,true) (some ⟨false,false,2⟩)
def cert_22_8 : Tree := (.side 0 16 false (2))
theorem checked_22_8 : check 64 p_22_8 cert_22_8 = true := by decide +kernel
theorem safe_22_8 : ∀ m, compatible p_22_8 m → WeightedBound 64 m := sound 64 _ cert_22_8 (by decide) checked_22_8
def p_22_9 := refine p_22 (5,true) (some ⟨false,true,2⟩)
def cert_22_9 : Tree := (split 15 (2,true) 6 #[
(.side 3 16 false (2)),
(.side 7 10 true (-2)),
(.side 10 6 true (-2)),
(.side 5 11 false (2)),
(.side 7 14 false (1)),
(.last 19 (5,false)),
(.last 21 (5,false)),
(.last 28 (5,false)),
(.side 0 17 false (2)),
(.side 0 20 true (-2)),
(.side 15 6 false (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf)))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch .empty (.branch .empty .leaf))]⟩),
(.last 20 (5,false)),
(.side 8 8 true (-2)),
(.side 9 7 false (0)),
(.side 7 9 false (1)),
(.last 17 (5,false)),
(.last 18 (5,false)),
(.last 17 (5,false)),
(.last 19 (5,false)),
(.last 16 (5,false)),
(.side 0 20 true (-2)),
(.last 16 (5,false)),
(.last 47 (5,false))])
theorem checked_22_9 : check 64 p_22_9 cert_22_9 = true := by decide +kernel
theorem safe_22_9 : ∀ m, compatible p_22_9 m → WeightedBound 64 m := sound 64 _ cert_22_9 (by decide) checked_22_9
def p_22_10 := refine p_22 (5,true) (some ⟨true,false,2⟩)
def cert_22_10 : Tree := (split 18 (2,true) 6 #[
(.side 3 16 false (2)),
(.side 4 18 false (2)),
(.side 5 14 false (2)),
(.side 6 16 false (2)),
(.last 21 (5,false)),
(.last 22 (5,false)),
(.side 11 8 false (0)),
(.side 11 18 false (0)),
(.side 0 22 false (2)),
(.side 0 24 true (-4)),
(.side 15 6 false (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch .empty (.branch .empty (.branch .leaf .leaf)))]⟩),
(.side 7 12 false (1)),
(.side 4 16 false (2)),
(.side 7 12 false (1)),
(.side 6 14 false (2)),
(.last 22 (5,false)),
(.last 25 (5,false)),
(.last 22 (5,false)),
(.last 24 (5,false)),
(.last 21 (5,false)),
(.side 2 18 false (2)),
(.last 21 (5,false)),
(.side 18 2 true (-2))])
theorem checked_22_10 : check 64 p_22_10 cert_22_10 = true := by decide +kernel
theorem safe_22_10 : ∀ m, compatible p_22_10 m → WeightedBound 64 m := sound 64 _ cert_22_10 (by decide) checked_22_10
def p_22_11 := refine p_22 (5,true) (some ⟨true,true,2⟩)
def cert_22_11 : Tree := (split 15 (2,true) 6 #[
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.last 18 (5,false)),
(.last 19 (5,false)),
(.last 19 (5,false)),
(.last 28 (5,false)),
(.side 0 18 false (2)),
(.side 0 20 true (-2)),
(.side 15 6 false (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch .empty (.branch .empty (.branch .leaf .leaf)))]⟩),
(.side 8 8 false (0)),
(.side 7 12 false (1)),
(.side 8 8 false (0)),
(.side 6 10 false (2)),
(.last 18 (5,false)),
(.side 12 4 true (-2)),
(.last 18 (5,false)),
(.last 20 (5,false)),
(.side 7 14 false (1)),
(.last 46 (5,false)),
(.side 14 2 true (-2)),
(.last 42 (5,false))])
theorem checked_22_11 : check 64 p_22_11 cert_22_11 = true := by decide +kernel
theorem safe_22_11 : ∀ m, compatible p_22_11 m → WeightedBound 64 m := sound 64 _ cert_22_11 (by decide) checked_22_11
def p_22_12 := refine p_22 (5,true) (some ⟨false,false,3⟩)
def cert_22_12 : Tree := (split 19 (5,false) 6 #[
(.side 7 16 false (1)),
(.side 7 18 false (1)),
(.side 7 14 false (1)),
(.side 6 16 false (2)),
(.side 7 21 false (1)),
(.side 18 4 true (-3)),
(.last 25 (2,true)),
(.side 8 16 false (0)),
(.last 20 (2,true)),
(.last 20 (2,true)),
(.last 20 (2,true)),
(.last 20 (2,true)),
(.side 8 12 false (0)),
(.side 7 16 false (1)),
(.side 8 12 false (0)),
(.side 6 14 false (2)),
(.side 21 2 false (-5)),
(.side 12 8 false (0)),
(.side 21 2 false (-5)),
(.side 21 4 false (-3)),
(.side 14 6 false (-2)),
(.side 7 16 false (1)),
(.side 14 6 false (-2)),
(.side 7 14 false (1))])
theorem checked_22_12 : check 64 p_22_12 cert_22_12 = true := by decide +kernel
theorem safe_22_12 : ∀ m, compatible p_22_12 m → WeightedBound 64 m := sound 64 _ cert_22_12 (by decide) checked_22_12
def p_22_13 := refine p_22 (5,true) (some ⟨false,true,3⟩)
def cert_22_13 : Tree := (.side 8 7 false (0))
theorem checked_22_13 : check 64 p_22_13 cert_22_13 = true := by decide +kernel
theorem safe_22_13 : ∀ m, compatible p_22_13 m → WeightedBound 64 m := sound 64 _ cert_22_13 (by decide) checked_22_13
def p_22_14 := refine p_22 (5,true) (some ⟨true,false,3⟩)
def cert_22_14 : Tree := (.side 9 6 false (0))
theorem checked_22_14 : check 64 p_22_14 cert_22_14 = true := by decide +kernel
theorem safe_22_14 : ∀ m, compatible p_22_14 m → WeightedBound 64 m := sound 64 _ cert_22_14 (by decide) checked_22_14
def p_22_15 := refine p_22 (5,true) (some ⟨true,true,3⟩)
def cert_22_15 : Tree := (.side 7 8 false (1))
theorem checked_22_15 : check 64 p_22_15 cert_22_15 = true := by decide +kernel
theorem safe_22_15 : ∀ m, compatible p_22_15 m → WeightedBound 64 m := sound 64 _ cert_22_15 (by decide) checked_22_15
def p_22_16 := refine p_22 (5,true) (some ⟨false,false,4⟩)
def cert_22_16 : Tree := (split 16 (5,false) 6 #[
(.last 19 (2,true)),
(.side 7 13 false (1)),
(.side 10 7 false (0)),
(.side 3 14 false (2)),
(.side 7 15 false (1)),
(.side 18 4 true (-3)),
(.last 18 (2,true)),
(.side 11 16 false (0)),
(.side 0 18 false (2)),
(.last 17 (2,true)),
(.last 20 (2,true)),
(.last 17 (2,true)),
(.side 8 14 false (0)),
(.side 8 9 false (0)),
(.side 9 8 false (0)),
(.side 7 10 false (1)),
(.side 15 2 false (-3)),
(.side 15 3 false (-3)),
(.side 15 2 false (-3)),
(.side 15 4 false (-3)),
(.side 16 1 false (-4)),
(.side 14 3 false (-2)),
(.side 16 1 false (-4)),
(.side 15 4 false (-3))])
theorem checked_22_16 : check 64 p_22_16 cert_22_16 = true := by decide +kernel
theorem safe_22_16 : ∀ m, compatible p_22_16 m → WeightedBound 64 m := sound 64 _ cert_22_16 (by decide) checked_22_16
def p_22_17 := refine p_22 (5,true) (some ⟨false,true,4⟩)
def cert_22_17 : Tree := (split 17 (5,false) 6 #[
(.last 20 (2,true)),
(.side 7 12 false (1)),
(.side 10 8 false (0)),
(.side 5 13 false (2)),
(.side 7 16 false (1)),
(.side 15 4 true (-3)),
(.last 19 (2,true)),
(.side 11 7 false (0)),
(.side 0 19 false (2)),
(.last 18 (2,true)),
(.last 21 (2,true)),
(.last 18 (2,true)),
(.side 8 15 false (0)),
(.side 8 10 false (0)),
(.side 9 9 false (0)),
(.side 7 11 false (1)),
(.side 16 2 false (-2)),
(.side 15 3 false (-1)),
(.side 16 2 false (-2)),
(.side 15 4 false (-1)),
(.side 17 1 false (-3)),
(.side 14 4 true (-3)),
(.side 17 1 false (-3)),
(.side 12 7 false (0))])
theorem checked_22_17 : check 64 p_22_17 cert_22_17 = true := by decide +kernel
theorem safe_22_17 : ∀ m, compatible p_22_17 m → WeightedBound 64 m := sound 64 _ cert_22_17 (by decide) checked_22_17
def p_22_18 := refine p_22 (5,true) (some ⟨true,false,4⟩)
def cert_22_18 : Tree := (split 16 (5,false) 6 #[
(.last 19 (2,true)),
(.side 7 11 false (1)),
(.side 10 7 false (0)),
(.side 5 12 false (2)),
(.side 7 15 false (1)),
(.side 15 4 true (-4)),
(.last 18 (2,true)),
(.side 11 6 false (0)),
(.side 0 18 false (2)),
(.last 17 (2,true)),
(.last 20 (2,true)),
(.last 17 (2,true)),
(.side 8 14 false (0)),
(.side 8 9 false (0)),
(.side 9 8 false (0)),
(.side 7 10 false (1)),
(.side 15 2 false (-3)),
(.side 15 3 false (-3)),
(.side 15 2 false (-3)),
(.side 15 4 false (-3)),
(.side 16 1 false (-4)),
(.side 14 3 false (-2)),
(.side 16 1 false (-4)),
(.side 15 4 false (-3))])
theorem checked_22_18 : check 64 p_22_18 cert_22_18 = true := by decide +kernel
theorem safe_22_18 : ∀ m, compatible p_22_18 m → WeightedBound 64 m := sound 64 _ cert_22_18 (by decide) checked_22_18
def p_22_19 := refine p_22 (5,true) (some ⟨true,true,4⟩)
def cert_22_19 : Tree := (split 18 (5,false) 6 #[
(.last 21 (2,true)),
(.side 7 13 false (1)),
(.side 10 9 false (0)),
(.side 5 14 false (2)),
(.side 7 17 false (1)),
(.side 16 4 true (-4)),
(.last 20 (2,true)),
(.side 11 8 false (0)),
(.side 0 20 false (2)),
(.last 19 (2,true)),
(.last 22 (2,true)),
(.last 19 (2,true)),
(.side 8 16 false (0)),
(.side 8 11 false (0)),
(.side 9 10 false (0)),
(.side 7 12 false (1)),
(.side 17 2 false (-3)),
(.side 16 3 false (-2)),
(.side 17 2 false (-3)),
(.side 15 4 false (-1)),
(.side 18 1 false (-4)),
(.side 14 5 false (-1)),
(.side 18 1 false (-4)),
(.side 15 6 false (-1))])
theorem checked_22_19 : check 64 p_22_19 cert_22_19 = true := by decide +kernel
theorem safe_22_19 : ∀ m, compatible p_22_19 m → WeightedBound 64 m := sound 64 _ cert_22_19 (by decide) checked_22_19
def p_22_20 := refine p_22 (5,true) (some ⟨false,false,5⟩)
def cert_22_20 : Tree := (split 15 (5,false) 6 #[
(.side 0 16 false (2)),
(.side 10 6 true (-3)),
(.side 7 14 false (1)),
(.last 25 (2,true)),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.last 17 (2,true)),
(.last 17 (2,true)),
(.side 0 17 false (2)),
(.last 19 (2,true)),
(.last 19 (2,true)),
(.side 7 13 false (1)),
(.side 8 13 false (0)),
(.side 9 7 false (0)),
(.side 9 7 false (0)),
(.side 7 11 false (1)),
(.side 15 2 false (-3)),
(.side 16 3 false (-2)),
(.side 15 2 false (-3)),
(.side 13 3 false (-1)),
(.side 15 1 false (-3)),
(.side 27 1 true (1)),
(.side 15 1 false (-3)),
(.side 59 1 true (-7))])
theorem checked_22_20 : check 64 p_22_20 cert_22_20 = true := by decide +kernel
theorem safe_22_20 : ∀ m, compatible p_22_20 m → WeightedBound 64 m := sound 64 _ cert_22_20 (by decide) checked_22_20
def p_22_21 := refine p_22 (5,true) (some ⟨false,true,5⟩)
def cert_22_21 : Tree := (split 19 (5,false) 6 #[
(.side 0 20 true (-2)),
(.side 0 20 true (-2)),
(.side 7 18 true (-2)),
(.side 14 22 true (-2)),
(.side 15 17 true (-1)),
(.side 15 17 true (-1)),
(.last 21 (2,true)),
(.side 1 19 true (-2)),
(.side 0 21 true (-2)),
(.side 0 21 true (-2)),
(.last 23 (2,true)),
(.side 15 16 true (-1)),
(.side 16 15 false (3)),
(.side 7 21 true (-2)),
(.side 16 9 true (0)),
(.side 15 14 true (-1)),
(.side 19 2 false (3)),
(.side 20 3 false (4)),
(.side 19 2 false (3)),
(.side 17 4 true (1)),
(.side 19 1 false (3)),
(.side 19 1 true (3)),
(.side 19 1 false (3)),
(.side 19 1 true (3))])
theorem checked_22_21 : check 64 p_22_21 cert_22_21 = true := by decide +kernel
theorem safe_22_21 : ∀ m, compatible p_22_21 m → WeightedBound 64 m := sound 64 _ cert_22_21 (by decide) checked_22_21
def p_22_22 := refine p_22 (5,true) (some ⟨true,false,5⟩)
def cert_22_22 : Tree := (split 15 (5,false) 6 #[
(.last 18 (2,true)),
(.side 7 10 false (1)),
(.side 10 6 false (0)),
(.side 5 11 false (2)),
(.side 7 14 false (1)),
(.side 15 4 true (-3)),
(.last 17 (2,true)),
(.side 11 5 false (0)),
(.side 0 17 false (2)),
(.last 16 (2,true)),
(.last 19 (2,true)),
(.last 16 (2,true)),
(.side 8 13 false (0)),
(.side 8 8 false (0)),
(.side 9 7 false (0)),
(.side 7 9 false (1)),
(.side 15 2 false (-3)),
(.side 15 3 false (-2)),
(.side 15 2 false (-3)),
(.side 15 4 false (-2)),
(.side 15 1 false (-3)),
(.side 14 2 true (-3)),
(.side 15 1 false (-3)),
(.side 14 3 false (-2))])
theorem checked_22_22 : check 64 p_22_22 cert_22_22 = true := by decide +kernel
theorem safe_22_22 : ∀ m, compatible p_22_22 m → WeightedBound 64 m := sound 64 _ cert_22_22 (by decide) checked_22_22
def p_22_23 := refine p_22 (5,true) (some ⟨true,true,5⟩)
def cert_22_23 : Tree := (split 19 (5,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))]⟩),
(.side 16 7 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))]⟩),
(.last 20 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .leaf .leaf)))]⟩),
(.last 20 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .leaf .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))]⟩),
(.side 25 2 false (-3)),
(.side 16 8 true (0)),
(.side 25 2 false (-3)),
(.side 17 4 true (1)),
(.side 18 2 true (2)),
(.side 19 1 true (3)),
(.side 17 3 true (1)),
(.side 19 1 true (3))])
theorem checked_22_23 : check 64 p_22_23 cert_22_23 = true := by decide +kernel
theorem safe_22_23 : ∀ m, compatible p_22_23 m → WeightedBound 64 m := sound 64 _ cert_22_23 (by decide) checked_22_23
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 64 m := by
  apply split_safe 64 p_22 14 (5,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_22_0 | exact safe_22_1 | exact safe_22_2 | exact safe_22_3 | exact safe_22_4 | exact safe_22_5 | exact safe_22_6 | exact safe_22_7 | exact safe_22_8 | exact safe_22_9 | exact safe_22_10 | exact safe_22_11 | exact safe_22_12 | exact safe_22_13 | exact safe_22_14 | exact safe_22_15 | exact safe_22_16 | exact safe_22_17 | exact safe_22_18 | exact safe_22_19 | exact safe_22_20 | exact safe_22_21 | exact safe_22_22 | exact safe_22_23
def p_23 := refine parent (4,false) (some ⟨true,true,5⟩)
def p_23_0 := refine p_23 (5,true) (some ⟨false,false,0⟩)
def cert_23_0 : Tree := (.side 3 12 false (2))
theorem checked_23_0 : check 64 p_23_0 cert_23_0 = true := by decide +kernel
theorem safe_23_0 : ∀ m, compatible p_23_0 m → WeightedBound 64 m := sound 64 _ cert_23_0 (by decide) checked_23_0
def p_23_1 := refine p_23 (5,true) (some ⟨false,true,0⟩)
def cert_23_1 : Tree := (.side 4 14 false (2))
theorem checked_23_1 : check 64 p_23_1 cert_23_1 = true := by decide +kernel
theorem safe_23_1 : ∀ m, compatible p_23_1 m → WeightedBound 64 m := sound 64 _ cert_23_1 (by decide) checked_23_1
def p_23_2 := refine p_23 (5,true) (some ⟨true,false,0⟩)
def cert_23_2 : Tree := (.side 5 10 false (2))
theorem checked_23_2 : check 64 p_23_2 cert_23_2 = true := by decide +kernel
theorem safe_23_2 : ∀ m, compatible p_23_2 m → WeightedBound 64 m := sound 64 _ cert_23_2 (by decide) checked_23_2
def p_23_3 := refine p_23 (5,true) (some ⟨true,true,0⟩)
def cert_23_3 : Tree := (.side 6 12 false (2))
theorem checked_23_3 : check 64 p_23_3 cert_23_3 = true := by decide +kernel
theorem safe_23_3 : ∀ m, compatible p_23_3 m → WeightedBound 64 m := sound 64 _ cert_23_3 (by decide) checked_23_3
def p_23_4 := refine p_23 (5,true) (some ⟨false,false,1⟩)
def cert_23_4 : Tree := (split 23 (5,false) 6 #[
(.side 16 17 true (0)),
(.side 13 34 true (-1)),
(.side 16 15 true (0)),
(.side 13 32 true (-1)),
(.side 21 3 true (1)),
(.side 13 29 true (-1)),
(.side 19 7 true (1)),
(.side 13 27 true (-1)),
(.last 24 (2,true)),
(.side 13 29 true (-1)),
(.last 24 (2,true)),
(.side 2 22 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 21 5 true (1)),
(.side 16 13 true (0)),
(.side 4 20 true (-2)),
(.side 19 6 true (1)),
(.side 22 2 true (2)),
(.side 16 9 true (0)),
(.side 22 2 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf))]⟩),
(.side 23 1 true (3)),
(.side 7 23 true (-2)),
(.side 23 1 true (3))])
theorem checked_23_4 : check 64 p_23_4 cert_23_4 = true := by decide +kernel
theorem safe_23_4 : ∀ m, compatible p_23_4 m → WeightedBound 64 m := sound 64 _ cert_23_4 (by decide) checked_23_4
def p_23_5 := refine p_23 (5,true) (some ⟨false,true,1⟩)
def cert_23_5 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,6)],[(true,6)],[(false,3),(false,5)],[]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) .empty)]⟩)
theorem checked_23_5 : check 64 p_23_5 cert_23_5 = true := by decide +kernel
theorem safe_23_5 : ∀ m, compatible p_23_5 m → WeightedBound 64 m := sound 64 _ cert_23_5 (by decide) checked_23_5
def p_23_6 := refine p_23 (5,true) (some ⟨true,false,1⟩)
def cert_23_6 : Tree := (.side 11 4 true (-1))
theorem checked_23_6 : check 64 p_23_6 cert_23_6 = true := by decide +kernel
theorem safe_23_6 : ∀ m, compatible p_23_6 m → WeightedBound 64 m := sound 64 _ cert_23_6 (by decide) checked_23_6
def p_23_7 := refine p_23 (5,true) (some ⟨true,true,1⟩)
def cert_23_7 : Tree := (.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) .empty)]⟩)
theorem checked_23_7 : check 64 p_23_7 cert_23_7 = true := by decide +kernel
theorem safe_23_7 : ∀ m, compatible p_23_7 m → WeightedBound 64 m := sound 64 _ cert_23_7 (by decide) checked_23_7
def p_23_8 := refine p_23 (5,true) (some ⟨false,false,2⟩)
def cert_23_8 : Tree := (split 15 (2,true) 6 #[
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,4)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) .empty)]⟩),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,4)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) .empty)]⟩),
(.last 18 (5,false)),
(.last 20 (5,false)),
(.side 15 7 false (-1)),
(.last 20 (5,false)),
(.side 0 18 false (2)),
(.side 0 54 true (-4)),
(.side 15 6 false (-1)),
(.side 2 14 false (2)),
(.side 8 8 false (0)),
(.last 34 (5,false)),
(.side 8 8 false (0)),
(.side 4 12 false (2)),
(.last 21 (5,false)),
(.last 23 (5,false)),
(.side 17 3 false (-2)),
(.last 23 (5,false)),
(.side 0 18 false (2)),
(.last 16 (5,false)),
(.side 0 18 false (2)),
(.last 16 (5,false))])
theorem checked_23_8 : check 64 p_23_8 cert_23_8 = true := by decide +kernel
theorem safe_23_8 : ∀ m, compatible p_23_8 m → WeightedBound 64 m := sound 64 _ cert_23_8 (by decide) checked_23_8
def p_23_9 := refine p_23 (5,true) (some ⟨false,true,2⟩)
def cert_23_9 : Tree := (split 15 (2,true) 6 #[
(.side 6 18 false (2)),
(.side 0 28 true (-2)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[],[],[(false,4)],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,2),(3,8),(3,9),(10,6),(3,11),(7,6),(7,8),(7,8)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf (.branch .leaf (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) .empty)]⟩),
(.side 18 16 false (3)),
(.side 6 16 false (2)),
(.last 18 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.last 18 (5,false)),
(.side 2 14 false (2)),
(.side 0 18 true (-2)),
(.side 2 14 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 4 12 false (2)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[],[],[(false,4)],[],[],[(false,7)],[]],#[(1,2),(1,2),(3,4),(5,6),(7,2),(3,8),(3,9),(10,6),(3,11),(7,6),(7,8),(7,8)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf (.branch .leaf (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .leaf) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) (.branch .leaf (.branch .empty (.branch .leaf .leaf)))) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) .empty)]⟩),
(.side 4 12 false (2)),
(.side 4 14 false (2)),
(.last 17 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[(false,3)],[(true,3)],[],[],[(false,13)],[(true,13)],[(false,6),(false,10)],[(true,6),(true,10)],[],[(true,7),(true,11)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))))) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) .leaf))),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty)]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.last 22 (5,false)),
(.last 16 (5,false)),
(.side 0 18 true (-2)),
(.last 16 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[(false,3)],[(true,3)],[],[],[(false,13)],[(true,13)],[],[(true,6),(true,10)],[],[(true,7),(true,11)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))))) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) .leaf))),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty)]⟩)])
theorem checked_23_9 : check 64 p_23_9 cert_23_9 = true := by decide +kernel
theorem safe_23_9 : ∀ m, compatible p_23_9 m → WeightedBound 64 m := sound 64 _ cert_23_9 (by decide) checked_23_9
def p_23_10 := refine p_23 (5,true) (some ⟨true,false,2⟩)
def cert_23_10 : Tree := (split 15 (2,true) 6 #[
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.side 7 18 false (1)),
(.last 28 (5,false)),
(.side 15 7 false (-1)),
(.last 28 (5,false)),
(.side 0 18 false (2)),
(.side 0 20 true (-2)),
(.side 15 6 false (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 8 8 false (0)),
(.side 7 12 false (1)),
(.side 8 8 false (0)),
(.side 6 10 false (2)),
(.last 21 (5,false)),
(.side 12 4 true (-1)),
(.side 17 3 false (-2)),
(.side 17 5 false (-1)),
(.last 23 (5,false)),
(.side 7 14 false (1)),
(.last 23 (5,false)),
(.side 14 2 true (-1))])
theorem checked_23_10 : check 64 p_23_10 cert_23_10 = true := by decide +kernel
theorem safe_23_10 : ∀ m, compatible p_23_10 m → WeightedBound 64 m := sound 64 _ cert_23_10 (by decide) checked_23_10
def p_23_11 := refine p_23 (5,true) (some ⟨true,true,2⟩)
def cert_23_11 : Tree := (split 15 (2,true) 6 #[
(.side 6 14 false (2)),
(.side 18 16 false (3)),
(.side 6 12 false (2)),
(.side 18 14 false (3)),
(.last 48 (5,false)),
(.last 18 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.last 18 (5,false)),
(.side 0 20 false (2)),
(.side 0 46 true (-4)),
(.side 16 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 6 10 false (2)),
(.side 6 14 false (2)),
(.side 6 10 false (2)),
(.side 6 12 false (2)),
(.side 17 5 false (-1)),
(.last 45 (5,false)),
(.side 17 5 false (-1)),
(.side 17 7 false (1)),
(.side 6 16 false (2)),
(.last 40 (5,false)),
(.side 14 2 true (0)),
(.last 38 (5,false))])
theorem checked_23_11 : check 64 p_23_11 cert_23_11 = true := by decide +kernel
theorem safe_23_11 : ∀ m, compatible p_23_11 m → WeightedBound 64 m := sound 64 _ cert_23_11 (by decide) checked_23_11
def p_23_12 := refine p_23 (5,true) (some ⟨false,false,3⟩)
def cert_23_12 : Tree := (.side 7 8 false (1))
theorem checked_23_12 : check 64 p_23_12 cert_23_12 = true := by decide +kernel
theorem safe_23_12 : ∀ m, compatible p_23_12 m → WeightedBound 64 m := sound 64 _ cert_23_12 (by decide) checked_23_12
def p_23_13 := refine p_23 (5,true) (some ⟨false,true,3⟩)
def cert_23_13 : Tree := (.side 4 12 false (2))
theorem checked_23_13 : check 64 p_23_13 cert_23_13 = true := by decide +kernel
theorem safe_23_13 : ∀ m, compatible p_23_13 m → WeightedBound 64 m := sound 64 _ cert_23_13 (by decide) checked_23_13
def p_23_14 := refine p_23 (5,true) (some ⟨true,false,3⟩)
def cert_23_14 : Tree := (.side 7 8 false (1))
theorem checked_23_14 : check 64 p_23_14 cert_23_14 = true := by decide +kernel
theorem safe_23_14 : ∀ m, compatible p_23_14 m → WeightedBound 64 m := sound 64 _ cert_23_14 (by decide) checked_23_14
def p_23_15 := refine p_23 (5,true) (some ⟨true,true,3⟩)
def cert_23_15 : Tree := (.side 6 10 false (2))
theorem checked_23_15 : check 64 p_23_15 cert_23_15 = true := by decide +kernel
theorem safe_23_15 : ∀ m, compatible p_23_15 m → WeightedBound 64 m := sound 64 _ cert_23_15 (by decide) checked_23_15
def p_23_16 := refine p_23 (5,true) (some ⟨false,false,4⟩)
def cert_23_16 : Tree := (.side 16 3 false (-2))
theorem checked_23_16 : check 64 p_23_16 cert_23_16 = true := by decide +kernel
theorem safe_23_16 : ∀ m, compatible p_23_16 m → WeightedBound 64 m := sound 64 _ cert_23_16 (by decide) checked_23_16
def p_23_17 := refine p_23 (5,true) (some ⟨false,true,4⟩)
def cert_23_17 : Tree := (split 22 (5,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 21 3 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 18 6 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.last 23 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.last 23 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 21 5 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 18 5 true (1)),
(.side 21 2 true (3)),
(.side 15 8 true (0)),
(.side 21 2 true (3)),
(.side 20 3 true (2)),
(.side 22 1 true (4)),
(.side 17 6 true (1)),
(.side 22 1 true (4))])
theorem checked_23_17 : check 64 p_23_17 cert_23_17 = true := by decide +kernel
theorem safe_23_17 : ∀ m, compatible p_23_17 m → WeightedBound 64 m := sound 64 _ cert_23_17 (by decide) checked_23_17
def p_23_18 := refine p_23 (5,true) (some ⟨true,false,4⟩)
def cert_23_18 : Tree := (.side 16 3 false (-2))
theorem checked_23_18 : check 64 p_23_18 cert_23_18 = true := by decide +kernel
theorem safe_23_18 : ∀ m, compatible p_23_18 m → WeightedBound 64 m := sound 64 _ cert_23_18 (by decide) checked_23_18
def p_23_19 := refine p_23 (5,true) (some ⟨true,true,4⟩)
def cert_23_19 : Tree := (.side 16 5 false (0))
theorem checked_23_19 : check 64 p_23_19 cert_23_19 = true := by decide +kernel
theorem safe_23_19 : ∀ m, compatible p_23_19 m → WeightedBound 64 m := sound 64 _ cert_23_19 (by decide) checked_23_19
def p_23_20 := refine p_23 (5,true) (some ⟨false,false,5⟩)
def cert_23_20 : Tree := (split 17 (5,false) 6 #[
(.side 0 18 false (2)),
(.side 0 18 false (2)),
(.side 7 20 false (1)),
(.side 6 19 false (2)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.last 19 (2,true)),
(.side 1 17 false (2)),
(.side 0 19 false (2)),
(.side 0 19 false (2)),
(.last 21 (2,true)),
(.side 7 15 false (1)),
(.side 7 19 false (1)),
(.side 7 23 false (1)),
(.side 9 9 false (0)),
(.side 7 13 false (1)),
(.side 15 7 false (-1)),
(.side 31 2 true (-1)),
(.side 15 4 false (-1)),
(.side 39 2 true (-5)),
(.side 17 1 false (-3)),
(.side 25 1 true (1)),
(.side 17 1 false (-3)),
(.side 39 1 true (-5))])
theorem checked_23_20 : check 64 p_23_20 cert_23_20 = true := by decide +kernel
theorem safe_23_20 : ∀ m, compatible p_23_20 m → WeightedBound 64 m := sound 64 _ cert_23_20 (by decide) checked_23_20
def p_23_21 := refine p_23 (5,true) (some ⟨false,true,5⟩)
def cert_23_21 : Tree := (split 17 (5,false) 6 #[
(.side 0 18 true (-2)),
(.side 0 18 true (-2)),
(.side 14 21 true (0)),
(.side 14 20 true (0)),
(.side 54 38 true (0)),
(.side 15 15 true (1)),
(.last 19 (2,true)),
(.side 1 17 true (-2)),
(.side 0 46 true (-4)),
(.side 0 19 true (-2)),
(.last 21 (2,true)),
(.side 15 14 true (1)),
(.side 7 46 true (-4)),
(.side 17 5 true (3)),
(.side 43 22 true (1)),
(.side 15 12 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))]⟩),
(.side 17 2 true (3)),
(.side 16 3 true (2)),
(.side 17 2 true (3)),
(.side 25 1 false (-1)),
(.side 17 1 true (3)),
(.side 39 1 false (5)),
(.side 17 1 true (3))])
theorem checked_23_21 : check 64 p_23_21 cert_23_21 = true := by decide +kernel
theorem safe_23_21 : ∀ m, compatible p_23_21 m → WeightedBound 64 m := sound 64 _ cert_23_21 (by decide) checked_23_21
def p_23_22 := refine p_23 (5,true) (some ⟨true,false,5⟩)
def cert_23_22 : Tree := (split 17 (5,false) 6 #[
(.last 20 (2,true)),
(.side 7 12 false (1)),
(.side 10 8 false (0)),
(.side 5 13 false (2)),
(.side 7 16 false (1)),
(.side 15 6 true (-3)),
(.last 19 (2,true)),
(.side 11 7 false (0)),
(.side 0 19 false (2)),
(.last 18 (2,true)),
(.last 21 (2,true)),
(.last 18 (2,true)),
(.side 8 17 false (0)),
(.side 8 10 false (0)),
(.side 9 9 false (0)),
(.side 7 11 false (1)),
(.side 15 7 false (-1)),
(.side 15 5 false (-1)),
(.side 15 4 false (-1)),
(.side 15 6 false (-1)),
(.side 17 1 false (-3)),
(.side 16 2 true (-3)),
(.side 17 1 false (-3)),
(.side 15 3 false (-1))])
theorem checked_23_22 : check 64 p_23_22 cert_23_22 = true := by decide +kernel
theorem safe_23_22 : ∀ m, compatible p_23_22 m → WeightedBound 64 m := sound 64 _ cert_23_22 (by decide) checked_23_22
def p_23_23 := refine p_23 (5,true) (some ⟨true,true,5⟩)
def cert_23_23 : Tree := (split 17 (5,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 17 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 16 5 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.last 18 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.last 18 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 17 5 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 17 2 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .leaf),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 17 2 true (3)),
(.side 16 2 true (2)),
(.side 17 1 true (3)),
(.side 15 3 true (1)),
(.side 17 1 true (3))])
theorem checked_23_23 : check 64 p_23_23 cert_23_23 = true := by decide +kernel
theorem safe_23_23 : ∀ m, compatible p_23_23 m → WeightedBound 64 m := sound 64 _ cert_23_23 (by decide) checked_23_23
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 64 m := by
  apply split_safe 64 p_23 14 (5,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_23_0 | exact safe_23_1 | exact safe_23_2 | exact safe_23_3 | exact safe_23_4 | exact safe_23_5 | exact safe_23_6 | exact safe_23_7 | exact safe_23_8 | exact safe_23_9 | exact safe_23_10 | exact safe_23_11 | exact safe_23_12 | exact safe_23_13 | exact safe_23_14 | exact safe_23_15 | exact safe_23_16 | exact safe_23_17 | exact safe_23_18 | exact safe_23_19 | exact safe_23_20 | exact safe_23_21 | exact safe_23_22 | exact safe_23_23
theorem safe : ∀ m, compatible parent m → WeightedBound 64 m := by
  apply split_safe 64 parent 13 (4,false) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23
theorem cover : Cover (WeightedBound 64) parent := .leaf _ safe
#print axioms safe
#print axioms cover
end BB6.Agent47Root46
