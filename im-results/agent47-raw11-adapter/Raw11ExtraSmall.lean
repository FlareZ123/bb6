import PhaseTree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent47Extra93
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,false,1⟩)
  | _,_ => none)
def p_0 := refine parent (4,true) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.side 6 17 false (3))
theorem checked_0 : check 24 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 24 m := sound 24 _ cert_0 (by decide) checked_0
def p_1 := refine parent (4,true) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 0 15 true (-1))
theorem checked_1 : check 24 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 24 m := sound 24 _ cert_1 (by decide) checked_1
def p_2 := refine parent (4,true) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 6 11 false (2))
theorem checked_2 : check 24 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 24 m := sound 24 _ cert_2 (by decide) checked_2
def p_3 := refine parent (4,true) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 22 15 false (4))
theorem checked_3 : check 24 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 24 m := sound 24 _ cert_3 (by decide) checked_3
def p_4 := refine parent (4,true) (some ⟨false,false,1⟩)
def cert_4 : Tree := (.side 6 38 false (2))
theorem checked_4 : check 24 p_4 cert_4 = true := by decide +kernel
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 24 m := sound 24 _ cert_4 (by decide) checked_4
def p_5 := refine parent (4,true) (some ⟨false,true,1⟩)
def cert_5 : Tree := (.side 6 19 false (4))
theorem checked_5 : check 24 p_5 cert_5 = true := by decide +kernel
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 24 m := sound 24 _ cert_5 (by decide) checked_5
def p_6 := refine parent (4,true) (some ⟨true,false,1⟩)
def cert_6 : Tree := (.side 15 3 true (1))
theorem checked_6 : check 24 p_6 cert_6 = true := by decide +kernel
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 24 m := sound 24 _ cert_6 (by decide) checked_6
def p_7 := refine parent (4,true) (some ⟨true,true,1⟩)
def cert_7 : Tree := (.side 1 14 true (-1))
theorem checked_7 : check 24 p_7 cert_7 = true := by decide +kernel
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 24 m := sound 24 _ cert_7 (by decide) checked_7
def p_8 := refine parent (4,true) (some ⟨false,false,2⟩)
def cert_8 : Tree := (.side 2 13 false (2))
theorem checked_8 : check 24 p_8 cert_8 = true := by decide +kernel
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 24 m := sound 24 _ cert_8 (by decide) checked_8
def p_9 := refine parent (4,true) (some ⟨false,true,2⟩)
def cert_9 : Tree := (.side 0 16 true (-1))
theorem checked_9 : check 24 p_9 cert_9 = true := by decide +kernel
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 24 m := sound 24 _ cert_9 (by decide) checked_9
def p_10 := refine parent (4,true) (some ⟨true,false,2⟩)
def cert_10 : Tree := (.side 2 13 false (2))
theorem checked_10 : check 24 p_10 cert_10 = true := by decide +kernel
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 24 m := sound 24 _ cert_10 (by decide) checked_10
def p_11 := refine parent (4,true) (some ⟨true,true,2⟩)
def cert_11 : Tree := (.side 4 17 false (3))
theorem checked_11 : check 24 p_11 cert_11 = true := by decide +kernel
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 24 m := sound 24 _ cert_11 (by decide) checked_11
def p_12 := refine parent (4,true) (some ⟨false,false,3⟩)
def cert_12 : Tree := (.side 4 11 false (2))
theorem checked_12 : check 24 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 24 m := sound 24 _ cert_12 (by decide) checked_12
def p_13 := refine parent (4,true) (some ⟨false,true,3⟩)
def cert_13 : Tree := (.side 19 3 true (1))
theorem checked_13 : check 24 p_13 cert_13 = true := by decide +kernel
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 24 m := sound 24 _ cert_13 (by decide) checked_13
def p_14 := refine parent (4,true) (some ⟨true,false,3⟩)
def cert_14 : Tree := (.side 4 11 false (2))
theorem checked_14 : check 24 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 24 m := sound 24 _ cert_14 (by decide) checked_14
def p_15 := refine parent (4,true) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 4 15 false (3))
theorem checked_15 : check 24 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 24 m := sound 24 _ cert_15 (by decide) checked_15
def p_16 := refine parent (4,true) (some ⟨false,false,4⟩)
def cert_16 : Tree := (.side 7 9 false (2))
theorem checked_16 : check 24 p_16 cert_16 = true := by decide +kernel
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 24 m := sound 24 _ cert_16 (by decide) checked_16
def p_17 := refine parent (4,true) (some ⟨false,true,4⟩)
def cert_17 : Tree := (.side 15 3 true (2))
theorem checked_17 : check 24 p_17 cert_17 = true := by decide +kernel
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 24 m := sound 24 _ cert_17 (by decide) checked_17
def p_18 := refine parent (4,true) (some ⟨true,false,4⟩)
def cert_18 : Tree := (.side 7 9 false (2))
theorem checked_18 : check 24 p_18 cert_18 = true := by decide +kernel
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 24 m := sound 24 _ cert_18 (by decide) checked_18
def p_19 := refine parent (4,true) (some ⟨true,true,4⟩)
def cert_19 : Tree := (.side 4 13 false (3))
theorem checked_19 : check 24 p_19 cert_19 = true := by decide +kernel
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 24 m := sound 24 _ cert_19 (by decide) checked_19
def p_20 := refine parent (4,true) (some ⟨false,false,5⟩)
def cert_20 : Tree := (split 15 (5,false) 6 #[
(.side 3 13 false (2)),
(.side 0 16 true (-1)),
(.side 5 11 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,2),(true,1)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 18 3 true (-2)),
(.side 4 19 false (3)),
(.side 7 9 false (2)),
(.side 6 17 false (3)),
(.side 16 3 true (0)),
(.side 6 19 false (3)),
(.side 24 3 true (-2)),
(.side 6 38 false (2)),
(.side 6 26 false (2)),
(.side 6 13 false (2)),
(.side 6 26 false (2)),
(.side 6 34 false (2)),
(.last 17 (5,true)),
(.side 16 3 true (1)),
(.last 17 (5,true)),
(.side 6 30 false (2)),
(.last 16 (5,true)),
(.side 15 1 true (1)),
(.last 16 (5,true)),
(.side 15 1 true (1))])
theorem checked_20 : check 24 p_20 cert_20 = true := by decide +kernel
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 24 m := sound 24 _ cert_20 (by decide) checked_20
def p_21 := refine parent (4,true) (some ⟨false,true,5⟩)
def cert_21 : Tree := (split 15 (5,false) 6 #[
(.side 0 16 true (-1)),
(.side 0 16 true (-1)),
(.side 19 3 true (1)),
(.side 23 17 false (5)),
(.side 4 19 false (3)),
(.side 9 21 true (-1)),
(.side 16 3 true (2)),
(.side 1 15 true (-1)),
(.side 6 19 false (3)),
(.side 0 17 true (-1)),
(.side 18 3 true (2)),
(.side 6 19 false (4)),
(.side 6 13 false (3)),
(.side 20 3 true (2)),
(.side 6 13 false (3)),
(.side 6 17 false (4)),
(.side 16 3 true (1)),
(.side 16 3 true (3)),
(.side 11 5 true (0)),
(.side 6 15 false (4)),
(.last 18 (5,true)),
(.side 15 1 true (3)),
(.last 18 (5,true)),
(.side 15 1 true (3))])
theorem checked_21 : check 24 p_21 cert_21 = true := by decide +kernel
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 24 m := sound 24 _ cert_21 (by decide) checked_21
def p_22 := refine parent (4,true) (some ⟨true,false,5⟩)
def cert_22 : Tree := (split 15 (5,false) 6 #[
(.side 3 13 false (2)),
(.side 4 17 false (3)),
(.side 5 11 false (2)),
(.side 6 15 false (3)),
(.side 16 17 false (2)),
(.side 4 13 false (2)),
(.side 7 9 false (2)),
(.side 6 11 false (2)),
(.side 10 6 true (0)),
(.side 16 3 true (2)),
(.side 12 12 false (2)),
(.side 16 3 true (2)),
(.side 6 26 false (2)),
(.side 17 3 true (1)),
(.side 6 26 false (2)),
(.side 6 30 false (2)),
(.last 17 (5,true)),
(.side 14 2 true (1)),
(.last 17 (5,true)),
(.last 17 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true))])
theorem checked_22 : check 24 p_22 cert_22 = true := by decide +kernel
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 24 m := sound 24 _ cert_22 (by decide) checked_22
def p_23 := refine parent (4,true) (some ⟨true,true,5⟩)
def cert_23 : Tree := (split 15 (5,false) 6 #[
(.side 4 17 false (3)),
(.side 0 16 true (-1)),
(.side 4 15 false (3)),
(.side 45 19 false (4)),
(.side 4 13 false (3)),
(.side 22 17 false (4)),
(.side 4 13 false (3)),
(.side 22 15 false (4)),
(.side 16 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6),(false,8)],[(true,2)],[(false,3)],[(true,3)],[],[(true,5)],[(true,6)],[],[(true,8)]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty))),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),.empty]⟩),
(.side 13 3 true (1)),
(.side 2 14 true (-1)),
(.side 17 3 true (1)),
(.side 34 3 true (2)),
(.side 12 5 true (0)),
(.side 4 12 true (-1)),
(.side 14 2 true (2)),
(.side 16 3 true (3)),
(.last 17 (5,true)),
(.side 7 10 true (-1)),
(.last 16 (5,true)),
(.side 15 1 true (3)),
(.last 16 (5,true)),
(.side 15 1 true (3))])
theorem checked_23 : check 24 p_23 cert_23 = true := by decide +kernel
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 24 m := sound 24 _ cert_23 (by decide) checked_23
theorem safe : ∀ m, compatible parent m → WeightedBound 24 m := by
  apply split_safe 24 parent 14 (4,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23 | omega
theorem cover : Cover (WeightedBound 24) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra93

namespace BB6.Agent47Extra94
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,false,4⟩)
  | _,_ => none)
def p_0 := refine parent (4,true) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.side 0 14 false (2))
theorem checked_0 : check 30 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 30 m := sound 30 _ cert_0 (by decide) checked_0
def p_1 := refine parent (4,true) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 0 20 true (-1))
theorem checked_1 : check 30 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 30 m := sound 30 _ cert_1 (by decide) checked_1
def p_2 := refine parent (4,true) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 7 8 false (1))
theorem checked_2 : check 30 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 30 m := sound 30 _ cert_2 (by decide) checked_2
def p_3 := refine parent (4,true) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 28 19 false (2))
theorem checked_3 : check 30 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 30 m := sound 30 _ cert_3 (by decide) checked_3
def p_4 := refine parent (4,true) (some ⟨false,false,1⟩)
def cert_4 : Tree := (.side 7 16 false (1))
theorem checked_4 : check 30 p_4 cert_4 = true := by decide +kernel
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 30 m := sound 30 _ cert_4 (by decide) checked_4
def p_5 := refine parent (4,true) (some ⟨false,true,1⟩)
def cert_5 : Tree := (.side 7 16 false (1))
theorem checked_5 : check 30 p_5 cert_5 = true := by decide +kernel
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 30 m := sound 30 _ cert_5 (by decide) checked_5
def p_6 := refine parent (4,true) (some ⟨true,false,1⟩)
def cert_6 : Tree := (.side 9 5 false (1))
theorem checked_6 : check 30 p_6 cert_6 = true := by decide +kernel
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 30 m := sound 30 _ cert_6 (by decide) checked_6
def p_7 := refine parent (4,true) (some ⟨true,true,1⟩)
def cert_7 : Tree := (.side 1 13 false (2))
theorem checked_7 : check 30 p_7 cert_7 = true := by decide +kernel
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 30 m := sound 30 _ cert_7 (by decide) checked_7
def p_8 := refine parent (4,true) (some ⟨false,false,2⟩)
def cert_8 : Tree := (.side 0 15 false (2))
theorem checked_8 : check 30 p_8 cert_8 = true := by decide +kernel
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 30 m := sound 30 _ cert_8 (by decide) checked_8
def p_9 := refine parent (4,true) (some ⟨false,true,2⟩)
def cert_9 : Tree := (.side 0 15 false (2))
theorem checked_9 : check 30 p_9 cert_9 = true := by decide +kernel
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 30 m := sound 30 _ cert_9 (by decide) checked_9
def p_10 := refine parent (4,true) (some ⟨true,false,2⟩)
def cert_10 : Tree := (.side 13 9 false (0))
theorem checked_10 : check 30 p_10 cert_10 = true := by decide +kernel
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 30 m := sound 30 _ cert_10 (by decide) checked_10
def p_11 := refine parent (4,true) (some ⟨true,true,2⟩)
def cert_11 : Tree := (.side 7 15 false (1))
theorem checked_11 : check 30 p_11 cert_11 = true := by decide +kernel
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 30 m := sound 30 _ cert_11 (by decide) checked_11
def p_12 := refine parent (4,true) (some ⟨false,false,3⟩)
def cert_12 : Tree := (.side 7 9 false (1))
theorem checked_12 : check 30 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 30 m := sound 30 _ cert_12 (by decide) checked_12
def p_13 := refine parent (4,true) (some ⟨false,true,3⟩)
def cert_13 : Tree := (.side 7 9 false (1))
theorem checked_13 : check 30 p_13 cert_13 = true := by decide +kernel
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 30 m := sound 30 _ cert_13 (by decide) checked_13
def p_14 := refine parent (4,true) (some ⟨true,false,3⟩)
def cert_14 : Tree := (.side 7 9 false (1))
theorem checked_14 : check 30 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 30 m := sound 30 _ cert_14 (by decide) checked_14
def p_15 := refine parent (4,true) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 7 13 false (1))
theorem checked_15 : check 30 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 30 m := sound 30 _ cert_15 (by decide) checked_15
def p_16 := refine parent (4,true) (some ⟨false,false,4⟩)
def cert_16 : Tree := (.side 14 1 false (-2))
theorem checked_16 : check 30 p_16 cert_16 = true := by decide +kernel
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 30 m := sound 30 _ cert_16 (by decide) checked_16
def p_17 := refine parent (4,true) (some ⟨false,true,4⟩)
def cert_17 : Tree := (.side 14 1 false (0))
theorem checked_17 : check 30 p_17 cert_17 = true := by decide +kernel
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 30 m := sound 30 _ cert_17 (by decide) checked_17
def p_18 := refine parent (4,true) (some ⟨true,false,4⟩)
def cert_18 : Tree := (.side 14 1 false (-2))
theorem checked_18 : check 30 p_18 cert_18 = true := by decide +kernel
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 30 m := sound 30 _ cert_18 (by decide) checked_18
def p_19 := refine parent (4,true) (some ⟨true,true,4⟩)
def cert_19 : Tree := (.side 12 2 true (-1))
theorem checked_19 : check 30 p_19 cert_19 = true := by decide +kernel
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 30 m := sound 30 _ cert_19 (by decide) checked_19
def p_20 := refine parent (4,true) (some ⟨false,false,5⟩)
def cert_20 : Tree := (split 14 (5,false) 6 #[
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.side 7 9 false (1)),
(.side 7 20 false (1)),
(.side 7 17 false (1)),
(.side 7 17 false (1)),
(.side 9 6 false (1)),
(.side 1 14 false (2)),
(.side 0 16 false (2)),
(.side 0 16 false (2)),
(.last 22 (5,true)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 7 10 false (1)),
(.side 7 10 false (1)),
(.side 7 14 false (1)),
(.side 15 1 false (-3)),
(.side 15 1 false (-1)),
(.side 15 1 false (-3)),
(.side 12 3 false (0)),
(.side 14 1 false (-2)),
(.last 18 (5,true)),
(.side 14 1 false (-2)),
(.last 18 (5,true))])
theorem checked_20 : check 30 p_20 cert_20 = true := by decide +kernel
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 30 m := sound 30 _ cert_20 (by decide) checked_20
def p_21 := refine parent (4,true) (some ⟨false,true,5⟩)
def cert_21 : Tree := (split 14 (5,false) 6 #[
(.side 0 15 false (2)),
(.side 0 24 true (-1)),
(.side 7 9 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,2)],[(false,4),(false,9)],[(false,2)],[(true,6),(true,10)],[(true,7)],[(true,8)],[(false,8)]],#[(0,1),(3,2),(6,4),(0,0),(5,0),(0,0),(0,7),(0,8),(10,9),(5,0),(0,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[(false,3),(true,3),(false,6),(true,6),(false,7),(false,10),(true,10),(false,11),(true,11),(false,13),(true,13),(false,18),(false,21),(true,21),(false,24),(true,24),(true,26),(false,27),(true,27)],[(false,4),(false,16),(false,20),(false,23)],[(true,4)],[(false,5)],[(true,5)],[(true,7)],[(false,8),(false,22)],[(true,8),(true,19),(true,22)],[(false,9)],[(true,9)],[(false,12),(false,25)],[(true,12),(true,25)],[(false,14)],[(true,14)],[(false,15)],[(true,15),(true,17)],[(true,16)],[(false,17)],[(true,18)],[(false,19)],[(true,20),(true,23)],[(false,26)]],#[(0,1),(2,3),(4,5),(6,6),(7,8),(9,10),(6,6),(6,11),(12,13),(14,15),(6,6),(6,6),(16,17),(6,6),(18,19),(20,21),(7,22),(23,21),(6,24),(25,13),(7,26),(6,6),(12,13),(7,26),(6,6),(16,17),(27,6),(6,6)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .leaf)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty .leaf) .empty)) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty .leaf) .empty)) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .leaf (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .leaf (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .leaf)) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)))) (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf) (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch .empty (.branch .empty (.branch .leaf (.branch .empty (.branch .leaf .leaf))))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .leaf (.branch .empty (.branch .empty .leaf))))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf))) (.branch .leaf (.branch (.branch .empty .leaf) (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .leaf .leaf))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .leaf) (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .leaf (.branch .empty (.branch .leaf .leaf))))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty)))) (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .leaf .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))))))),.empty]⟩),
(.side 7 17 false (1)),
(.side 15 17 false (4)),
(.side 9 6 true (-1)),
(.side 1 20 true (-1)),
(.side 0 16 false (2)),
(.side 0 24 true (-1)),
(.side 7 24 false (1)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 7 10 true (-1)),
(.side 7 10 false (1)),
(.side 7 14 false (1)),
(.side 15 1 false (-1)),
(.side 15 1 false (1)),
(.side 15 1 false (-1)),
(.side 18 3 true (2)),
(.side 14 1 false (0)),
(.last 16 (5,true)),
(.side 14 1 false (0)),
(.last 16 (5,true))])
theorem checked_21 : check 30 p_21 cert_21 = true := by decide +kernel
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 30 m := sound 30 _ cert_21 (by decide) checked_21
def p_22 := refine parent (4,true) (some ⟨true,false,5⟩)
def cert_22 : Tree := (split 14 (5,false) 6 #[
(.last 21 (5,true)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 3 12 false (2)),
(.side 7 17 false (1)),
(.side 7 11 false (1)),
(.side 7 15 false (1)),
(.side 7 8 false (1)),
(.side 0 16 false (2)),
(.side 16 1 false (0)),
(.side 13 12 false (-1)),
(.side 10 5 false (1)),
(.side 7 10 false (1)),
(.side 8 7 false (1)),
(.side 7 10 false (1)),
(.side 7 12 false (1)),
(.side 15 1 false (-3)),
(.side 13 2 true (-2)),
(.side 15 1 false (-3)),
(.last 16 (5,true)),
(.side 14 1 false (-2)),
(.last 15 (5,true)),
(.side 14 1 false (-2)),
(.last 15 (5,true))])
theorem checked_22 : check 30 p_22 cert_22 = true := by decide +kernel
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 30 m := sound 30 _ cert_22 (by decide) checked_22
def p_23 := refine parent (4,true) (some ⟨true,true,5⟩)
def cert_23 : Tree := (split 14 (5,false) 6 #[
(.side 7 15 false (1)),
(.side 0 24 true (-1)),
(.side 7 13 false (1)),
(.side 6 11 false (2)),
(.side 7 11 false (1)),
(.side 28 21 false (2)),
(.side 7 11 false (1)),
(.side 28 19 false (2)),
(.side 16 1 false (0)),
(.side 32 21 false (2)),
(.last 20 (5,true)),
(.side 2 13 false (2)),
(.side 8 7 false (1)),
(.side 7 15 false (1)),
(.last 24 (5,true)),
(.side 4 11 false (2)),
(.side 13 2 true (-1)),
(.side 11 4 true (-1)),
(.last 16 (5,true)),
(.side 18 3 true (2)),
(.last 15 (5,true)),
(.last 16 (5,true)),
(.last 15 (5,true)),
(.last 16 (5,true))])
theorem checked_23 : check 30 p_23 cert_23 = true := by decide +kernel
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 30 m := sound 30 _ cert_23 (by decide) checked_23
theorem safe : ∀ m, compatible parent m → WeightedBound 30 m := by
  apply split_safe 30 parent 13 (4,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23 | omega
theorem cover : Cover (WeightedBound 30) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra94

namespace BB6.Agent47Extra95
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,4⟩)
  | _,_ => none)
def p_0 := refine parent (4,true) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.side 0 13 true (-1))
theorem checked_0 : check 75 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 75 m := sound 75 _ cert_0 (by decide) checked_0
def p_1 := refine parent (4,true) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 0 13 true (-1))
theorem checked_1 : check 75 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 75 m := sound 75 _ cert_1 (by decide) checked_1
def p_2 := refine parent (4,true) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 18 1 true (2))
theorem checked_2 : check 75 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 75 m := sound 75 _ cert_2 (by decide) checked_2
def p_3 := refine parent (4,true) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 129 1 true (9))
theorem checked_3 : check 75 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 75 m := sound 75 _ cert_3 (by decide) checked_3
def p_4 := refine parent (4,true) (some ⟨false,false,1⟩)
def cert_4 : Tree := (.side 22 21 false (0))
theorem checked_4 : check 75 p_4 cert_4 = true := by decide +kernel
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 75 m := sound 75 _ cert_4 (by decide) checked_4
def p_5 := refine parent (4,true) (some ⟨false,true,1⟩)
def cert_5 : Tree := (.side 11 16 true (0))
theorem checked_5 : check 75 p_5 cert_5 = true := by decide +kernel
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 75 m := sound 75 _ cert_5 (by decide) checked_5
def p_6 := refine parent (4,true) (some ⟨true,false,1⟩)
def cert_6 : Tree := (.side 15 1 true (3))
theorem checked_6 : check 75 p_6 cert_6 = true := by decide +kernel
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 75 m := sound 75 _ cert_6 (by decide) checked_6
def p_7 := refine parent (4,true) (some ⟨true,true,1⟩)
def cert_7 : Tree := (.side 1 12 true (-1))
theorem checked_7 : check 75 p_7 cert_7 = true := by decide +kernel
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 75 m := sound 75 _ cert_7 (by decide) checked_7
def p_8 := refine parent (4,true) (some ⟨false,false,2⟩)
def cert_8 : Tree := (.side 6 50 false (2))
theorem checked_8 : check 75 p_8 cert_8 = true := by decide +kernel
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 75 m := sound 75 _ cert_8 (by decide) checked_8
def p_9 := refine parent (4,true) (some ⟨false,true,2⟩)
def cert_9 : Tree := (.side 0 14 true (-1))
theorem checked_9 : check 75 p_9 cert_9 = true := by decide +kernel
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 75 m := sound 75 _ cert_9 (by decide) checked_9
def p_10 := refine parent (4,true) (some ⟨true,false,2⟩)
def cert_10 : Tree := (.side 17 1 true (3))
theorem checked_10 : check 75 p_10 cert_10 = true := by decide +kernel
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 75 m := sound 75 _ cert_10 (by decide) checked_10
def p_11 := refine parent (4,true) (some ⟨true,true,2⟩)
def cert_11 : Tree := (.side 64 1 true (4))
theorem checked_11 : check 75 p_11 cert_11 = true := by decide +kernel
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 75 m := sound 75 _ cert_11 (by decide) checked_11
def p_12 := refine parent (4,true) (some ⟨false,false,3⟩)
def cert_12 : Tree := (.side 33 1 true (-1))
theorem checked_12 : check 75 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 75 m := sound 75 _ cert_12 (by decide) checked_12
def p_13 := refine parent (4,true) (some ⟨false,true,3⟩)
def cert_13 : Tree := (.side 19 1 true (3))
theorem checked_13 : check 75 p_13 cert_13 = true := by decide +kernel
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 75 m := sound 75 _ cert_13 (by decide) checked_13
def p_14 := refine parent (4,true) (some ⟨true,false,3⟩)
def cert_14 : Tree := (.side 6 32 false (2))
theorem checked_14 : check 75 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 75 m := sound 75 _ cert_14 (by decide) checked_14
def p_15 := refine parent (4,true) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 57 13 true (-1))
theorem checked_15 : check 75 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 75 m := sound 75 _ cert_15 (by decide) checked_15
def p_16 := refine parent (4,true) (some ⟨false,false,4⟩)
def cert_16 : Tree := (.side 13 1 true (1))
theorem checked_16 : check 75 p_16 cert_16 = true := by decide +kernel
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 75 m := sound 75 _ cert_16 (by decide) checked_16
def p_17 := refine parent (4,true) (some ⟨false,true,4⟩)
def cert_17 : Tree := (.side 13 1 true (3))
theorem checked_17 : check 75 p_17 cert_17 = true := by decide +kernel
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 75 m := sound 75 _ cert_17 (by decide) checked_17
def p_18 := refine parent (4,true) (some ⟨true,false,4⟩)
def cert_18 : Tree := (.side 11 2 true (1))
theorem checked_18 : check 75 p_18 cert_18 = true := by decide +kernel
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 75 m := sound 75 _ cert_18 (by decide) checked_18
def p_19 := refine parent (4,true) (some ⟨true,true,4⟩)
def cert_19 : Tree := (.side 13 1 true (3))
theorem checked_19 : check 75 p_19 cert_19 = true := by decide +kernel
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 75 m := sound 75 _ cert_19 (by decide) checked_19
def p_20 := refine parent (4,true) (some ⟨false,false,5⟩)
def cert_20 : Tree := (split 13 (5,false) 6 #[
(.side 6 50 false (2)),
(.side 0 14 true (-1)),
(.side 33 1 true (-1)),
(.side 54 25 false (2)),
(.side 1 13 false (2)),
(.side 72 1 true (4)),
(.side 16 1 true (2)),
(.side 1 13 true (-1)),
(.side 18 21 false (0)),
(.side 0 15 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,2),(true,1)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 22 21 false (0)),
(.side 16 15 false (0)),
(.side 20 1 true (2)),
(.side 16 15 false (0)),
(.side 20 19 false (0)),
(.side 14 1 true (0)),
(.side 14 1 true (2)),
(.side 17 3 false (-1)),
(.side 14 1 true (2)),
(.last 15 (5,true)),
(.side 13 1 true (1)),
(.last 15 (5,true)),
(.side 13 1 true (1))])
theorem checked_20 : check 75 p_20 cert_20 = true := by decide +kernel
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 75 m := sound 75 _ cert_20 (by decide) checked_20
def p_21 := refine parent (4,true) (some ⟨false,true,5⟩)
def cert_21 : Tree := (split 13 (5,false) 6 #[
(.side 0 14 true (-1)),
(.side 0 14 true (-1)),
(.side 19 1 true (3)),
(.side 3 31 true (-1)),
(.last 69 (5,true)),
(.side 11 17 true (1)),
(.side 16 1 true (4)),
(.side 1 13 true (-1)),
(.side 0 15 true (-1)),
(.side 0 15 true (-1)),
(.side 18 1 true (4)),
(.side 11 16 true (0)),
(.side 20 1 true (2)),
(.side 20 1 true (4)),
(.side 7 9 true (-1)),
(.side 11 14 true (0)),
(.side 14 1 true (2)),
(.side 14 1 true (4)),
(.side 11 3 true (1)),
(.side 14 1 true (4)),
(.last 17 (5,true)),
(.side 13 1 true (3)),
(.last 17 (5,true)),
(.side 13 1 true (3))])
theorem checked_21 : check 75 p_21 cert_21 = true := by decide +kernel
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 75 m := sound 75 _ cert_21 (by decide) checked_21
def p_22 := refine parent (4,true) (some ⟨true,false,5⟩)
def cert_22 : Tree := (split 13 (5,false) 6 #[
(.side 17 1 true (3)),
(.side 64 15 true (-1)),
(.side 6 32 false (2)),
(.side 3 11 true (-1)),
(.side 1 13 false (2)),
(.side 37 1 true (-1)),
(.side 7 11 false (2)),
(.side 18 1 true (2)),
(.side 18 21 false (0)),
(.side 15 1 true (3)),
(.side 36 12 false (-1)),
(.side 15 1 true (3)),
(.side 16 15 false (0)),
(.side 17 1 true (3)),
(.side 16 15 false (0)),
(.side 18 17 false (0)),
(.side 11 4 true (0)),
(.side 12 2 true (1)),
(.side 17 3 false (-1)),
(.last 15 (5,true)),
(.last 15 (5,true)),
(.last 14 (5,true)),
(.last 15 (5,true)),
(.last 14 (5,true))])
theorem checked_22 : check 75 p_22 cert_22 = true := by decide +kernel
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 75 m := sound 75 _ cert_22 (by decide) checked_22
def p_23 := refine parent (4,true) (some ⟨true,true,5⟩)
def cert_23 : Tree := (split 13 (5,false) 6 #[
(.last 63 (5,true)),
(.side 0 14 true (-1)),
(.last 57 (5,true)),
(.side 122 17 true (1)),
(.side 37 1 true (-1)),
(.side 143 1 true (9)),
(.last 51 (5,true)),
(.side 129 1 true (9)),
(.side 15 1 true (3)),
(.side 81 1 true (9)),
(.side 12 3 true (2)),
(.side 2 12 true (-1)),
(.side 17 1 true (3)),
(.side 52 1 true (4)),
(.side 12 5 true (1)),
(.side 4 10 true (-1)),
(.side 12 2 true (2)),
(.side 14 1 true (4)),
(.last 15 (5,true)),
(.side 14 1 true (4)),
(.last 14 (5,true)),
(.side 13 1 true (3)),
(.last 14 (5,true)),
(.side 13 1 true (3))])
theorem checked_23 : check 75 p_23 cert_23 = true := by decide +kernel
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 75 m := sound 75 _ cert_23 (by decide) checked_23
theorem safe : ∀ m, compatible parent m → WeightedBound 75 m := by
  apply split_safe 75 parent 12 (4,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23 | omega
theorem cover : Cover (WeightedBound 75) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra95

namespace BB6.Agent47Extra96
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,false,4⟩)
  | _,_ => none)
def p_0 := refine parent (4,true) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.side 6 46 false (3))
theorem checked_0 : check 58 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 58 m := sound 58 _ cert_0 (by decide) checked_0
def p_1 := refine parent (4,true) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 7 12 false (1))
theorem checked_1 : check 58 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 58 m := sound 58 _ cert_1 (by decide) checked_1
def p_2 := refine parent (4,true) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 7 8 false (1))
theorem checked_2 : check 58 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 58 m := sound 58 _ cert_2 (by decide) checked_2
def p_3 := refine parent (4,true) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 5 9 false (2))
theorem checked_3 : check 58 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 58 m := sound 58 _ cert_3 (by decide) checked_3
def p_4 := refine parent (4,true) (some ⟨false,false,1⟩)
def cert_4 : Tree := (.side 7 16 false (1))
theorem checked_4 : check 58 p_4 cert_4 = true := by decide +kernel
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 58 m := sound 58 _ cert_4 (by decide) checked_4
def p_5 := refine parent (4,true) (some ⟨false,true,1⟩)
def cert_5 : Tree := (.side 7 10 false (1))
theorem checked_5 : check 58 p_5 cert_5 = true := by decide +kernel
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 58 m := sound 58 _ cert_5 (by decide) checked_5
def p_6 := refine parent (4,true) (some ⟨true,false,1⟩)
def cert_6 : Tree := (.side 6 78 false (3))
theorem checked_6 : check 58 p_6 cert_6 = true := by decide +kernel
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 58 m := sound 58 _ cert_6 (by decide) checked_6
def p_7 := refine parent (4,true) (some ⟨true,true,1⟩)
def cert_7 : Tree := (.side 7 7 false (1))
theorem checked_7 : check 58 p_7 cert_7 = true := by decide +kernel
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 58 m := sound 58 _ cert_7 (by decide) checked_7
def p_8 := refine parent (4,true) (some ⟨false,false,2⟩)
def cert_8 : Tree := (.side 0 15 false (2))
theorem checked_8 : check 58 p_8 cert_8 = true := by decide +kernel
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 58 m := sound 58 _ cert_8 (by decide) checked_8
def p_9 := refine parent (4,true) (some ⟨false,true,2⟩)
def cert_9 : Tree := (.side 17 1 false (3))
theorem checked_9 : check 58 p_9 cert_9 = true := by decide +kernel
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 58 m := sound 58 _ cert_9 (by decide) checked_9
def p_10 := refine parent (4,true) (some ⟨true,false,2⟩)
def cert_10 : Tree := (.side 2 17 false (2))
theorem checked_10 : check 58 p_10 cert_10 = true := by decide +kernel
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 58 m := sound 58 _ cert_10 (by decide) checked_10
def p_11 := refine parent (4,true) (some ⟨true,true,2⟩)
def cert_11 : Tree := (.side 28 21 false (2))
theorem checked_11 : check 58 p_11 cert_11 = true := by decide +kernel
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 58 m := sound 58 _ cert_11 (by decide) checked_11
def p_12 := refine parent (4,true) (some ⟨false,false,3⟩)
def cert_12 : Tree := (.side 7 9 false (1))
theorem checked_12 : check 58 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 58 m := sound 58 _ cert_12 (by decide) checked_12
def p_13 := refine parent (4,true) (some ⟨false,true,3⟩)
def cert_13 : Tree := (.side 18 13 true (1))
theorem checked_13 : check 58 p_13 cert_13 = true := by decide +kernel
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 58 m := sound 58 _ cert_13 (by decide) checked_13
def p_14 := refine parent (4,true) (some ⟨true,false,3⟩)
def cert_14 : Tree := (.side 7 9 false (1))
theorem checked_14 : check 58 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 58 m := sound 58 _ cert_14 (by decide) checked_14
def p_15 := refine parent (4,true) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 7 11 false (1))
theorem checked_15 : check 58 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 58 m := sound 58 _ cert_15 (by decide) checked_15
def p_16 := refine parent (4,true) (some ⟨false,false,4⟩)
def cert_16 : Tree := (.side 14 1 false (-2))
theorem checked_16 : check 58 p_16 cert_16 = true := by decide +kernel
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 58 m := sound 58 _ cert_16 (by decide) checked_16
def p_17 := refine parent (4,true) (some ⟨false,true,4⟩)
def cert_17 : Tree := (.side 17 1 false (3))
theorem checked_17 : check 58 p_17 cert_17 = true := by decide +kernel
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 58 m := sound 58 _ cert_17 (by decide) checked_17
def p_18 := refine parent (4,true) (some ⟨true,false,4⟩)
def cert_18 : Tree := (.side 14 1 false (-2))
theorem checked_18 : check 58 p_18 cert_18 = true := by decide +kernel
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 58 m := sound 58 _ cert_18 (by decide) checked_18
def p_19 := refine parent (4,true) (some ⟨true,true,4⟩)
def cert_19 : Tree := (.side 15 3 true (1))
theorem checked_19 : check 58 p_19 cert_19 = true := by decide +kernel
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 58 m := sound 58 _ cert_19 (by decide) checked_19
def p_20 := refine parent (4,true) (some ⟨false,false,5⟩)
def cert_20 : Tree := (split 14 (5,false) 6 #[
(.side 0 15 false (2)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 14 false (1)),
(.side 7 17 false (1)),
(.side 36 25 false (2)),
(.side 9 6 false (1)),
(.last 24 (5,true)),
(.side 0 16 false (2)),
(.last 28 (5,true)),
(.last 22 (5,true)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 7 10 false (1)),
(.side 7 10 false (1)),
(.side 7 14 false (1)),
(.side 15 1 false (-3)),
(.side 15 1 false (-1)),
(.side 15 1 false (-3)),
(.side 12 3 false (0)),
(.side 14 1 false (-2)),
(.last 16 (5,true)),
(.side 14 1 false (-2)),
(.last 16 (5,true))])
theorem checked_20 : check 58 p_20 cert_20 = true := by decide +kernel
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 58 m := sound 58 _ cert_20 (by decide) checked_20
def p_21 := refine parent (4,true) (some ⟨false,true,5⟩)
def cert_21 : Tree := (split 14 (5,true) 6 #[
(.last 19 (5,false)),
(.side 15 15 false (2)),
(.side 7 9 false (1)),
(.side 5 10 true (-1)),
(.side 7 17 false (1)),
(.side 7 11 false (1)),
(.last 28 (5,false)),
(.side 7 8 true (-1)),
(.side 0 16 false (2)),
(.last 17 (5,false)),
(.last 52 (5,false)),
(.last 17 (5,false)),
(.side 7 10 false (1)),
(.last 19 (5,false)),
(.side 7 10 false (1)),
(.side 7 12 false (1)),
(.side 15 1 false (-1)),
(.side 17 1 false (3)),
(.side 15 1 false (-1)),
(.side 15 3 true (1)),
(.last 15 (5,false)),
(.last 17 (5,false)),
(.last 15 (5,false)),
(.last 17 (5,false))])
theorem checked_21 : check 58 p_21 cert_21 = true := by decide +kernel
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 58 m := sound 58 _ cert_21 (by decide) checked_21
def p_22 := refine parent (4,true) (some ⟨true,false,5⟩)
def cert_22 : Tree := (split 14 (5,false) 6 #[
(.side 3 17 false (2)),
(.side 7 13 false (1)),
(.side 7 9 false (1)),
(.side 5 10 false (2)),
(.side 7 17 false (1)),
(.side 7 11 false (1)),
(.side 7 15 false (1)),
(.side 7 8 false (1)),
(.side 0 16 false (2)),
(.side 25 1 false (3)),
(.side 13 12 false (-1)),
(.last 28 (5,true)),
(.side 7 10 false (1)),
(.last 36 (5,true)),
(.side 7 10 false (1)),
(.side 7 12 false (1)),
(.side 15 1 false (-3)),
(.side 13 2 true (-2)),
(.side 15 1 false (-3)),
(.last 16 (5,true)),
(.side 14 1 false (-2)),
(.last 15 (5,true)),
(.side 14 1 false (-2)),
(.last 15 (5,true))])
theorem checked_22 : check 58 p_22 cert_22 = true := by decide +kernel
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 58 m := sound 58 _ cert_22 (by decide) checked_22
def p_23 := refine parent (4,true) (some ⟨true,true,5⟩)
def cert_23 : Tree := (split 14 (5,true) 6 #[
(.side 7 15 false (1)),
(.side 15 19 false (2)),
(.side 7 13 false (1)),
(.side 15 17 false (2)),
(.side 7 11 false (1)),
(.side 7 15 false (1)),
(.side 7 11 false (1)),
(.side 7 13 false (1)),
(.side 16 1 false (0)),
(.last 17 (5,false)),
(.last 23 (5,false)),
(.last 17 (5,false)),
(.side 8 7 false (1)),
(.last 19 (5,false)),
(.last 29 (5,false)),
(.side 6 9 false (2)),
(.last 16 (5,false)),
(.last 22 (5,false)),
(.side 13 2 true (-1)),
(.side 15 3 true (1)),
(.last 16 (5,false)),
(.last 17 (5,false)),
(.last 16 (5,false)),
(.last 17 (5,false))])
theorem checked_23 : check 58 p_23 cert_23 = true := by decide +kernel
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 58 m := sound 58 _ cert_23 (by decide) checked_23
theorem safe : ∀ m, compatible parent m → WeightedBound 58 m := by
  apply split_safe 58 parent 13 (4,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23 | omega
theorem cover : Cover (WeightedBound 58) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra96

namespace BB6.Agent47Extra97
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,true,4⟩)
  | _,_ => none)
def p_0 := refine parent (4,true) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.side 4 42 false (2))
theorem checked_0 : check 58 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 58 m := sound 58 _ cert_0 (by decide) checked_0
def p_1 := refine parent (4,true) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 0 13 true (-1))
theorem checked_1 : check 58 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 58 m := sound 58 _ cert_1 (by decide) checked_1
def p_2 := refine parent (4,true) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 4 36 false (2))
theorem checked_2 : check 58 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 58 m := sound 58 _ cert_2 (by decide) checked_2
def p_3 := refine parent (4,true) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 6 24 true (-1))
theorem checked_3 : check 58 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 58 m := sound 58 _ cert_3 (by decide) checked_3
def p_4 := refine parent (4,true) (some ⟨false,false,1⟩)
def cert_4 : Tree := (.side 31 1 true (-1))
theorem checked_4 : check 58 p_4 cert_4 = true := by decide +kernel
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 58 m := sound 58 _ cert_4 (by decide) checked_4
def p_5 := refine parent (4,true) (some ⟨false,true,1⟩)
def cert_5 : Tree := (.side 71 1 true (7))
theorem checked_5 : check 58 p_5 cert_5 = true := by decide +kernel
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 58 m := sound 58 _ cert_5 (by decide) checked_5
def p_6 := refine parent (4,true) (some ⟨true,false,1⟩)
def cert_6 : Tree := (.side 4 30 false (2))
theorem checked_6 : check 58 p_6 cert_6 = true := by decide +kernel
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 58 m := sound 58 _ cert_6 (by decide) checked_6
def p_7 := refine parent (4,true) (some ⟨true,true,1⟩)
def cert_7 : Tree := (.side 65 1 true (7))
theorem checked_7 : check 58 p_7 cert_7 = true := by decide +kernel
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 58 m := sound 58 _ cert_7 (by decide) checked_7
def p_8 := refine parent (4,true) (some ⟨false,false,2⟩)
def cert_8 : Tree := (.side 14 1 true (2))
theorem checked_8 : check 58 p_8 cert_8 = true := by decide +kernel
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 58 m := sound 58 _ cert_8 (by decide) checked_8
def p_9 := refine parent (4,true) (some ⟨false,true,2⟩)
def cert_9 : Tree := (.side 75 1 true (7))
theorem checked_9 : check 58 p_9 cert_9 = true := by decide +kernel
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 58 m := sound 58 _ cert_9 (by decide) checked_9
def p_10 := refine parent (4,true) (some ⟨true,false,2⟩)
def cert_10 : Tree := (.side 19 1 true (3))
theorem checked_10 : check 58 p_10 cert_10 = true := by decide +kernel
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 58 m := sound 58 _ cert_10 (by decide) checked_10
def p_11 := refine parent (4,true) (some ⟨true,true,2⟩)
def cert_11 : Tree := (.side 2 11 true (-1))
theorem checked_11 : check 58 p_11 cert_11 = true := by decide +kernel
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 58 m := sound 58 _ cert_11 (by decide) checked_11
def p_12 := refine parent (4,true) (some ⟨false,false,3⟩)
def cert_12 : Tree := (.side 16 1 true (2))
theorem checked_12 : check 58 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 58 m := sound 58 _ cert_12 (by decide) checked_12
def p_13 := refine parent (4,true) (some ⟨false,true,3⟩)
def cert_13 : Tree := (.side 4 42 false (3))
theorem checked_13 : check 58 p_13 cert_13 = true := by decide +kernel
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 58 m := sound 58 _ cert_13 (by decide) checked_13
def p_14 := refine parent (4,true) (some ⟨true,false,3⟩)
def cert_14 : Tree := (.side 4 13 false (2))
theorem checked_14 : check 58 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 58 m := sound 58 _ cert_14 (by decide) checked_14
def p_15 := refine parent (4,true) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 4 9 true (-1))
theorem checked_15 : check 58 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 58 m := sound 58 _ cert_15 (by decide) checked_15
def p_16 := refine parent (4,true) (some ⟨false,false,4⟩)
def cert_16 : Tree := (.side 14 1 true (0))
theorem checked_16 : check 58 p_16 cert_16 = true := by decide +kernel
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 58 m := sound 58 _ cert_16 (by decide) checked_16
def p_17 := refine parent (4,true) (some ⟨false,true,4⟩)
def cert_17 : Tree := (.side 13 1 true (3))
theorem checked_17 : check 58 p_17 cert_17 = true := by decide +kernel
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 58 m := sound 58 _ cert_17 (by decide) checked_17
def p_18 := refine parent (4,true) (some ⟨true,false,4⟩)
def cert_18 : Tree := (.side 16 3 false (0))
theorem checked_18 : check 58 p_18 cert_18 = true := by decide +kernel
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 58 m := sound 58 _ cert_18 (by decide) checked_18
def p_19 := refine parent (4,true) (some ⟨true,true,4⟩)
def cert_19 : Tree := (.side 13 1 true (3))
theorem checked_19 : check 58 p_19 cert_19 = true := by decide +kernel
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 58 m := sound 58 _ cert_19 (by decide) checked_19
def p_20 := refine parent (4,true) (some ⟨false,false,5⟩)
def cert_20 : Tree := (split 13 (5,true) 6 #[
(.side 22 19 false (0)),
(.side 0 14 true (-1)),
(.side 16 17 false (0)),
(.side 75 1 true (7)),
(.side 1 13 false (2)),
(.side 24 25 false (1)),
(.side 16 1 true (2)),
(.side 1 13 true (-1)),
(.side 31 1 true (-1)),
(.side 0 15 true (-1)),
(.last 32 (5,false)),
(.side 4 48 false (2)),
(.side 31 1 true (-1)),
(.side 20 1 true (2)),
(.last 32 (5,false)),
(.side 4 42 false (2)),
(.side 14 1 true (0)),
(.side 14 1 true (2)),
(.last 18 (5,false)),
(.side 14 1 true (2)),
(.last 14 (5,false)),
(.last 14 (5,false)),
(.last 14 (5,false)),
(.last 14 (5,false))])
theorem checked_20 : check 58 p_20 cert_20 = true := by decide +kernel
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 58 m := sound 58 _ cert_20 (by decide) checked_20
def p_21 := refine parent (4,true) (some ⟨false,true,5⟩)
def cert_21 : Tree := (split 13 (5,false) 6 #[
(.side 75 1 true (7)),
(.side 0 14 true (-1)),
(.side 4 42 false (3)),
(.last 52 (5,true)),
(.side 1 13 true (-1)),
(.side 20 54 false (4)),
(.side 16 1 true (4)),
(.side 1 13 true (-1)),
(.side 4 48 false (3)),
(.side 0 15 true (-1)),
(.last 45 (5,true)),
(.side 71 1 true (7)),
(.side 4 42 false (3)),
(.side 20 1 true (4)),
(.last 41 (5,true)),
(.side 16 48 false (4)),
(.side 14 1 true (2)),
(.side 14 1 true (4)),
(.side 11 3 true (1)),
(.side 14 1 true (4)),
(.last 15 (5,true)),
(.side 13 1 true (3)),
(.last 15 (5,true)),
(.side 13 1 true (3))])
theorem checked_21 : check 58 p_21 cert_21 = true := by decide +kernel
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 58 m := sound 58 _ cert_21 (by decide) checked_21
def p_22 := refine parent (4,true) (some ⟨true,false,5⟩)
def cert_22 : Tree := (split 13 (5,true) 6 #[
(.side 17 1 true (3)),
(.side 22 23 false (1)),
(.side 16 17 false (0)),
(.side 3 11 true (-1)),
(.side 1 13 false (2)),
(.side 18 19 false (0)),
(.last 17 (5,false)),
(.side 18 1 true (2)),
(.side 18 25 false (0)),
(.side 15 1 true (3)),
(.last 32 (5,false)),
(.side 15 1 true (3)),
(.side 4 30 false (2)),
(.side 17 1 true (3)),
(.last 32 (5,false)),
(.side 4 36 false (2)),
(.last 25 (5,false)),
(.last 15 (5,false)),
(.last 18 (5,false)),
(.side 12 2 true (1)),
(.last 14 (5,false)),
(.last 15 (5,false)),
(.last 14 (5,false)),
(.last 15 (5,false))])
theorem checked_22 : check 58 p_22 cert_22 = true := by decide +kernel
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 58 m := sound 58 _ cert_22 (by decide) checked_22
def p_23 := refine parent (4,true) (some ⟨true,true,5⟩)
def cert_23 : Tree := (split 13 (5,false) 6 #[
(.side 3 11 true (-1)),
(.side 0 14 true (-1)),
(.side 5 9 true (-1)),
(.side 17 23 false (6)),
(.side 18 1 true (2)),
(.side 4 28 true (-1)),
(.side 7 7 true (-1)),
(.side 6 24 true (-1)),
(.side 15 1 true (3)),
(.side 32 1 true (6)),
(.side 12 3 true (2)),
(.side 65 1 true (7)),
(.side 4 36 false (3)),
(.side 6 11 true (-1)),
(.last 37 (5,true)),
(.side 16 42 false (4)),
(.side 12 2 true (2)),
(.side 14 1 true (4)),
(.last 15 (5,true)),
(.side 14 1 true (4)),
(.last 14 (5,true)),
(.side 13 1 true (3)),
(.last 14 (5,true)),
(.side 13 1 true (3))])
theorem checked_23 : check 58 p_23 cert_23 = true := by decide +kernel
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 58 m := sound 58 _ cert_23 (by decide) checked_23
theorem safe : ∀ m, compatible parent m → WeightedBound 58 m := by
  apply split_safe 58 parent 12 (4,true) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23 | omega
theorem cover : Cover (WeightedBound 58) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra97

namespace BB6.Agent47Extra98
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | _,_ => none)
def p_0 := refine parent (5,false) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.side 7 13 false (1))
theorem checked_0 : check 32 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 32 m := sound 32 _ cert_0 (by decide) checked_0
def p_1 := refine parent (5,false) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 0 20 true (-1))
theorem checked_1 : check 32 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 32 m := sound 32 _ cert_1 (by decide) checked_1
def p_2 := refine parent (5,false) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 7 11 false (1))
theorem checked_2 : check 32 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 32 m := sound 32 _ cert_2 (by decide) checked_2
def p_3 := refine parent (5,false) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 6 9 false (2))
theorem checked_3 : check 32 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 32 m := sound 32 _ cert_3 (by decide) checked_3
def p_4 := refine parent (5,false) (some ⟨false,false,1⟩)
def cert_4 : Tree := (.side 7 9 false (1))
theorem checked_4 : check 32 p_4 cert_4 = true := by decide +kernel
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 32 m := sound 32 _ cert_4 (by decide) checked_4
def p_5 := refine parent (5,false) (some ⟨false,true,1⟩)
def cert_5 : Tree := (.side 24 19 false (2))
theorem checked_5 : check 32 p_5 cert_5 = true := by decide +kernel
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 32 m := sound 32 _ cert_5 (by decide) checked_5
def p_6 := refine parent (5,false) (some ⟨true,false,1⟩)
def cert_6 : Tree := (.side 7 9 false (1))
theorem checked_6 : check 32 p_6 cert_6 = true := by decide +kernel
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 32 m := sound 32 _ cert_6 (by decide) checked_6
def p_7 := refine parent (5,false) (some ⟨true,true,1⟩)
def cert_7 : Tree := (.side 24 17 false (2))
theorem checked_7 : check 32 p_7 cert_7 = true := by decide +kernel
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 32 m := sound 32 _ cert_7 (by decide) checked_7
def p_8 := refine parent (5,false) (some ⟨false,false,2⟩)
def cert_8 : Tree := (.side 0 17 false (2))
theorem checked_8 : check 32 p_8 cert_8 = true := by decide +kernel
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 32 m := sound 32 _ cert_8 (by decide) checked_8
def p_9 := refine parent (5,false) (some ⟨false,true,2⟩)
def cert_9 : Tree := (.side 28 19 false (2))
theorem checked_9 : check 32 p_9 cert_9 = true := by decide +kernel
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 32 m := sound 32 _ cert_9 (by decide) checked_9
def p_10 := refine parent (5,false) (some ⟨true,false,2⟩)
def cert_10 : Tree := (split 14 (4,true) 6 #[
(.side 0 15 false (2)),
(.side 0 24 true (-1)),
(.side 7 9 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,2),(true,1)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 17 false (1)),
(.side 15 17 false (4)),
(.side 9 6 true (-1)),
(.side 1 20 true (-1)),
(.side 0 16 false (2)),
(.side 0 24 true (-1)),
(.side 7 24 false (1)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 7 10 true (-1)),
(.side 7 10 false (1)),
(.side 7 14 false (1)),
(.last 26 (5,true)),
(.side 7 28 false (1)),
(.last 26 (5,true)),
(.last 16 (5,true)),
(.side 12 12 false (0)),
(.side 19 9 true (1)),
(.side 12 12 false (0)),
(.last 18 (5,true))])
theorem checked_10 : check 32 p_10 cert_10 = true := by decide +kernel
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 32 m := sound 32 _ cert_10 (by decide) checked_10
def p_11 := refine parent (5,false) (some ⟨true,true,2⟩)
def cert_11 : Tree := (.side 2 11 false (2))
theorem checked_11 : check 32 p_11 cert_11 = true := by decide +kernel
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 32 m := sound 32 _ cert_11 (by decide) checked_11
def p_12 := refine parent (5,false) (some ⟨false,false,3⟩)
def cert_12 : Tree := (.side 8 5 false (1))
theorem checked_12 : check 32 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 32 m := sound 32 _ cert_12 (by decide) checked_12
def p_13 := refine parent (5,false) (some ⟨false,true,3⟩)
def cert_13 : Tree := (.side 7 13 false (1))
theorem checked_13 : check 32 p_13 cert_13 = true := by decide +kernel
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 32 m := sound 32 _ cert_13 (by decide) checked_13
def p_14 := refine parent (5,false) (some ⟨true,false,3⟩)
def cert_14 : Tree := (split 16 (4,true) 6 #[
(.side 7 22 false (1)),
(.side 0 28 true (-2)),
(.side 7 16 false (1)),
(.side 18 56 false (2)),
(.side 1 16 false (2)),
(.side 39 24 false (-1)),
(.side 7 18 false (1)),
(.side 25 26 false (-1)),
(.side 7 18 false (1)),
(.side 27 28 false (-1)),
(.side 7 18 false (1)),
(.side 7 22 false (1)),
(.side 7 16 false (1)),
(.side 7 22 false (1)),
(.side 7 16 false (1)),
(.side 7 20 false (1)),
(.last 18 (5,true)),
(.side 7 18 false (1)),
(.last 18 (5,true)),
(.last 18 (5,true)),
(.side 12 5 false (0)),
(.side 7 18 false (1)),
(.side 12 5 false (0)),
(.last 22 (5,true))])
theorem checked_14 : check 32 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 32 m := sound 32 _ cert_14 (by decide) checked_14
def p_15 := refine parent (5,false) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 4 9 false (2))
theorem checked_15 : check 32 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 32 m := sound 32 _ cert_15 (by decide) checked_15
def p_16 := refine parent (5,false) (some ⟨false,false,4⟩)
def cert_16 : Tree := (split 13 (4,true) 6 #[
(.side 0 14 false (2)),
(.side 0 20 true (-1)),
(.side 7 8 false (1)),
(.side 28 19 false (2)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (1)),
(.side 1 13 false (2)),
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.side 13 9 false (0)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.side 14 2 false (-2)),
(.side 14 2 false (0)),
(.side 14 2 false (-2)),
(.last 15 (5,true)),
(.side 14 2 false (-2)),
(.side 14 2 false (0)),
(.side 14 2 false (-2)),
(.side 12 2 true (-1))])
theorem checked_16 : check 32 p_16 cert_16 = true := by decide +kernel
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 32 m := sound 32 _ cert_16 (by decide) checked_16
def p_17 := refine parent (5,false) (some ⟨false,true,4⟩)
def cert_17 : Tree := (.side 11 2 true (0))
theorem checked_17 : check 32 p_17 cert_17 = true := by decide +kernel
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 32 m := sound 32 _ cert_17 (by decide) checked_17
def p_18 := refine parent (5,false) (some ⟨true,false,4⟩)
def cert_18 : Tree := (split 13 (4,true) 6 #[
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 7 8 false (1)),
(.side 3 11 false (2)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 7 18 false (1)),
(.side 7 7 false (1)),
(.side 0 15 false (2)),
(.side 15 2 false (1)),
(.side 2 17 false (2)),
(.side 10 4 true (-1)),
(.side 7 9 false (1)),
(.side 8 6 true (-1)),
(.side 7 9 false (1)),
(.side 7 11 false (1)),
(.side 14 2 false (-2)),
(.side 15 2 false (1)),
(.side 14 2 false (-2)),
(.last 16 (5,true)),
(.side 14 2 false (-2)),
(.last 14 (5,true)),
(.side 14 2 false (-2)),
(.last 14 (5,true))])
theorem checked_18 : check 32 p_18 cert_18 = true := by decide +kernel
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 32 m := sound 32 _ cert_18 (by decide) checked_18
def p_19 := refine parent (5,false) (some ⟨true,true,4⟩)
def cert_19 : Tree := (split 14 (5,true) 6 #[
(.side 7 15 false (1)),
(.side 0 24 true (-1)),
(.side 7 13 false (1)),
(.side 6 11 false (2)),
(.side 7 11 false (1)),
(.side 28 21 false (2)),
(.side 7 11 false (1)),
(.side 28 19 false (2)),
(.side 0 21 false (2)),
(.side 32 21 false (2)),
(.last 16 (4,true)),
(.side 2 13 false (2)),
(.side 8 7 false (1)),
(.side 7 15 false (1)),
(.last 18 (4,true)),
(.side 4 11 false (2)),
(.last 15 (4,true)),
(.side 11 4 true (0)),
(.last 15 (4,true)),
(.side 13 2 true (0)),
(.side 15 3 false (-1)),
(.last 16 (4,true)),
(.last 17 (4,true)),
(.last 16 (4,true))])
theorem checked_19 : check 32 p_19 cert_19 = true := by decide +kernel
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 32 m := sound 32 _ cert_19 (by decide) checked_19
def p_20 := refine parent (5,false) (some ⟨false,false,5⟩)
def cert_20 : Tree := (split 13 (5,true) 6 #[
(.side 0 14 false (2)),
(.side 0 20 true (-1)),
(.side 7 8 false (1)),
(.side 28 19 false (2)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 9 5 false (1)),
(.side 1 13 false (2)),
(.side 0 15 false (2)),
(.side 0 15 false (2)),
(.last 22 (4,true)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.side 15 1 false (-3)),
(.side 15 1 false (-1)),
(.side 15 1 false (-3)),
(.side 13 2 true (-1)),
(.side 14 1 false (-2)),
(.side 14 1 false (0)),
(.side 14 1 false (-2)),
(.side 12 2 true (-1))])
theorem checked_20 : check 32 p_20 cert_20 = true := by decide +kernel
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 32 m := sound 32 _ cert_20 (by decide) checked_20
def p_21 := refine parent (5,false) (some ⟨false,true,5⟩)
def cert_21 : Tree := (split 14 (5,true) 6 #[
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
(.side 16 1 true (0)),
(.side 16 1 true (2)),
(.side 11 4 true (0)),
(.side 14 2 true (2)),
(.side 15 1 true (1)),
(.side 15 1 true (3)),
(.side 13 2 true (1)),
(.side 15 1 true (3))])
theorem checked_21 : check 32 p_21 cert_21 = true := by decide +kernel
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 32 m := sound 32 _ cert_21 (by decide) checked_21
def p_22 := refine parent (5,false) (some ⟨true,false,5⟩)
def cert_22 : Tree := (split 13 (5,true) 6 #[
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 7 8 false (1)),
(.side 3 11 false (2)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.last 16 (4,true)),
(.side 7 7 false (1)),
(.side 0 15 false (2)),
(.side 16 1 false (0)),
(.last 18 (4,true)),
(.side 10 4 true (-1)),
(.side 7 9 false (1)),
(.side 8 6 true (-1)),
(.side 7 9 false (1)),
(.side 7 11 false (1)),
(.side 15 1 false (-3)),
(.last 14 (4,true)),
(.side 15 1 false (-3)),
(.last 14 (4,true)),
(.side 14 1 false (-2)),
(.side 15 1 false (1)),
(.side 14 1 false (-2)),
(.side 17 3 true (1))])
theorem checked_22 : check 32 p_22 cert_22 = true := by decide +kernel
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 32 m := sound 32 _ cert_22 (by decide) checked_22
def p_23 := refine parent (5,false) (some ⟨true,true,5⟩)
def cert_23 : Tree := (split 14 (5,true) 6 #[
(.side 6 32 false (2)),
(.side 0 15 true (-1)),
(.side 6 28 false (2)),
(.side 22 13 false (4)),
(.side 6 24 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3),(true,2)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.side 6 24 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.side 17 1 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.last 16 (4,true)),
(.side 6 15 false (3)),
(.side 6 9 false (2)),
(.side 6 32 false (3)),
(.side 6 9 false (2)),
(.side 6 13 false (3)),
(.last 15 (4,true)),
(.side 16 1 true (2)),
(.last 15 (4,true)),
(.side 14 2 true (2)),
(.side 18 1 true (-2)),
(.side 15 1 true (3)),
(.side 16 3 false (0)),
(.side 15 1 true (3))])
theorem checked_23 : check 32 p_23 cert_23 = true := by decide +kernel
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 32 m := sound 32 _ cert_23 (by decide) checked_23
theorem safe : ∀ m, compatible parent m → WeightedBound 32 m := by
  apply split_safe 32 parent 12 (5,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23 | omega
theorem cover : Cover (WeightedBound 32) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra98

namespace BB6.Agent47Extra99
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,false,0⟩)
  | _,_ => none)
def cert : Tree := (split 19 (5,false) 6 #[
(.side 0 20 true (-1)),
(.side 0 20 true (-1)),
(.side 13 7 true (0)),
(.side 27 21 false (5)),
(.side 4 23 false (3)),
(.side 13 24 true (0)),
(.side 16 4 true (0)),
(.side 1 19 true (-1)),
(.side 6 23 false (3)),
(.side 0 21 true (-1)),
(.side 16 6 true (0)),
(.side 6 23 false (4)),
(.side 6 17 false (3)),
(.side 13 8 true (0)),
(.side 6 17 false (3)),
(.side 6 21 false (4)),
(.side 18 2 true (2)),
(.side 18 2 true (2)),
(.side 11 9 true (0)),
(.side 18 2 true (2)),
(.side 27 10 false (-1)),
(.side 19 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6),(false,4)],[(true,2),(true,6),(true,4)],[(false,5),(false,3),(false,7)],[(true,5),(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch .empty .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))))]⟩),
(.side 19 1 true (3))])
theorem checked : check 25 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 25 m := sound 25 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 25) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra99

namespace BB6.Agent47Extra100
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,1⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none)
def cert : Tree := (.last 38 (4,true))
theorem checked : check 44 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 44 m := sound 44 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 44) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra100

namespace BB6.Agent47Extra101
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,false,2⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none)
def cert : Tree := (.last 40 (4,true))
theorem checked : check 46 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 46 m := sound 46 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 46) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra101

namespace BB6.Agent47Extra102
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none)
def cert : Tree := (.last 36 (4,true))
theorem checked : check 42 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 42 m := sound 42 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 42) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra102

namespace BB6.Agent47Extra103
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | 5,true => some (some ⟨true,true,0⟩)
  | _,_ => none)
def cert : Tree := (.last 36 (4,true))
theorem checked : check 42 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 42 m := sound 42 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 42) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra103

namespace BB6.Agent47Extra104
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,false,1⟩)
  | _,_ => none)
def cert : Tree := (split 31 (5,false) 6 #[
(.side 4 56 false (2)),
(.side 45 13 true (-2)),
(.side 4 42 false (2)),
(.side 16 33 false (2)),
(.side 13 19 false (2)),
(.side 41 24 true (1)),
(.last 34 (4,true)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0)],[(false,2),(false,6)],[(true,2)],[(false,3)],[(true,3)],[],[(true,5)],[],[],[(true,8)]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch .empty (.branch .empty .leaf)))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),.empty,(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty)),(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))))]⟩),
(.side 22 19 false (0)),
(.side 0 54 true (-4)),
(.last 36 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[(false,4),(false,12)],[(true,4),(true,12)],[(false,5),(false,13),(false,9)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch .leaf (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)) .empty)]⟩),
(.side 22 13 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6),(false,4)],[(true,2),(true,6),(true,4)],[(false,5)],[(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty)]⟩),
(.side 22 13 false (0)),
(.side 22 15 false (0)),
(.side 30 2 true (-2)),
(.last 32 (4,true)),
(.side 11 21 false (2)),
(.last 32 (4,true)),
(.side 20 18 false (0)),
(.side 22 21 false (0)),
(.side 20 18 false (0)),
(.side 22 15 false (0))])
theorem checked : check 42 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 42 m := sound 42 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 42) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra104

namespace BB6.Agent47Extra105
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,1⟩)
  | _,_ => none)
def cert : Tree := (split 27 (5,false) 6 #[
(.side 0 33 true (-1)),
(.side 15 13 true (0)),
(.side 7 22 true (-1)),
(.side 3 25 true (-1)),
(.last 46 (4,true)),
(.side 13 24 true (0)),
(.last 30 (4,true)),
(.side 1 33 true (-1)),
(.last 46 (4,true)),
(.side 0 32 true (-1)),
(.last 32 (4,true)),
(.last 68 (4,true)),
(.side 6 25 false (4)),
(.side 28 8 true (3)),
(.last 40 (4,true)),
(.side 6 27 false (4)),
(.side 26 2 true (2)),
(.last 28 (4,true)),
(.side 11 28 true (0)),
(.last 28 (4,true)),
(.side 38 18 false (0)),
(.side 12 16 true (0)),
(.side 35 12 false (-1)),
(.side 35 31 false (5))])
theorem checked : check 74 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 74 m := sound 74 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 74) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra105

namespace BB6.Agent47Extra106
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,false,1⟩)
  | _,_ => none)
def cert : Tree := (split 16 (5,false) 6 #[
(.side 0 17 true (-1)),
(.side 0 17 true (-1)),
(.side 13 7 true (1)),
(.last 56 (4,true)),
(.side 24 19 false (2)),
(.side 13 24 true (1)),
(.side 13 4 true (1)),
(.side 1 16 true (-1)),
(.side 30 19 false (0)),
(.side 0 18 true (-1)),
(.side 13 6 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6),(false,8)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))]⟩),
(.side 24 13 false (0)),
(.side 13 8 true (1)),
(.side 24 13 false (0)),
(.side 28 15 false (0)),
(.side 15 2 true (3)),
(.side 15 2 true (3)),
(.side 11 6 true (1)),
(.side 15 2 true (3)),
(.side 32 7 false (-1)),
(.side 16 1 true (4)),
(.last 22 (4,true)),
(.side 16 1 true (4))])
theorem checked : check 62 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 62 m := sound 62 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 62) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra106

namespace BB6.Agent47Extra107
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,false,2⟩)
  | _,_ => none)
def cert : Tree := (split 31 (5,false) 6 #[
(.side 6 56 false (2)),
(.side 45 13 true (-2)),
(.side 6 42 false (2)),
(.side 22 33 false (1)),
(.side 22 19 false (0)),
(.side 41 24 true (1)),
(.last 34 (4,true)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0)],[(false,2),(false,6)],[(true,2),(true,4)],[(false,3)],[(true,3)],[(false,4),(false,9)],[(true,5)],[(true,6),(true,9)],[(false,7)],[(true,8)]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[(false,4),(false,12)],[(true,12),(true,4)],[(false,5),(false,13)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch .empty .leaf)) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf))) .empty) (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch .empty (.branch .leaf .leaf))))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty))) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch .empty (.branch .leaf .leaf))))) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty))) .empty)) .empty)]⟩),
(.side 13 19 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,4),(false,6)],[(true,2),(true,4),(true,6)],[(false,3),(false,5),(false,7)],[(true,3),(true,5),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[(false,4)],[],[(false,5)],[],[],[],[],[],[(false,24)],[],[(false,25)],[],[(false,10),(false,26),(false,18)],[(true,10),(true,26),(true,18)],[],[],[(false,20)],[(true,20)],[(false,21)],[],[],[],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf)))) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf)))) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty)) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty)) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))) .empty)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty)) .empty)) .empty)),.empty,(.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)) .empty)]⟩),
(.last 36 (4,true)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4),(true,5),(true,3)],[(false,2),(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,6),(false,10),(false,9)],[],[(false,3)],[(true,3)],[],[],[(false,5)],[(true,5)],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,2),(3,14),(3,15),(7,16),(17,10),(18,6),(3,19),(7,20),(13,6),(7,14),(21,10),(7,22),(13,10),(13,14),(13,14)]⟩,#[(.branch (.branch (.branch .leaf (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .leaf)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .leaf) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))))),(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)))))),(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)))]⟩),
(.side 21 13 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,3),(true,1),(true,5),(true,7)],[(false,2)],[(true,2)],[(false,3)],[],[(false,5),(false,7)]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,6),(7,2)]⟩,#[(.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .leaf)))),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) .empty)) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))))]⟩),
(.side 21 13 false (1)),
(.side 21 15 false (1)),
(.side 30 2 true (-2)),
(.last 32 (4,true)),
(.side 11 21 false (2)),
(.last 32 (4,true)),
(.side 0 36 false (2)),
(.side 6 50 false (2)),
(.side 0 36 false (2)),
(.side 39 1 true (3))])
theorem checked : check 42 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 42 m := sound 42 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 42) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra107

namespace BB6.Agent47Extra108
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,false,2⟩)
  | _,_ => none)
def cert : Tree := (split 18 (5,false) 6 #[
(.side 0 19 true (-1)),
(.side 0 19 true (-1)),
(.side 15 7 true (1)),
(.last 58 (4,true)),
(.side 30 19 false (0)),
(.side 15 24 true (1)),
(.side 15 4 true (1)),
(.side 1 18 true (-1)),
(.side 28 19 false (2)),
(.side 0 20 true (-1)),
(.side 13 6 true (0)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4),(true,5),(true,3)],[(false,2),(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6),(false,8)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty))),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))))) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))))) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))))]⟩),
(.side 23 13 false (1)),
(.side 15 8 true (1)),
(.side 23 13 false (1)),
(.side 27 15 false (1)),
(.side 17 2 true (3)),
(.side 17 2 true (3)),
(.side 11 8 true (0)),
(.side 17 2 true (3)),
(.last 23 (4,true)),
(.side 18 1 true (4)),
(.last 23 (4,true)),
(.side 18 1 true (4))])
theorem checked : check 64 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 64 m := sound 64 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 64) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra108

namespace BB6.Agent47Extra109
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,true,2⟩)
  | _,_ => none)
def cert : Tree := (split 31 (5,false) 6 #[
(.side 134 107 false (2)),
(.side 58 13 true (-1)),
(.side 6 42 false (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4)],[(true,5)],[(true,3)],[(false,7)],[(false,8)],[(true,9),(true,18)],[(true,7)],[(false,10)],[(false,12)],[(true,13)],[(true,14)],[(true,12)],[(false,16)],[(false,17)],[(true,16)]],#[(0,1),(3,2),(0,0),(4,7),(0,5),(0,6),(0,0),(8,11),(9,0),(0,10),(12,0),(0,0),(13,16),(0,14),(0,15),(0,0),(17,19),(18,0),(0,10),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[(false,3)],[(true,3)],[(false,4),(false,7),(true,7),(false,8),(true,8),(false,10),(false,11),(true,11),(false,12),(true,13),(true,16),(false,18),(true,18),(false,19),(false,21),(false,22),(true,22),(false,23),(true,23),(true,26),(false,28),(true,28),(true,29),(false,30),(true,30),(false,32),(true,32),(false,33),(true,34),(false,35),(true,35),(false,38),(true,38)],[(true,4)],[(false,5)],[(true,5)],[(false,6)],[(true,6)],[(false,9)],[(true,9)],[(true,10)],[(true,12)],[(false,13)],[(false,14)],[(true,14)],[(false,15),(false,25)],[(true,15),(true,25)],[(false,16)],[(false,17)],[(true,17),(true,37)],[(true,19)],[(false,20)],[(true,20),(true,31)],[(true,21)],[(false,24),(false,39)],[(true,24),(true,39)],[(false,26)],[(false,27),(false,36)],[(true,27),(true,36)],[(false,29)],[(false,31)],[(true,33)],[(false,34)],[(false,37)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(8,8),(8,8),(14,15),(8,16),(8,8),(8,17),(18,8),(19,20),(21,22),(23,8),(24,25),(8,8),(8,26),(27,28),(8,29),(8,8),(8,8),(30,31),(21,22),(32,8),(33,34),(8,8),(35,8),(8,8),(36,28),(8,8),(8,37),(38,8),(8,8),(33,34),(39,25),(8,8),(30,31)]⟩,#[(.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty)) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .leaf (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .leaf) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .leaf (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch .leaf (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch .leaf (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))))) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .leaf (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .leaf (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty .leaf)) (.branch (.branch .leaf (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))))),.empty,(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)))) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) .empty))]⟩),
(.side 22 19 false (0)),
(.side 56 24 true (-1)),
(.last 34 (4,true)),
(.last 121 (4,true)),
(.side 21 19 false (1)),
(.side 0 39 true (-4)),
(.last 36 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[(true,4)],[(false,5)],[(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[],[(true,4),(true,12)],[(false,9)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch .leaf (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch .leaf (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .leaf) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) .empty)]⟩),
(.side 19 13 false (1)),
(.side 37 8 true (2)),
(.side 19 13 false (1)),
(.side 17 15 false (3)),
(.side 30 2 true (-2)),
(.last 32 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[(true,4)],[(false,5)],[(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[],[],[],[(true,4),(true,12)],[(false,9)],[(true,9)],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch .leaf (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch .leaf (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .leaf) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty))]⟩),
(.last 32 (4,true)),
(.side 22 17 false (0)),
(.side 65 1 true (5)),
(.last 36 (4,true)),
(.side 85 1 true (5))])
theorem checked : check 127 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 127 m := sound 127 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 127) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra109

namespace BB6.Agent47Extra110
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,false,3⟩)
  | _,_ => none)
def cert : Tree := (split 25 (5,false) 6 #[
(.side 6 75 false (3)),
(.side 16 13 true (-4)),
(.side 6 30 false (2)),
(.side 16 27 false (1)),
(.side 16 19 false (0)),
(.side 16 24 true (-4)),
(.last 28 (4,true)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,5),(true,3)],[(false,2),(false,4),(false,6)],[(true,2)],[(false,3)],[(true,4),(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,6),(7,2)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,5)],[(true,2)],[(false,3)],[(true,3),(true,13),(true,9)],[(false,4)],[(true,5),(true,19),(true,15)],[(false,6),(false,15)],[(true,6)],[],[(true,7),(true,20),(true,16)],[(false,8),(false,19)],[(true,8)],[(false,9)],[(false,10)],[],[],[(false,13)],[(false,14)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,2),(3,8),(9,10),(11,12),(13,14),(15,6),(16,6),(7,17),(9,18),(19,6),(20,8),(9,8),(21,12),(13,22),(16,12),(13,8),(23,12),(16,17),(20,17),(20,17)]⟩,#[(.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf)))))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf)))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty))))]⟩),
(.side 15 19 false (1)),
(.side 0 30 true (-4)),
(.last 30 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[(true,4)],[(false,5)],[(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[],[(true,4),(true,12)],[(false,9)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch .leaf (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) (.branch .empty (.branch .leaf (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .leaf) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) .empty)]⟩),
(.side 13 13 false (1)),
(.side 26 8 true (-1)),
(.side 13 13 false (1)),
(.side 13 15 false (1)),
(.side 24 2 true (-2)),
(.last 26 (4,true)),
(.side 11 15 false (2)),
(.last 26 (4,true)),
(.side 18 11 false (-1)),
(.side 34 1 true (0)),
(.side 18 11 false (-1)),
(.side 31 1 true (1))])
theorem checked : check 36 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 36 m := sound 36 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 36) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra110

namespace BB6.Agent47Extra111
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,3⟩)
  | _,_ => none)
def cert : Tree := (split 20 (5,false) 6 #[
(.side 0 21 true (-1)),
(.side 0 21 true (-1)),
(.side 14 7 true (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,5),(true,3)],[(false,2),(false,4),(false,6)],[(true,2)],[(false,3)],[(true,4),(true,6)],[(false,5)]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,6),(7,2)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2)],[(true,2)],[(false,3)],[(true,3),(true,9),(true,13)],[(false,4)],[(true,5),(true,15),(true,19)],[(false,6)],[(true,6)],[],[(true,7),(true,16),(true,20)],[(false,8)],[(true,8)],[(false,9)],[(false,10)],[],[],[(false,13)],[(false,14)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,2),(3,8),(9,10),(11,12),(13,14),(15,6),(16,6),(7,17),(9,18),(19,6),(20,8),(9,8),(21,12),(13,22),(16,12),(13,8),(23,12),(16,17),(20,17),(20,17)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf)))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf)))))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty))))]⟩),
(.side 28 19 false (2)),
(.side 13 24 true (1)),
(.side 17 4 true (1)),
(.side 1 20 true (-1)),
(.side 34 19 false (0)),
(.side 0 22 true (-1)),
(.side 17 6 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,6),(false,8)],[(true,2)],[(false,3)],[(true,3)],[],[(true,5)],[(true,6)],[],[(true,8)]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))]⟩),
(.side 28 13 false (0)),
(.side 13 8 true (1)),
(.side 28 13 false (0)),
(.side 32 15 false (0)),
(.side 19 2 true (3)),
(.side 19 2 true (3)),
(.side 11 10 true (1)),
(.side 19 2 true (3)),
(.side 40 11 false (-1)),
(.side 20 1 true (4)),
(.last 27 (4,true)),
(.side 20 1 true (4))])
theorem checked : check 33 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 33 m := sound 33 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 33) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra111

namespace BB6.Agent47Extra112
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,false,3⟩)
  | _,_ => none)
def cert : Tree := (split 25 (5,false) 6 #[
(.side 6 38 false (2)),
(.side 39 13 true (-2)),
(.side 6 30 false (2)),
(.side 16 27 false (1)),
(.side 16 19 false (0)),
(.side 35 24 true (1)),
(.last 28 (4,true)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0)],[(false,2),(false,6)],[(true,2)],[(false,3)],[(true,3)],[],[(true,5)],[(true,6)],[],[(true,8)]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,6)],[(true,2)],[(false,3)],[(true,3)],[],[(true,5)],[(true,6)],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty)),(.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .leaf)) .leaf)) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) .empty)),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch .empty (.branch .empty .leaf)))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),.empty,(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty)),(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))))]⟩),
(.side 15 19 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,4),(false,6)],[(true,2),(true,4),(true,6)],[(false,3),(false,5),(false,7)],[(true,5),(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6),(false,8)],[(true,2)],[(false,3)],[(true,3)],[],[(true,5)],[(true,6)],[],[(true,8)]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)))))),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf))))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf))))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf)))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)))]⟩),
(.last 30 (4,true)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,5),(true,3),(true,4)],[(false,2),(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6),(false,8)],[(true,2)],[(false,3)],[(true,3)],[],[(true,5)],[(true,6)],[],[(true,8)]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch (.branch .leaf (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf))) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .empty))),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))))) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))))) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))))]⟩),
(.side 13 13 false (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,5),(true,3),(true,4)],[(false,2),(false,5),(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,3),(true,1),(true,5)],[(false,2),(false,5)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))))),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))))]⟩),
(.side 13 13 false (1)),
(.side 13 15 false (1)),
(.side 24 2 true (-2)),
(.last 26 (4,true)),
(.side 11 15 false (2)),
(.last 26 (4,true)),
(.side 7 24 false (2)),
(.side 6 32 false (2)),
(.side 7 24 false (2)),
(.last 30 (4,true))])
theorem checked : check 36 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 36 m := sound 36 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 36) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra112

namespace BB6.Agent47Extra113
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,true,3⟩)
  | _,_ => none)
def cert : Tree := (split 29 (5,false) 6 #[
(.side 114 97 false (2)),
(.side 56 13 true (-1)),
(.side 6 38 false (3)),
(.side 42 29 false (2)),
(.side 20 19 false (0)),
(.side 54 24 true (-1)),
(.last 32 (4,true)),
(.last 115 (4,true)),
(.side 19 19 false (1)),
(.side 0 37 true (-4)),
(.last 34 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[(true,4)],[(false,5)],[(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[],[(true,4),(true,12)],[(false,9)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch .leaf (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch .leaf (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .leaf) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) .empty)]⟩),
(.side 17 13 false (1)),
(.side 35 8 true (2)),
(.side 17 13 false (1)),
(.side 15 15 false (3)),
(.side 28 2 true (-2)),
(.last 30 (4,true)),
(.side 15 17 false (3)),
(.last 30 (4,true)),
(.side 20 15 false (0)),
(.side 57 13 true (-1)),
(.side 20 13 false (0)),
(.side 42 29 false (2))])
theorem checked : check 121 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 121 m := sound 121 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 121) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra113

namespace BB6.Agent47Extra114
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,false,4⟩)
  | _,_ => none)
def cert : Tree := (split 14 (5,false) 6 #[
(.side 0 15 true (-1)),
(.side 0 15 true (-1)),
(.side 13 7 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4),(true,10)],[(true,5)],[(true,6)],[(true,3)],[(false,8),(false,11)],[(false,9)],[(true,9)],[(true,8),(true,11)]],#[(0,1),(3,2),(0,0),(4,8),(0,5),(0,6),(0,7),(0,0),(9,12),(10,11),(0,5),(9,12),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,4)],[(true,2)],[(false,3),(true,3),(false,6),(true,6),(false,9),(true,9),(false,13),(true,13),(false,15),(false,16),(true,16),(true,19),(false,20),(false,22),(false,23),(true,23),(true,24),(false,27),(true,27)],[(true,4)],[(false,5)],[(true,5),(true,7)],[(false,7)],[(false,8),(false,10)],[(true,8),(true,10)],[(false,11)],[(true,11)],[(false,12)],[(true,12),(true,18),(true,26)],[(false,14)],[(true,14)],[(true,15),(true,22)],[(false,17),(false,25)],[(true,17),(true,25)],[(false,18),(false,26)],[(false,19)],[(true,20)],[(false,21)],[(true,21)],[(false,24)]],#[(0,1),(2,3),(4,5),(6,6),(4,7),(8,9),(6,6),(10,9),(11,12),(6,6),(11,12),(13,14),(15,16),(6,6),(17,18),(6,19),(6,6),(20,21),(22,16),(23,6),(6,24),(25,26),(6,19),(6,6),(27,6),(20,21),(22,16),(6,6)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .empty))) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)))) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty)) (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)))) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty .leaf)))) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .leaf (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) .empty)) (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf))))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)))) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) .empty))) (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty)))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) .empty))]⟩),
(.side 13 19 false (2)),
(.side 13 24 true (0)),
(.side 13 4 true (1)),
(.side 1 14 true (-1)),
(.side 13 19 false (2)),
(.side 0 16 true (-1)),
(.side 13 6 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[(true,4)],[(false,5)],[(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[],[(true,4),(true,12)],[(false,9)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch .leaf (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch .leaf (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .leaf) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) .empty)]⟩),
(.side 13 13 false (2)),
(.side 13 8 true (1)),
(.side 13 13 false (2)),
(.side 17 15 false (3)),
(.side 13 2 true (1)),
(.side 13 2 true (1)),
(.side 11 4 true (1)),
(.side 13 2 true (1)),
(.side 19 1 false (-1)),
(.side 14 1 true (2)),
(.side 19 1 false (-1)),
(.side 14 1 true (2))])
theorem checked : check 20 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 20 m := sound 20 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 20) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra114

namespace BB6.Agent47Extra115
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,4⟩)
  | _,_ => none)
def cert : Tree := (split 14 (5,false) 6 #[
(.side 0 15 true (-1)),
(.side 0 15 true (-1)),
(.side 13 7 true (2)),
(.last 43 (4,true)),
(.last 48 (4,true)),
(.side 13 24 true (2)),
(.side 13 4 true (3)),
(.side 1 14 true (-1)),
(.side 0 16 true (-1)),
(.side 0 16 true (-1)),
(.side 13 6 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6),(false,8)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))]⟩),
(.side 30 13 false (0)),
(.side 13 8 true (3)),
(.side 7 10 true (-1)),
(.side 36 15 false (0)),
(.side 13 2 true (3)),
(.side 13 2 true (3)),
(.side 11 4 true (1)),
(.side 13 2 true (3)),
(.side 21 1 false (1)),
(.side 14 1 true (4)),
(.last 20 (4,true)),
(.side 14 1 true (4))])
theorem checked : check 54 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 54 m := sound 54 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 54) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra115

namespace BB6.Agent47Extra116
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,true,4⟩)
  | _,_ => none)
def cert : Tree := (split 14 (5,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6),(false,8)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))]⟩),
(.side 0 15 true (-1)),
(.side 6 42 false (4)),
(.last 113 (4,true)),
(.side 1 14 true (-1)),
(.side 97 24 true (2)),
(.side 13 4 true (3)),
(.side 1 14 true (-1)),
(.side 23 19 false (1)),
(.side 0 16 true (-1)),
(.last 38 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6),(false,8)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))]⟩),
(.side 19 13 false (1)),
(.side 13 8 true (3)),
(.side 19 13 false (1)),
(.side 21 15 false (3)),
(.side 13 2 true (3)),
(.side 13 2 true (3)),
(.side 11 4 true (1)),
(.side 13 2 true (3)),
(.side 12 4 true (2)),
(.side 14 1 true (4)),
(.last 17 (4,true)),
(.side 14 1 true (4))])
theorem checked : check 119 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 119 m := sound 119 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 119) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra116

namespace BB6.Agent47Extra117
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,false,5⟩)
  | _,_ => none)
def cert : Tree := (split 13 (5,false) 6 #[
(.side 6 56 false (2)),
(.side 0 14 true (-1)),
(.side 6 30 false (2)),
(.side 22 31 false (2)),
(.side 1 13 false (2)),
(.side 58 24 true (-1)),
(.side 13 4 true (0)),
(.side 1 13 true (-1)),
(.side 18 19 false (0)),
(.side 0 15 true (-1)),
(.last 32 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[],[(false,2)],[(true,2)],[],[],[(false,4),(false,12)],[(true,4),(true,12)],[(false,5),(false,13),(false,9)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch .leaf (.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)) .empty)]⟩),
(.side 16 13 false (0)),
(.side 13 8 true (0)),
(.side 16 13 false (0)),
(.side 20 15 false (0)),
(.side 13 2 true (0)),
(.side 13 2 true (1)),
(.last 17 (4,true)),
(.side 13 2 true (1)),
(.side 16 1 false (-2)),
(.side 13 1 true (1)),
(.side 16 1 false (-2)),
(.side 13 1 true (1))])
theorem checked : check 38 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 38 m := sound 38 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 38) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra117

namespace BB6.Agent47Extra118
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨false,true,5⟩)
  | _,_ => none)
def cert : Tree := (split 13 (5,false) 6 #[
(.side 0 14 true (-1)),
(.side 0 14 true (-1)),
(.side 13 7 true (1)),
(.side 12 30 true (0)),
(.side 24 19 false (0)),
(.side 13 24 true (1)),
(.side 13 4 true (2)),
(.side 1 13 true (-1)),
(.side 0 15 true (-1)),
(.side 0 15 true (-1)),
(.side 13 6 true (1)),
(.last 68 (4,true)),
(.side 6 19 false (3)),
(.side 13 8 true (2)),
(.side 7 9 true (-1)),
(.side 6 25 false (4)),
(.side 13 2 true (2)),
(.side 13 2 true (3)),
(.side 11 3 true (1)),
(.side 13 2 true (3)),
(.side 18 1 false (0)),
(.side 13 1 true (3)),
(.side 22 1 false (4)),
(.side 13 1 true (3))])
theorem checked : check 74 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 74 m := sound 74 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 74) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra118

namespace BB6.Agent47Extra119
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,false,5⟩)
  | _,_ => none)
def cert : Tree := (split 13 (5,false) 6 #[
(.side 0 19 true (-1)),
(.side 58 13 true (-1)),
(.side 6 30 false (2)),
(.side 3 11 true (-1)),
(.side 1 13 false (2)),
(.side 18 24 true (-4)),
(.last 16 (4,true)),
(.side 1 19 true (-1)),
(.side 18 19 false (0)),
(.side 0 18 true (-1)),
(.last 32 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6),(false,8)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))]⟩),
(.side 16 13 false (0)),
(.side 14 8 true (1)),
(.side 16 13 false (0)),
(.side 18 15 false (0)),
(.side 13 2 true (0)),
(.last 14 (4,true)),
(.last 17 (4,true)),
(.last 14 (4,true)),
(.side 16 1 false (-2)),
(.side 12 2 true (1)),
(.side 16 1 false (-2)),
(.side 18 3 false (0))])
theorem checked : check 38 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 38 m := sound 38 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 38) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra119

namespace BB6.Agent47Extra120
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 5,true => some (some ⟨true,true,5⟩)
  | _,_ => none)
def cert : Tree := (split 13 (5,false) 6 #[
(.side 163 107 false (0)),
(.side 0 14 true (-1)),
(.side 6 38 false (3)),
(.side 33 35 false (7)),
(.side 18 19 false (0)),
(.side 80 24 true (4)),
(.last 30 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(false,3)],[(true,4),(true,10),(true,14)],[(true,5)],[(true,6)],[(true,3)],[(false,8),(false,11),(false,15)],[(false,9)],[(true,9)],[(false,6)],[(true,8),(true,11),(true,15)],[(false,12),(false,16)],[(true,12),(true,16)],[(false,7)],[(true,7)]],#[(0,1),(3,2),(0,0),(4,8),(0,5),(0,6),(12,7),(16,17),(9,13),(10,11),(0,5),(9,13),(14,15),(0,0),(0,5),(9,13),(14,15),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,3),(true,3),(false,4),(true,4),(false,7),(true,7),(true,9),(false,10),(false,12),(true,12),(false,15),(true,15),(false,17),(false,21),(true,21),(false,28),(true,28)],[(true,2)],[(false,5)],[(true,5),(true,13),(true,19)],[(false,6),(false,16),(false,22)],[(true,6),(true,16),(true,22)],[(false,8),(false,23)],[(true,8)],[(false,9)],[(true,10)],[(false,11)],[(true,11)],[(false,13)],[(false,14)],[(true,14)],[(true,17)],[(false,18)],[(true,18),(true,24)],[(false,19)],[(false,20),(false,26),(false,27)],[(true,20),(true,26),(true,27)],[(true,23)],[(false,24)],[(false,25)],[(true,25)]],#[(0,1),(2,3),(4,5),(4,4),(4,4),(6,7),(8,9),(4,4),(10,11),(12,4),(4,13),(14,15),(4,4),(16,7),(17,18),(4,4),(8,9),(4,19),(20,21),(22,7),(23,24),(4,4),(8,9),(10,25),(26,21),(27,28),(23,24),(23,24),(4,4)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .leaf)) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty))) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .leaf)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .leaf) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) .leaf)))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty)) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf)))) .leaf)) (.branch (.branch .leaf (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))) (.branch .leaf (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .leaf .leaf))) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf (.branch .empty .leaf)))) .leaf) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .leaf)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))))),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .leaf) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .leaf))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty .leaf)) (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .leaf) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch .leaf (.branch (.branch .leaf (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .leaf .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)))) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))))),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty .leaf))))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty))) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) .empty))]⟩),
(.side 0 18 true (-1)),
(.side 38 23 true (0)),
(.last 15 (4,true)),
(.side 2 12 true (-1)),
(.side 26 13 false (0)),
(.side 37 8 true (2)),
(.last 17 (4,true)),
(.side 4 10 true (-1)),
(.last 14 (4,true)),
(.side 13 2 true (3)),
(.last 14 (4,true)),
(.side 13 2 true (3)),
(.side 12 2 true (2)),
(.side 13 1 true (3)),
(.side 12 3 true (2)),
(.side 13 1 true (3))])
theorem checked : check 36 parent cert = true := by decide +kernel
theorem safe : ∀ m, compatible parent m → WeightedBound 36 m := sound 36 _ cert (by decide) checked
theorem cover : Cover (WeightedBound 36) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra120

namespace BB6.Agent47Extra121
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | _,_ => none)
def p_0 := refine parent (5,false) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.side 7 13 false (1))
theorem checked_0 : check 141 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 141 m := sound 141 _ cert_0 (by decide) checked_0
def p_1 := refine parent (5,false) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 13 17 false (2))
theorem checked_1 : check 141 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 141 m := sound 141 _ cert_1 (by decide) checked_1
def p_2 := refine parent (5,false) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 7 11 false (1))
theorem checked_2 : check 141 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 141 m := sound 141 _ cert_2 (by decide) checked_2
def p_3 := refine parent (5,false) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 13 15 false (2))
theorem checked_3 : check 141 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 141 m := sound 141 _ cert_3 (by decide) checked_3
def p_4 := refine parent (5,false) (some ⟨false,false,1⟩)
def cert_4 : Tree := (.side 7 9 false (1))
theorem checked_4 : check 141 p_4 cert_4 = true := by decide +kernel
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 141 m := sound 141 _ cert_4 (by decide) checked_4
def p_5 := refine parent (5,false) (some ⟨false,true,1⟩)
def cert_5 : Tree := (.side 7 13 false (1))
theorem checked_5 : check 141 p_5 cert_5 = true := by decide +kernel
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 141 m := sound 141 _ cert_5 (by decide) checked_5
def p_6 := refine parent (5,false) (some ⟨true,false,1⟩)
def cert_6 : Tree := (.side 7 9 false (1))
theorem checked_6 : check 141 p_6 cert_6 = true := by decide +kernel
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 141 m := sound 141 _ cert_6 (by decide) checked_6
def p_7 := refine parent (5,false) (some ⟨true,true,1⟩)
def cert_7 : Tree := (.side 7 11 false (1))
theorem checked_7 : check 141 p_7 cert_7 = true := by decide +kernel
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 141 m := sound 141 _ cert_7 (by decide) checked_7
def p_8 := refine parent (5,false) (some ⟨false,false,2⟩)
def cert_8 : Tree := (.side 0 17 false (2))
theorem checked_8 : check 141 p_8 cert_8 = true := by decide +kernel
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 141 m := sound 141 _ cert_8 (by decide) checked_8
def p_9 := refine parent (5,false) (some ⟨false,true,2⟩)
def cert_9 : Tree := (split 14 (4,true) 6 #[
(.side 0 15 true (-1)),
(.side 0 15 true (-1)),
(.side 19 3 true (1)),
(.side 156 3 true (8)),
(.side 24 25 false (0)),
(.side 10 20 true (0)),
(.side 16 3 true (2)),
(.side 1 14 true (-1)),
(.side 6 58 false (2)),
(.side 0 16 true (-1)),
(.side 18 3 true (2)),
(.side 77 3 true (3)),
(.side 38 3 true (-2)),
(.side 20 3 true (2)),
(.side 6 40 false (2)),
(.side 71 17 true (-1)),
(.side 15 3 true (0)),
(.side 15 3 true (2)),
(.side 11 4 true (0)),
(.last 16 (5,true)),
(.side 0 17 true (-1)),
(.side 0 17 true (-1)),
(.side 15 3 true (1)),
(.side 95 3 true (7))])
theorem checked_9 : check 141 p_9 cert_9 = true := by decide +kernel
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 141 m := sound 141 _ cert_9 (by decide) checked_9
def p_10 := refine parent (5,false) (some ⟨true,false,2⟩)
def cert_10 : Tree := (split 14 (4,true) 6 #[
(.side 6 21 false (3)),
(.side 15 15 false (2)),
(.side 7 9 false (1)),
(.side 5 10 true (-1)),
(.side 7 17 false (1)),
(.side 7 11 false (1)),
(.side 16 9 true (0)),
(.side 7 8 true (-1)),
(.side 0 16 false (2)),
(.side 0 18 true (-1)),
(.side 2 18 false (2)),
(.side 10 27 false (3)),
(.side 7 10 false (1)),
(.side 22 7 true (1)),
(.side 7 10 false (1)),
(.side 7 12 false (1)),
(.last 23 (5,true)),
(.side 14 26 true (-1)),
(.last 23 (5,true)),
(.last 18 (5,true)),
(.side 12 12 false (0)),
(.last 15 (5,true)),
(.side 12 12 false (0)),
(.last 15 (5,true))])
theorem checked_10 : check 141 p_10 cert_10 = true := by decide +kernel
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 141 m := sound 141 _ cert_10 (by decide) checked_10
def p_11 := refine parent (5,false) (some ⟨true,true,2⟩)
def cert_11 : Tree := (split 14 (4,true) 6 #[
(.side 6 17 false (3)),
(.side 0 15 true (-1)),
(.side 6 11 false (2)),
(.side 22 15 false (4)),
(.side 6 38 false (2)),
(.side 6 19 false (4)),
(.side 16 3 true (2)),
(.side 1 14 true (-1)),
(.side 2 13 false (2)),
(.side 0 16 true (-1)),
(.side 2 13 false (2)),
(.side 4 17 false (3)),
(.side 4 11 false (2)),
(.side 20 3 true (2)),
(.side 4 11 false (2)),
(.side 4 15 false (3)),
(.last 16 (5,true)),
(.side 15 3 true (2)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.side 6 38 false (2)),
(.side 6 19 false (4)),
(.side 15 3 true (1)),
(.side 2 14 true (-1))])
theorem checked_11 : check 141 p_11 cert_11 = true := by decide +kernel
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 141 m := sound 141 _ cert_11 (by decide) checked_11
def p_12 := refine parent (5,false) (some ⟨false,false,3⟩)
def cert_12 : Tree := (.side 8 5 false (1))
theorem checked_12 : check 141 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 141 m := sound 141 _ cert_12 (by decide) checked_12
def p_13 := refine parent (5,false) (some ⟨false,true,3⟩)
def cert_13 : Tree := (split 16 (4,true) 6 #[
(.side 6 19 false (3)),
(.side 0 17 true (-1)),
(.side 6 13 false (2)),
(.side 24 17 false (4)),
(.side 6 44 false (2)),
(.side 6 21 false (4)),
(.side 17 5 true (1)),
(.side 1 16 true (-1)),
(.side 2 15 false (2)),
(.side 0 18 true (-1)),
(.side 2 15 false (2)),
(.side 4 19 false (3)),
(.side 4 13 false (2)),
(.side 20 5 true (1)),
(.side 4 13 false (2)),
(.side 4 17 false (3)),
(.last 18 (5,true)),
(.side 17 5 true (2)),
(.last 18 (5,true)),
(.last 18 (5,true)),
(.side 6 15 false (2)),
(.side 21 5 true (2)),
(.side 17 5 true (1)),
(.side 36 5 true (2))])
theorem checked_13 : check 141 p_13 cert_13 = true := by decide +kernel
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 141 m := sound 141 _ cert_13 (by decide) checked_13
def p_14 := refine parent (5,false) (some ⟨true,false,3⟩)
def cert_14 : Tree := (split 16 (4,true) 6 #[
(.side 6 72 false (3)),
(.side 17 22 false (2)),
(.side 7 16 false (1)),
(.side 17 24 false (2)),
(.side 1 16 false (2)),
(.side 7 18 false (1)),
(.side 6 78 false (3)),
(.side 7 20 false (1)),
(.side 7 18 false (1)),
(.side 0 20 true (-2)),
(.side 7 18 false (1)),
(.side 4 60 false (3)),
(.side 7 16 false (1)),
(.side 4 66 false (3)),
(.side 7 16 false (1)),
(.side 7 18 false (1)),
(.last 18 (5,true)),
(.side 29 20 false (-1)),
(.last 18 (5,true)),
(.last 20 (5,true)),
(.side 12 5 false (0)),
(.last 17 (5,true)),
(.side 12 5 false (0)),
(.last 17 (5,true))])
theorem checked_14 : check 141 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 141 m := sound 141 _ cert_14 (by decide) checked_14
def p_15 := refine parent (5,false) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 6 7 false (2))
theorem checked_15 : check 141 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 141 m := sound 141 _ cert_15 (by decide) checked_15
def p_16 := refine parent (5,false) (some ⟨false,false,4⟩)
def cert_16 : Tree := (split 13 (4,true) 6 #[
(.side 0 14 false (2)),
(.side 7 8 true (-1)),
(.side 7 8 false (1)),
(.side 7 13 false (1)),
(.side 7 16 false (1)),
(.side 9 29 false (4)),
(.side 9 5 false (1)),
(.side 1 16 true (-1)),
(.side 0 15 false (2)),
(.side 0 20 true (-1)),
(.side 13 9 false (0)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.side 14 2 false (-2)),
(.side 14 2 false (0)),
(.side 14 2 false (-2)),
(.last 15 (5,true)),
(.side 14 2 false (-2)),
(.side 14 2 false (0)),
(.side 14 2 false (-2)),
(.side 12 2 true (-1))])
theorem checked_16 : check 141 p_16 cert_16 = true := by decide +kernel
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 141 m := sound 141 _ cert_16 (by decide) checked_16
def p_17 := refine parent (5,false) (some ⟨false,true,4⟩)
def cert_17 : Tree := (split 13 (4,true) 6 #[
(.side 28 19 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,2),(true,1)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.side 7 13 false (1)),
(.side 3 11 true (-1)),
(.side 1 13 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,2),(true,1)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.side 16 5 true (1)),
(.side 1 20 true (-1)),
(.side 7 15 false (1)),
(.side 0 19 true (-1)),
(.side 7 15 false (1)),
(.side 24 19 false (2)),
(.side 7 13 false (1)),
(.side 14 9 true (1)),
(.side 7 13 false (1)),
(.side 14 17 false (2)),
(.last 15 (5,true)),
(.side 14 3 true (2)),
(.last 15 (5,true)),
(.last 16 (5,true)),
(.side 11 4 true (0)),
(.last 14 (5,true)),
(.side 12 2 true (0)),
(.last 14 (5,true))])
theorem checked_17 : check 141 p_17 cert_17 = true := by decide +kernel
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 141 m := sound 141 _ cert_17 (by decide) checked_17
def p_18 := refine parent (5,false) (some ⟨true,false,4⟩)
def cert_18 : Tree := (split 13 (4,true) 6 #[
(.side 6 46 false (3)),
(.side 7 12 false (1)),
(.side 7 8 false (1)),
(.side 5 9 false (2)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.side 6 78 false (3)),
(.side 7 7 false (1)),
(.side 0 15 false (2)),
(.side 17 2 false (3)),
(.side 2 17 false (2)),
(.side 28 21 false (2)),
(.side 7 9 false (1)),
(.side 18 13 true (1)),
(.side 7 9 false (1)),
(.side 7 11 false (1)),
(.side 14 2 false (-2)),
(.side 17 2 false (3)),
(.side 14 2 false (-2)),
(.last 18 (5,true)),
(.side 14 2 false (-2)),
(.last 14 (5,true)),
(.side 14 2 false (-2)),
(.last 14 (5,true))])
theorem checked_18 : check 141 p_18 cert_18 = true := by decide +kernel
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 141 m := sound 141 _ cert_18 (by decide) checked_18
def p_19 := refine parent (5,false) (some ⟨true,true,4⟩)
def cert_19 : Tree := (split 13 (4,true) 6 #[
(.side 3 11 false (2)),
(.side 4 15 false (3)),
(.side 5 9 false (2)),
(.side 6 13 false (3)),
(.side 7 7 false (1)),
(.side 4 11 false (2)),
(.side 7 7 false (1)),
(.side 6 9 false (2)),
(.side 10 4 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,2),(true,1)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.side 7 17 false (1)),
(.side 24 17 false (2)),
(.side 7 11 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,2),(true,1)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),
(.side 7 11 false (1)),
(.side 14 15 false (2)),
(.side 14 4 false (0)),
(.side 14 3 true (2)),
(.side 14 4 false (0)),
(.last 16 (5,true)),
(.last 14 (5,true)),
(.last 14 (5,true)),
(.last 14 (5,true)),
(.last 14 (5,true))])
theorem checked_19 : check 141 p_19 cert_19 = true := by decide +kernel
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 141 m := sound 141 _ cert_19 (by decide) checked_19
def p_20 := refine parent (5,false) (some ⟨false,false,5⟩)
def cert_20 : Tree := (split 13 (5,true) 6 #[
(.side 0 14 false (2)),
(.side 7 8 true (-1)),
(.side 7 8 false (1)),
(.side 7 13 false (1)),
(.side 7 16 false (1)),
(.last 16 (4,true)),
(.side 9 5 false (1)),
(.last 16 (4,true)),
(.side 0 15 false (2)),
(.last 18 (4,true)),
(.last 22 (4,true)),
(.side 7 15 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 9 false (1)),
(.side 7 13 false (1)),
(.side 15 1 false (-3)),
(.side 15 1 false (-1)),
(.side 15 1 false (-3)),
(.last 16 (4,true)),
(.side 14 1 false (-2)),
(.side 14 1 false (0)),
(.side 14 1 false (-2)),
(.side 12 2 true (-1))])
theorem checked_20 : check 141 p_20 cert_20 = true := by decide +kernel
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 141 m := sound 141 _ cert_20 (by decide) checked_20
def p_21 := refine parent (5,false) (some ⟨false,true,5⟩)
def cert_21 : Tree := (split 13 (5,true) 6 #[
(.side 28 19 false (2)),
(.last 135 (4,true)),
(.side 7 13 false (1)),
(.side 3 11 true (-1)),
(.side 1 13 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[(true,4)],[(false,5)],[(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[],[],[],[(true,4),(true,12)],[(false,9)],[],[(false,10)],[(true,10)],[],[]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,#[(.branch .leaf (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .leaf) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf (.branch .leaf .leaf))) (.branch .empty (.branch .leaf (.branch .leaf .leaf)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) .empty) (.branch (.branch .leaf (.branch .leaf .leaf)) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch .leaf (.branch (.branch .leaf .leaf) .empty)))) .leaf) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)),.empty,(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch (.branch (.branch .empty .leaf) .empty) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty))]⟩),
(.last 16 (4,true)),
(.side 1 20 true (-1)),
(.side 7 15 false (1)),
(.side 0 19 true (-1)),
(.side 7 15 false (1)),
(.side 24 19 false (2)),
(.side 7 13 false (1)),
(.side 14 9 true (1)),
(.side 7 13 false (1)),
(.side 14 17 false (2)),
(.side 15 3 false (-1)),
(.last 14 (4,true)),
(.side 15 3 false (-1)),
(.last 14 (4,true)),
(.side 17 1 true (1)),
(.side 15 1 true (3)),
(.side 12 2 true (0)),
(.side 15 1 true (3))])
theorem checked_21 : check 141 p_21 cert_21 = true := by decide +kernel
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 141 m := sound 141 _ cert_21 (by decide) checked_21
def p_22 := refine parent (5,false) (some ⟨true,false,5⟩)
def cert_22 : Tree := (split 13 (5,true) 6 #[
(.last 17 (4,true)),
(.side 7 12 false (1)),
(.side 7 8 false (1)),
(.side 5 9 false (2)),
(.side 7 16 false (1)),
(.side 7 10 false (1)),
(.last 16 (4,true)),
(.side 7 7 false (1)),
(.side 0 15 false (2)),
(.last 15 (4,true)),
(.last 18 (4,true)),
(.last 15 (4,true)),
(.side 7 9 false (1)),
(.last 17 (4,true)),
(.side 7 9 false (1)),
(.side 7 11 false (1)),
(.side 15 1 false (-3)),
(.last 14 (4,true)),
(.side 15 1 false (-3)),
(.last 14 (4,true)),
(.side 14 1 false (-2)),
(.side 17 1 false (3)),
(.side 14 1 false (-2)),
(.side 15 3 true (1))])
theorem checked_22 : check 141 p_22 cert_22 = true := by decide +kernel
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 141 m := sound 141 _ cert_22 (by decide) checked_22
def p_23 := refine parent (5,false) (some ⟨true,true,5⟩)
def cert_23 : Tree := (split 13 (5,true) 6 #[
(.side 3 11 false (2)),
(.side 4 15 false (3)),
(.side 5 9 false (2)),
(.side 6 13 false (3)),
(.side 7 7 false (1)),
(.side 4 11 false (2)),
(.side 7 7 false (1)),
(.side 6 9 false (2)),
(.side 10 4 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6),(false,8)],[(true,2)],[(false,3)],[(true,3)],[],[(true,5)],[(true,6)],[],[(true,8)]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf))))]⟩),
(.last 15 (4,true)),
(.side 24 17 false (2)),
(.side 7 11 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,3),(true,1),(true,5)],[(false,2),(false,5)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)))]⟩),
(.side 7 11 false (1)),
(.side 14 15 false (2)),
(.last 14 (4,true)),
(.last 14 (4,true)),
(.last 14 (4,true)),
(.last 14 (4,true)),
(.side 25 1 true (-3)),
(.side 15 1 true (3)),
(.side 14 3 false (0)),
(.side 15 1 true (3))])
theorem checked_23 : check 141 p_23 cert_23 = true := by decide +kernel
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 141 m := sound 141 _ cert_23 (by decide) checked_23
theorem safe : ∀ m, compatible parent m → WeightedBound 141 m := by
  apply split_safe 141 parent 12 (5,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23 | omega
theorem cover : Cover (WeightedBound 141) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra121

namespace BB6.Agent47Extra122
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,false,3⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,1⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | _,_ => none)
def p_0 := refine parent (5,true) (some ⟨false,false,0⟩)
def cert_0 : Tree := (split 29 (5,false) 6 #[
(.side 13 17 false (2)),
(.side 14 21 false (2)),
(.side 15 15 false (2)),
(.side 16 19 false (2)),
(.side 17 13 false (1)),
(.side 14 17 false (2)),
(.side 17 13 false (1)),
(.side 16 15 false (2)),
(.side 20 21 false (0)),
(.side 16 25 false (2)),
(.last 31 (4,true)),
(.side 4 48 false (2)),
(.side 4 36 false (2)),
(.side 4 50 false (2)),
(.last 33 (4,true)),
(.side 4 38 false (2)),
(.last 30 (4,true)),
(.last 30 (4,true)),
(.last 30 (4,true)),
(.last 30 (4,true)),
(.side 20 19 false (0)),
(.side 16 23 false (2)),
(.last 34 (4,true)),
(.side 4 42 false (2))])
theorem checked_0 : check 45 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 45 m := sound 45 _ cert_0 (by decide) checked_0
def p_1 := refine parent (5,true) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 0 13 true (-1))
theorem checked_1 : check 45 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 45 m := sound 45 _ cert_1 (by decide) checked_1
def p_2 := refine parent (5,true) (some ⟨true,false,0⟩)
def cert_2 : Tree := (split 27 (5,false) 6 #[
(.side 13 17 false (2)),
(.side 13 21 false (2)),
(.side 13 15 false (2)),
(.side 14 19 false (2)),
(.side 15 13 false (1)),
(.side 13 17 false (2)),
(.side 15 13 false (1)),
(.side 14 15 false (2)),
(.side 18 19 false (0)),
(.side 14 23 false (2)),
(.last 29 (4,true)),
(.side 4 42 false (2)),
(.side 4 32 false (2)),
(.side 4 44 false (2)),
(.last 31 (4,true)),
(.side 4 34 false (2)),
(.last 28 (4,true)),
(.last 28 (4,true)),
(.last 28 (4,true)),
(.last 28 (4,true)),
(.side 18 13 false (0)),
(.side 14 17 false (2)),
(.side 18 13 false (0)),
(.side 4 36 false (2))])
theorem checked_2 : check 45 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 45 m := sound 45 _ cert_2 (by decide) checked_2
def p_3 := refine parent (5,true) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 6 24 true (-1))
theorem checked_3 : check 45 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 45 m := sound 45 _ cert_3 (by decide) checked_3
def p_4 := refine parent (5,true) (some ⟨false,false,1⟩)
def cert_4 : Tree := (split 25 (5,false) 6 #[
(.side 13 17 false (1)),
(.side 13 21 false (1)),
(.side 13 15 false (1)),
(.side 13 19 false (1)),
(.side 13 13 false (1)),
(.side 13 17 false (1)),
(.side 13 13 false (1)),
(.side 13 15 false (1)),
(.side 16 17 false (0)),
(.side 39 21 false (1)),
(.last 27 (4,true)),
(.side 4 69 false (3)),
(.side 4 28 false (2)),
(.side 4 42 false (3)),
(.last 29 (4,true)),
(.side 4 30 false (2)),
(.last 26 (4,true)),
(.last 26 (4,true)),
(.last 26 (4,true)),
(.last 26 (4,true)),
(.side 1 26 false (2)),
(.side 4 36 false (2)),
(.side 1 26 false (2)),
(.side 32 1 true (0))])
theorem checked_4 : check 45 p_4 cert_4 = true := by decide +kernel
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 45 m := sound 45 _ cert_4 (by decide) checked_4
def p_5 := refine parent (5,true) (some ⟨false,true,1⟩)
def cert_5 : Tree := (split 35 (5,false) 6 #[
(.side 20 17 false (2)),
(.side 15 21 false (4)),
(.side 21 15 false (2)),
(.side 22 19 false (2)),
(.side 23 13 false (1)),
(.side 19 17 false (3)),
(.side 23 13 false (1)),
(.side 22 15 false (2)),
(.side 54 27 false (2)),
(.side 54 31 false (4)),
(.last 37 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,2),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,2),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,1)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,2),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.last 39 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,2),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.last 36 (4,true)),
(.last 36 (4,true)),
(.last 36 (4,true)),
(.last 36 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(false,4)],[(true,5)],[(false,3)],[(true,7)],[(false,8)],[(true,9)],[(false,10),(false,21)],[(true,11)],[(false,12)],[(true,13)],[(false,13)],[(true,15)],[(true,12)],[(false,9)],[(true,18),(true,24)],[(false,19)],[(true,20),(true,22)],[(false,16)],[(true,8)],[(false,20),(false,22)],[(true,19)],[(true,16)]],#[(0,1),(3,2),(0,0),(7,4),(5,0),(0,6),(0,0),(0,8),(9,23),(18,10),(11,0),(0,12),(13,17),(15,14),(0,0),(0,16),(22,26),(0,0),(0,19),(20,25),(24,21),(11,0),(24,21),(0,0),(0,19),(0,0),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[(false,3),(true,3),(false,4),(false,6),(true,6),(false,9),(true,9),(false,11),(true,11),(false,12),(true,12),(false,14),(false,17),(true,17),(false,20),(true,20),(false,21),(true,22),(false,24),(true,24),(false,25),(true,25),(true,27),(false,28),(true,28),(false,29),(false,32),(true,32),(false,33),(true,33),(false,36),(true,37),(false,39),(true,39)],[(true,4)],[(false,5)],[(true,5)],[(false,7)],[(true,7)],[(false,8)],[(true,8)],[(false,10)],[(true,10)],[(false,13)],[(true,13)],[(true,14),(true,36)],[(false,15)],[(true,15),(true,30)],[(false,16)],[(true,16)],[(false,18)],[(true,18),(true,34)],[(false,19),(false,35)],[(true,19),(true,35)],[(true,21)],[(false,22)],[(false,23),(false,38)],[(true,23),(true,38)],[(false,26)],[(true,26)],[(false,27)],[(true,29)],[(false,30)],[(false,31)],[(true,31)],[(false,34)],[(false,37)]],#[(0,1),(2,3),(4,5),(6,6),(6,7),(8,9),(6,6),(10,11),(12,13),(6,6),(14,15),(6,6),(6,6),(16,17),(6,18),(19,20),(21,22),(6,6),(23,24),(25,26),(6,6),(6,27),(28,6),(29,30),(6,6),(6,6),(31,32),(33,6),(6,6),(6,34),(35,20),(36,37),(6,6),(6,6),(38,24),(25,26),(6,18),(39,6),(29,30),(6,6)]⟩,#[(.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty (.branch .empty .leaf)))))))) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))))) (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) (.branch .empty (.branch .leaf (.branch .empty (.branch .empty .leaf))))) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)))))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) .empty) (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) (.branch (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty))))))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))) (.branch .leaf (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))) (.branch .leaf (.branch (.branch .empty .leaf) .empty))) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty)))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))) (.branch .empty (.branch .leaf (.branch .empty (.branch .empty .leaf))))) (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf)) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))))))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty)))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty (.branch .empty .leaf))))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .leaf) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .empty)))))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch .empty .leaf) (.branch .leaf (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))))) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty)) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))) .empty)))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty (.branch .empty .leaf))))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty))) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)))))))),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) .empty)) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .empty))))))))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(false,4)],[(true,5),(true,11)],[(false,5),(false,11)],[(true,7)],[(false,8)],[(true,9)],[(false,10)],[(true,4)],[(true,10)]],#[(0,1),(3,2),(0,0),(0,4),(5,12),(7,6),(0,0),(0,8),(9,0),(0,10),(11,13),(7,6),(0,0),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[(false,3),(true,3),(false,4),(true,4),(false,6),(true,6),(false,8),(true,8),(false,9),(true,9),(false,12),(true,12),(false,13),(true,14),(false,16),(true,16),(false,17),(true,17)],[(false,5),(false,15)],[(true,5)],[(false,7)],[(true,7)],[(false,10)],[(true,10)],[(false,11)],[(true,11)],[(true,13)],[(false,14)],[(true,15)]],#[(0,1),(2,3),(4,5),(6,6),(6,6),(7,8),(6,6),(9,10),(6,6),(6,6),(11,12),(13,14),(6,6),(6,15),(16,6),(7,17),(6,6),(6,6)]⟩,#[(.branch (.branch .leaf (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .leaf (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) .empty) .empty)))),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .leaf) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) .empty) .empty)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch .empty (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty .leaf)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf)) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)))),(.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty))) .empty))]⟩),
(.side 26 15 false (0)),
(.side 72 1 true (8))])
theorem checked_5 : check 45 p_5 cert_5 = true := by decide +kernel
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 45 m := sound 45 _ cert_5 (by decide) checked_5
def p_6 := refine parent (5,true) (some ⟨true,false,1⟩)
def cert_6 : Tree := (split 25 (5,false) 6 #[
(.side 13 17 false (1)),
(.side 13 21 false (1)),
(.side 13 15 false (1)),
(.side 13 19 false (1)),
(.side 13 13 false (1)),
(.side 13 17 false (1)),
(.side 13 13 false (1)),
(.side 13 15 false (1)),
(.side 16 17 false (0)),
(.side 13 21 false (2)),
(.last 27 (4,true)),
(.side 4 36 false (2)),
(.side 4 28 false (2)),
(.side 4 38 false (2)),
(.last 29 (4,true)),
(.side 4 30 false (2)),
(.last 26 (4,true)),
(.last 26 (4,true)),
(.last 26 (4,true)),
(.last 26 (4,true)),
(.side 4 28 false (2)),
(.side 4 38 false (2)),
(.last 29 (4,true)),
(.side 4 30 false (2))])
theorem checked_6 : check 45 p_6 cert_6 = true := by decide +kernel
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 45 m := sound 45 _ cert_6 (by decide) checked_6
def p_7 := refine parent (5,true) (some ⟨true,true,1⟩)
def cert_7 : Tree := (split 33 (5,false) 6 #[
(.side 20 17 false (2)),
(.side 20 21 false (2)),
(.side 20 15 false (2)),
(.side 15 19 false (4)),
(.side 21 13 false (1)),
(.side 20 17 false (2)),
(.side 21 13 false (1)),
(.side 19 15 false (3)),
(.side 50 25 false (2)),
(.side 52 29 false (4)),
(.last 35 (4,true)),
(.side 34 39 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,2),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,1)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,2),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.last 37 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,2),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.last 34 (4,true)),
(.last 34 (4,true)),
(.last 34 (4,true)),
(.last 34 (4,true)),
(.side 34 41 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,6),(false,4)],[(true,2),(true,6)],[(false,3),(false,7),(false,5)],[(true,5),(true,7),(true,3)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf))))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf)))) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf))))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf)))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf)))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty (.branch .empty .leaf))))))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,2),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,6)],[(true,2)],[(false,3)],[(true,3)],[],[(true,5)],[(true,6)],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.side 66 1 true (8))])
theorem checked_7 : check 45 p_7 cert_7 = true := by decide +kernel
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 45 m := sound 45 _ cert_7 (by decide) checked_7
def p_8 := refine parent (5,true) (some ⟨false,false,2⟩)
def cert_8 : Tree := (split 15 (5,false) 6 #[
(.side 24 17 false (0)),
(.side 0 16 true (-1)),
(.side 22 15 false (0)),
(.side 43 19 false (3)),
(.side 20 13 false (0)),
(.side 30 17 false (0)),
(.side 20 13 false (0)),
(.side 28 15 false (0)),
(.side 13 3 true (1)),
(.side 40 25 true (0)),
(.last 17 (4,true)),
(.side 2 14 true (-1)),
(.side 13 5 true (1)),
(.side 36 22 true (0)),
(.last 19 (4,true)),
(.side 4 12 true (-1)),
(.last 16 (4,true)),
(.side 14 2 true (2)),
(.last 16 (4,true)),
(.side 14 2 true (2)),
(.side 26 15 false (0)),
(.side 15 1 true (3)),
(.side 26 15 false (0)),
(.side 15 1 true (3))])
theorem checked_8 : check 45 p_8 cert_8 = true := by decide +kernel
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 45 m := sound 45 _ cert_8 (by decide) checked_8
def p_9 := refine parent (5,true) (some ⟨false,true,2⟩)
def cert_9 : Tree := (split 35 (5,false) 6 #[
(.side 22 17 false (2)),
(.side 22 21 false (2)),
(.side 22 15 false (2)),
(.side 17 19 false (4)),
(.side 23 13 false (1)),
(.side 22 17 false (2)),
(.side 23 13 false (1)),
(.side 21 15 false (3)),
(.side 56 27 false (2)),
(.side 56 31 false (4)),
(.last 37 (4,true)),
(.side 36 45 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,2),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,1)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,2),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.last 39 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,2),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.last 36 (4,true)),
(.last 36 (4,true)),
(.last 36 (4,true)),
(.last 36 (4,true)),
(.side 36 49 true (-2)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2),(false,4),(false,6)],[(true,2)],[(false,3)],[(true,4),(true,6)],[(false,5),(false,7)]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,6),(7,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.last 38 (4,true)),
(.side 76 1 true (8))])
theorem checked_9 : check 45 p_9 cert_9 = true := by decide +kernel
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 45 m := sound 45 _ cert_9 (by decide) checked_9
def p_10 := refine parent (5,true) (some ⟨true,false,2⟩)
def cert_10 : Tree := (split 14 (4,true) 6 #[
(.side 0 15 true (-1)),
(.side 0 15 true (-1)),
(.last 21 (5,false)),
(.last 37 (5,false)),
(.last 33 (5,false)),
(.last 29 (5,false)),
(.last 18 (5,false)),
(.side 1 14 true (-1)),
(.last 33 (5,false)),
(.side 0 16 true (-1)),
(.last 20 (5,false)),
(.last 33 (5,false)),
(.last 27 (5,false)),
(.last 22 (5,false)),
(.last 27 (5,false)),
(.last 31 (5,false)),
(.last 16 (5,false)),
(.last 16 (5,false)),
(.side 11 4 true (1)),
(.last 16 (5,false)),
(.last 15 (5,false)),
(.last 15 (5,false)),
(.last 15 (5,false)),
(.last 15 (5,false))])
theorem checked_10 : check 45 p_10 cert_10 = true := by decide +kernel
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 45 m := sound 45 _ cert_10 (by decide) checked_10
def p_11 := refine parent (5,true) (some ⟨true,true,2⟩)
def cert_11 : Tree := (.side 2 11 true (-1))
theorem checked_11 : check 45 p_11 cert_11 = true := by decide +kernel
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 45 m := sound 45 _ cert_11 (by decide) checked_11
def p_12 := refine parent (5,true) (some ⟨false,false,3⟩)
def cert_12 : Tree := (split 17 (5,false) 6 #[
(.side 4 19 false (3)),
(.side 0 18 true (-1)),
(.side 4 17 false (3)),
(.side 49 21 false (4)),
(.side 4 15 false (3)),
(.side 24 19 false (4)),
(.side 4 15 false (3)),
(.side 24 17 false (4)),
(.side 15 3 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,6)],[(true,2),(true,6),(true,4)],[(false,3),(false,5),(false,7)],[(true,3),(true,5),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,6),(false,10)],[],[(false,3)],[(true,3)],[],[],[(false,5)],[(true,5)],[],[],[],[(true,9)],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,8),(9,14),(3,15),(7,16),(17,10),(18,6),(3,19),(7,20),(13,16),(17,14),(21,10),(7,22),(13,20),(21,14),(13,22)]⟩,#[(.branch (.branch (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .leaf) .leaf)) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch .empty (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .leaf (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .leaf) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .leaf (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty))),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .leaf (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty)) .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) .leaf)),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)))))),.empty,(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)))]⟩),
(.last 19 (4,true)),
(.side 2 16 true (-1)),
(.side 13 5 true (0)),
(.side 13 24 true (-2)),
(.last 21 (4,true)),
(.side 4 14 true (-1)),
(.last 18 (4,true)),
(.side 16 2 true (2)),
(.last 18 (4,true)),
(.side 16 2 true (2)),
(.side 4 15 false (3)),
(.side 17 1 true (3)),
(.side 4 15 false (3)),
(.side 17 1 true (3))])
theorem checked_12 : check 45 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 45 m := sound 45 _ cert_12 (by decide) checked_12
def p_13 := refine parent (5,true) (some ⟨false,true,3⟩)
def cert_13 : Tree := (split 29 (5,false) 6 #[
(.side 16 17 false (2)),
(.side 16 21 false (2)),
(.side 16 15 false (2)),
(.side 15 19 false (3)),
(.side 17 13 false (1)),
(.side 16 17 false (2)),
(.side 17 13 false (1)),
(.side 15 15 false (3)),
(.side 20 21 false (1)),
(.side 13 25 false (3)),
(.last 31 (4,true)),
(.side 4 48 false (3)),
(.side 4 36 false (3)),
(.side 4 50 false (3)),
(.last 33 (4,true)),
(.side 4 38 false (3)),
(.last 30 (4,true)),
(.last 30 (4,true)),
(.last 30 (4,true)),
(.last 30 (4,true)),
(.side 4 40 false (3)),
(.side 4 54 false (3)),
(.last 34 (4,true)),
(.side 4 42 false (3))])
theorem checked_13 : check 45 p_13 cert_13 = true := by decide +kernel
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 45 m := sound 45 _ cert_13 (by decide) checked_13
def p_14 := refine parent (5,true) (some ⟨true,false,3⟩)
def cert_14 : Tree := (split 16 (4,true) 6 #[
(.side 6 19 false (3)),
(.side 0 17 true (-1)),
(.side 6 13 false (2)),
(.side 24 17 false (4)),
(.last 33 (5,false)),
(.side 6 21 false (4)),
(.last 20 (5,false)),
(.side 1 16 true (-1)),
(.side 2 15 false (2)),
(.side 0 18 true (-1)),
(.side 2 15 false (2)),
(.side 4 19 false (3)),
(.side 4 13 false (2)),
(.last 24 (5,false)),
(.side 4 13 false (2)),
(.side 4 17 false (3)),
(.last 18 (5,false)),
(.last 18 (5,false)),
(.side 6 13 false (2)),
(.last 18 (5,false)),
(.last 17 (5,false)),
(.last 17 (5,false)),
(.last 17 (5,false)),
(.last 17 (5,false))])
theorem checked_14 : check 45 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 45 m := sound 45 _ cert_14 (by decide) checked_14
def p_15 := refine parent (5,true) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 4 9 true (-1))
theorem checked_15 : check 45 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 45 m := sound 45 _ cert_15 (by decide) checked_15
def p_16 := refine parent (5,true) (some ⟨false,false,4⟩)
def cert_16 : Tree := (split 13 (4,true) 6 #[
(.last 31 (5,false)),
(.side 0 14 true (-1)),
(.last 25 (5,false)),
(.last 35 (5,false)),
(.side 1 13 false (2)),
(.last 33 (5,false)),
(.last 17 (5,false)),
(.side 1 13 true (-1)),
(.last 27 (5,false)),
(.side 0 15 true (-1)),
(.last 27 (5,false)),
(.last 31 (5,false)),
(.last 25 (5,false)),
(.last 21 (5,false)),
(.last 25 (5,false)),
(.last 29 (5,false)),
(.last 15 (5,false)),
(.last 15 (5,false)),
(.side 17 3 false (-1)),
(.last 15 (5,false)),
(.last 14 (5,false)),
(.last 14 (5,false)),
(.last 14 (5,false)),
(.last 14 (5,false))])
theorem checked_16 : check 45 p_16 cert_16 = true := by decide +kernel
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 45 m := sound 45 _ cert_16 (by decide) checked_16
def p_17 := refine parent (5,true) (some ⟨false,true,4⟩)
def cert_17 : Tree := (split 14 (5,false) 6 #[
(.side 20 17 false (2)),
(.side 0 15 true (-1)),
(.side 19 15 false (2)),
(.side 11 19 true (1)),
(.side 19 13 false (1)),
(.side 25 17 false (3)),
(.side 19 13 false (1)),
(.side 26 15 false (2)),
(.side 13 3 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6),(false,8)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))))]⟩),
(.last 16 (4,true)),
(.side 2 13 true (-1)),
(.side 13 5 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,3),(true,1),(true,5)],[(false,2),(false,5)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)))]⟩),
(.last 18 (4,true)),
(.side 4 11 true (-1)),
(.last 15 (4,true)),
(.side 13 2 true (3)),
(.last 15 (4,true)),
(.side 13 2 true (3)),
(.side 12 3 true (2)),
(.side 14 1 true (4)),
(.last 16 (4,true)),
(.side 14 1 true (4))])
theorem checked_17 : check 45 p_17 cert_17 = true := by decide +kernel
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 45 m := sound 45 _ cert_17 (by decide) checked_17
def p_18 := refine parent (5,true) (some ⟨true,false,4⟩)
def cert_18 : Tree := (split 13 (4,true) 6 #[
(.last 18 (5,false)),
(.last 31 (5,false)),
(.last 25 (5,false)),
(.side 3 11 true (-1)),
(.side 1 13 false (2)),
(.last 27 (5,false)),
(.last 20 (5,false)),
(.last 19 (5,false)),
(.last 27 (5,false)),
(.last 16 (5,false)),
(.last 27 (5,false)),
(.last 16 (5,false)),
(.last 25 (5,false)),
(.last 18 (5,false)),
(.last 25 (5,false)),
(.last 27 (5,false)),
(.last 15 (5,false)),
(.last 16 (5,false)),
(.side 17 3 false (-1)),
(.last 16 (5,false)),
(.last 14 (5,false)),
(.side 11 4 true (1)),
(.last 14 (5,false)),
(.side 12 2 true (1))])
theorem checked_18 : check 45 p_18 cert_18 = true := by decide +kernel
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 45 m := sound 45 _ cert_18 (by decide) checked_18
def p_19 := refine parent (5,true) (some ⟨true,true,4⟩)
def cert_19 : Tree := (split 14 (5,false) 6 #[
(.side 20 17 false (2)),
(.side 0 15 true (-1)),
(.side 18 15 false (2)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3),(true,4)],[(false,2),(false,4)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch .empty (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)),.empty,(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty)]⟩),
(.side 17 13 false (1)),
(.side 26 17 false (2)),
(.side 17 13 false (1)),
(.side 23 15 false (3)),
(.side 13 3 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6),(false,8)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),.empty,(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))))]⟩),
(.last 16 (4,true)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3),(true,4)],[(false,2),(false,4)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[.leaf,(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch .empty (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)),.empty,(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty)]⟩),
(.side 6 9 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,3),(true,1),(true,5)],[(false,2),(false,5)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf)))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)))]⟩),
(.last 22 (4,true)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3),(true,4)],[(false,2),(false,4)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[.leaf,(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch .empty (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)),.empty,(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty)]⟩),
(.last 15 (4,true)),
(.side 13 2 true (3)),
(.last 15 (4,true)),
(.side 13 2 true (3)),
(.side 12 3 true (2)),
(.side 14 1 true (4)),
(.last 16 (4,true)),
(.side 14 1 true (4))])
theorem checked_19 : check 45 p_19 cert_19 = true := by decide +kernel
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 45 m := sound 45 _ cert_19 (by decide) checked_19
def p_20 := refine parent (5,true) (some ⟨false,false,5⟩)
def cert_20 : Tree := (split 14 (5,false) 6 #[
(.side 16 17 false (0)),
(.side 0 15 true (-1)),
(.side 15 15 false (0)),
(.side 6 17 false (3)),
(.side 15 13 false (-1)),
(.side 18 17 false (2)),
(.side 15 13 false (-1)),
(.side 22 15 false (0)),
(.side 14 3 true (-1)),
(.side 6 76 false (2)),
(.last 16 (4,true)),
(.side 2 13 false (2)),
(.side 14 5 true (-2)),
(.side 6 46 false (3)),
(.last 18 (4,true)),
(.side 4 11 false (2)),
(.last 15 (4,true)),
(.side 14 2 true (0)),
(.last 15 (4,true)),
(.side 14 2 true (0)),
(.side 16 1 false (-2)),
(.side 14 1 true (0)),
(.side 16 1 false (-2)),
(.side 14 1 true (0))])
theorem checked_20 : check 45 p_20 cert_20 = true := by decide +kernel
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 45 m := sound 45 _ cert_20 (by decide) checked_20
def p_21 := refine parent (5,true) (some ⟨false,true,5⟩)
def cert_21 : Tree := (split 13 (5,false) 6 #[
(.side 22 17 false (2)),
(.side 0 14 true (-1)),
(.side 16 15 false (2)),
(.side 26 19 false (2)),
(.side 1 13 true (-1)),
(.side 24 17 false (2)),
(.last 31 (4,true)),
(.side 1 13 true (-1)),
(.side 22 23 false (1)),
(.side 0 15 true (-1)),
(.last 33 (4,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,2),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,6)],[],[(false,3)],[(true,3)],[],[(true,5)],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .leaf)) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))]⟩),
(.side 4 36 false (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,3),(true,1),(true,5)],[(false,2),(false,5)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf)))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)))]⟩),
(.last 33 (4,true)),
(.side 16 42 false (4)),
(.last 16 (4,true)),
(.side 13 2 true (3)),
(.side 11 3 true (1)),
(.side 13 2 true (3)),
(.side 20 1 false (0)),
(.side 13 1 true (3)),
(.side 29 1 false (5)),
(.side 13 1 true (3))])
theorem checked_21 : check 45 p_21 cert_21 = true := by decide +kernel
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 45 m := sound 45 _ cert_21 (by decide) checked_21
def p_22 := refine parent (5,true) (some ⟨true,false,5⟩)
def cert_22 : Tree := (split 14 (5,false) 6 #[
(.side 16 17 false (0)),
(.side 15 21 false (2)),
(.side 15 15 false (0)),
(.side 18 19 false (1)),
(.side 15 13 false (-1)),
(.side 15 17 false (1)),
(.side 15 13 false (-1)),
(.side 16 15 false (0)),
(.side 0 21 false (2)),
(.last 16 (4,true)),
(.last 16 (4,true)),
(.last 16 (4,true)),
(.side 8 7 false (2)),
(.last 18 (4,true)),
(.last 18 (4,true)),
(.side 6 9 false (2)),
(.last 15 (4,true)),
(.last 15 (4,true)),
(.last 15 (4,true)),
(.last 15 (4,true)),
(.side 16 1 false (-2)),
(.side 13 2 true (0)),
(.side 16 1 false (-2)),
(.side 16 3 false (0))])
theorem checked_22 : check 45 p_22 cert_22 = true := by decide +kernel
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 45 m := sound 45 _ cert_22 (by decide) checked_22
def p_23 := refine parent (5,true) (some ⟨true,true,5⟩)
def cert_23 : Tree := (split 13 (5,false) 6 #[
(.side 3 11 true (-1)),
(.side 0 14 true (-1)),
(.side 5 9 true (-1)),
(.side 22 19 false (4)),
(.side 4 17 false (3)),
(.side 4 28 true (-1)),
(.side 7 7 true (-1)),
(.side 6 24 true (-1)),
(.side 13 3 true (2)),
(.side 9 49 true (-1)),
(.last 15 (4,true)),
(.side 33 39 true (-1)),
(.side 4 32 false (3)),
(.side 6 11 true (-1)),
(.last 31 (4,true)),
(.side 16 38 false (4)),
(.last 14 (4,true)),
(.side 13 2 true (3)),
(.last 14 (4,true)),
(.side 13 2 true (3)),
(.side 12 2 true (2)),
(.side 13 1 true (3)),
(.side 12 3 true (2)),
(.side 13 1 true (3))])
theorem checked_23 : check 45 p_23 cert_23 = true := by decide +kernel
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 45 m := sound 45 _ cert_23 (by decide) checked_23
theorem safe : ∀ m, compatible parent m → WeightedBound 45 m := by
  apply split_safe 45 parent 12 (5,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23 | omega
theorem cover : Cover (WeightedBound 45) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra122

namespace BB6.Agent47Extra141
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
def p_0 := refine parent (4,false) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_0 : check 70 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 70 m := sound 70 _ cert_0 (by decide) checked_0
def p_1 := refine parent (4,false) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 0 32 true (-2))
theorem checked_1 : check 70 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 70 m := sound 70 _ cert_1 (by decide) checked_1
def p_2 := refine parent (4,false) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 56 3 true (2))
theorem checked_2 : check 70 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 70 m := sound 70 _ cert_2 (by decide) checked_2
def p_3 := refine parent (4,false) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 20 18 false (3))
theorem checked_3 : check 70 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 70 m := sound 70 _ cert_3 (by decide) checked_3
def p_4 := refine parent (4,false) (some ⟨false,false,1⟩)
def cert_4 : Tree := (.side 6 18 false (2))
theorem checked_4 : check 70 p_4 cert_4 = true := by decide +kernel
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 70 m := sound 70 _ cert_4 (by decide) checked_4
def p_5 := refine parent (4,false) (some ⟨false,true,1⟩)
def cert_5 : Tree := (.side 18 16 true (2))
theorem checked_5 : check 70 p_5 cert_5 = true := by decide +kernel
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 70 m := sound 70 _ cert_5 (by decide) checked_5
def p_6 := refine parent (4,false) (some ⟨true,false,1⟩)
def cert_6 : Tree := (.side 14 4 true (0))
theorem checked_6 : check 70 p_6 cert_6 = true := by decide +kernel
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 70 m := sound 70 _ cert_6 (by decide) checked_6
def p_7 := refine parent (4,false) (some ⟨true,true,1⟩)
def cert_7 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,.empty]⟩)
theorem checked_7 : check 70 p_7 cert_7 = true := by decide +kernel
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 70 m := sound 70 _ cert_7 (by decide) checked_7
def p_8 := refine parent (4,false) (some ⟨false,false,2⟩)
def cert_8 : Tree := (.side 2 16 false (2))
theorem checked_8 : check 70 p_8 cert_8 = true := by decide +kernel
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 70 m := sound 70 _ cert_8 (by decide) checked_8
def p_9 := refine parent (4,false) (some ⟨false,true,2⟩)
def cert_9 : Tree := (.side 4 22 false (2))
theorem checked_9 : check 70 p_9 cert_9 = true := by decide +kernel
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 70 m := sound 70 _ cert_9 (by decide) checked_9
def p_10 := refine parent (4,false) (some ⟨true,false,2⟩)
def cert_10 : Tree := (.side 2 16 false (2))
theorem checked_10 : check 70 p_10 cert_10 = true := by decide +kernel
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 70 m := sound 70 _ cert_10 (by decide) checked_10
def p_11 := refine parent (4,false) (some ⟨true,true,2⟩)
def cert_11 : Tree := (.side 61 44 true (0))
theorem checked_11 : check 70 p_11 cert_11 = true := by decide +kernel
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 70 m := sound 70 _ cert_11 (by decide) checked_11
def p_12 := refine parent (4,false) (some ⟨false,false,3⟩)
def cert_12 : Tree := (.side 4 14 false (2))
theorem checked_12 : check 70 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 70 m := sound 70 _ cert_12 (by decide) checked_12
def p_13 := refine parent (4,false) (some ⟨false,true,3⟩)
def cert_13 : Tree := (.side 62 4 true (2))
theorem checked_13 : check 70 p_13 cert_13 = true := by decide +kernel
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 70 m := sound 70 _ cert_13 (by decide) checked_13
def p_14 := refine parent (4,false) (some ⟨true,false,3⟩)
def cert_14 : Tree := (.side 4 14 false (2))
theorem checked_14 : check 70 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 70 m := sound 70 _ cert_14 (by decide) checked_14
def p_15 := refine parent (4,false) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 4 16 false (2))
theorem checked_15 : check 70 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 70 m := sound 70 _ cert_15 (by decide) checked_15
def p_16 := refine parent (4,false) (some ⟨false,false,4⟩)
def cert_16 : Tree := (.side 7 16 false (1))
theorem checked_16 : check 70 p_16 cert_16 = true := by decide +kernel
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 70 m := sound 70 _ cert_16 (by decide) checked_16
def p_17 := refine parent (4,false) (some ⟨false,true,4⟩)
def cert_17 : Tree := (.side 53 1 true (3))
theorem checked_17 : check 70 p_17 cert_17 = true := by decide +kernel
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 70 m := sound 70 _ cert_17 (by decide) checked_17
def p_18 := refine parent (4,false) (some ⟨true,false,4⟩)
def cert_18 : Tree := (.side 7 16 false (1))
theorem checked_18 : check 70 p_18 cert_18 = true := by decide +kernel
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 70 m := sound 70 _ cert_18 (by decide) checked_18
def p_19 := refine parent (4,false) (some ⟨true,true,4⟩)
def cert_19 : Tree := (.side 4 20 false (2))
theorem checked_19 : check 70 p_19 cert_19 = true := by decide +kernel
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 70 m := sound 70 _ cert_19 (by decide) checked_19
def p_20 := refine parent (4,false) (some ⟨false,false,5⟩)
def cert_20 : Tree := (split 18 (5,false) 6 #[
(.side 3 16 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 5 14 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 23 false (1)),
(.side 70 54 true (0)),
(.side 6 22 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 24 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 29 false (1)),
(.side 6 18 false (2)),
(.side 7 12 false (1)),
(.side 62 5 true (2)),
(.side 7 12 false (1)),
(.side 6 16 false (2)),
(.side 7 16 false (1)),
(.side 17 2 true (0)),
(.side 7 16 false (1)),
(.last 20 (5,true)),
(.last 19 (5,true)),
(.last 20 (5,true)),
(.last 19 (5,true)),
(.last 20 (5,true))])
theorem checked_20 : check 70 p_20 cert_20 = true := by decide +kernel
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 70 m := sound 70 _ cert_20 (by decide) checked_20
def p_21 := refine parent (4,false) (some ⟨false,true,5⟩)
def cert_21 : Tree := (split 18 (5,true) 6 #[
(.last 54 (5,false)),
(.side 0 19 true (-2)),
(.last 22 (5,false)),
(.side 3 36 true (-2)),
(.side 4 22 false (2)),
(.last 35 (5,false)),
(.last 23 (5,false)),
(.side 1 18 true (-2)),
(.side 6 22 false (2)),
(.side 0 20 true (-2)),
(.last 25 (5,false)),
(.last 34 (5,false)),
(.last 23 (5,false)),
(.last 23 (5,false)),
(.last 64 (5,false)),
(.last 32 (5,false)),
(.last 20 (5,false)),
(.last 20 (5,false)),
(.side 17 2 true (1)),
(.last 20 (5,false)),
(.last 19 (5,false)),
(.last 19 (5,false)),
(.last 19 (5,false)),
(.last 19 (5,false))])
theorem checked_21 : check 70 p_21 cert_21 = true := by decide +kernel
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 70 m := sound 70 _ cert_21 (by decide) checked_21
def p_22 := refine parent (4,false) (some ⟨true,false,5⟩)
def cert_22 : Tree := (split 18 (5,false) 6 #[
(.side 3 16 false (2)),
(.side 4 18 false (2)),
(.side 5 14 false (2)),
(.side 6 16 false (2)),
(.side 7 23 false (1)),
(.side 58 3 true (2)),
(.side 11 8 true (-1)),
(.side 56 3 true (2)),
(.side 0 24 false (2)),
(.side 6 20 false (2)),
(.side 7 29 false (1)),
(.side 15 4 true (0)),
(.side 7 12 false (1)),
(.side 4 16 false (2)),
(.side 7 12 false (1)),
(.side 6 14 false (2)),
(.side 7 16 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .leaf),.empty]⟩),
(.side 7 16 false (1)),
(.side 6 18 false (2)),
(.last 19 (5,true)),
(.last 19 (5,true)),
(.last 19 (5,true)),
(.last 19 (5,true))])
theorem checked_22 : check 70 p_22 cert_22 = true := by decide +kernel
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 70 m := sound 70 _ cert_22 (by decide) checked_22
def p_23 := refine parent (4,false) (some ⟨true,true,5⟩)
def cert_23 : Tree := (split 18 (5,true) 6 #[
(.side 4 20 false (2)),
(.side 26 22 false (4)),
(.side 4 18 false (2)),
(.side 26 20 false (4)),
(.last 21 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(false,9)],[(false,1)],[(true,1)],[(false,2),(false,4),(true,4),(false,5),(true,5),(false,7),(false,8),(true,8),(false,10),(true,10),(false,11),(true,11)],[(true,2)],[(false,3)],[(true,3)],[(false,6)],[(true,6)],[(true,7)],[(true,9)]],#[(0,1),(2,3),(4,5),(6,7),(4,4),(4,4),(8,9),(4,10),(4,4),(1,11),(4,4),(4,4)]⟩,⟨#[[(false,0)],[(true,0)],[(true,1),(true,7)],[(true,2)],[(true,3)],[(false,2)],[(false,1)],[(true,4)],[(false,7)]],#[(0,1),(6,2),(5,3),(0,4),(0,7),(0,0),(0,0),(8,2),(0,0)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) .empty) .empty)),(.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))),(.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) .empty),(.branch .empty (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)))),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty),.empty,(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty))]⟩),
(.last 60 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[(false,3)],[(true,3)],[],[],[],[],[],[(true,6)],[],[],[],[],[],[],[],[],[(false,27)],[(true,27)],[],[],[],[(true,13),(true,29)],[],[(true,30)],[(false,23)],[(true,23)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,14)],[(false,2)],[(true,2)],[],[],[(false,4)],[(true,4)],[],[],[],[],[],[(true,8)],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,14),(15,16),(3,17),(7,18),(19,10),(20,6),(21,2),(3,22),(3,23),(7,24),(13,25),(26,16),(27,10),(28,6),(3,29),(7,30),(13,31),(21,6),(7,22),(32,16),(33,10),(7,34),(13,35),(21,10),(13,22),(36,16),(13,37),(21,16),(21,22),(21,22)]⟩,#[(.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty)))) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty))) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty)) .empty)) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)))) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .leaf (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))))) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty (.branch .leaf (.branch .empty .leaf))))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty)) .empty)) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) .empty)) .empty) .empty) .empty),.empty,(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty (.branch .empty (.branch .empty .leaf))))))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty)))) .empty)]⟩),
(.side 6 20 false (2)),
(.side 27 24 false (3)),
(.side 6 20 false (2)),
(.last 48 (5,false)),
(.side 4 16 false (2)),
(.last 23 (5,false)),
(.side 4 16 false (2)),
(.side 21 18 false (3)),
(.side 6 22 false (2)),
(.last 20 (5,false)),
(.last 25 (5,false)),
(.last 20 (5,false)),
(.last 20 (5,false)),
(.last 19 (5,false)),
(.last 20 (5,false)),
(.last 19 (5,false))])
theorem checked_23 : check 70 p_23 cert_23 = true := by decide +kernel
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 70 m := sound 70 _ cert_23 (by decide) checked_23
theorem safe : ∀ m, compatible parent m → WeightedBound 70 m := by
  apply split_safe 70 parent 17 (4,false) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23 | omega
theorem cover : Cover (WeightedBound 70) parent := .leaf _ safe
#print axioms cover
end BB6.Agent47Extra141
