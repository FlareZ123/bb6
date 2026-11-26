import PhaseTree
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent47Root48
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def parent : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,5⟩)
  | _,_ => none)
def p_0 := refine parent (5,false) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.side 7 10 false (1))
theorem checked_0 : check 151 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 151 m := sound 151 _ cert_0 (by decide) checked_0
def p_1 := refine parent (5,false) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,4)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),.empty]⟩)
theorem checked_1 : check 151 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 151 m := sound 151 _ cert_1 (by decide) checked_1
def p_2 := refine parent (5,false) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 7 8 false (1))
theorem checked_2 : check 151 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 151 m := sound 151 _ cert_2 (by decide) checked_2
def p_3 := refine parent (5,false) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,4)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),.empty]⟩)
theorem checked_3 : check 151 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 151 m := sound 151 _ cert_3 (by decide) checked_3
def p_4 := refine parent (5,false) (some ⟨false,false,1⟩)
def p_4_0 := refine p_4 (4,false) (some ⟨false,false,0⟩)
def cert_4_0 : Tree := (.side 0 16 false (2))
theorem checked_4_0 : check 151 p_4_0 cert_4_0 = true := by decide +kernel
theorem safe_4_0 : ∀ m, compatible p_4_0 m → WeightedBound 151 m := sound 151 _ cert_4_0 (by decide) checked_4_0
def p_4_1 := refine p_4 (4,false) (some ⟨false,true,0⟩)
def cert_4_1 : Tree := (.side 0 22 true (-2))
theorem checked_4_1 : check 151 p_4_1 cert_4_1 = true := by decide +kernel
theorem safe_4_1 : ∀ m, compatible p_4_1 m → WeightedBound 151 m := sound 151 _ cert_4_1 (by decide) checked_4_1
def p_4_2 := refine p_4 (4,false) (some ⟨true,false,0⟩)
def cert_4_2 : Tree := (.side 32 3 true (0))
theorem checked_4_2 : check 151 p_4_2 cert_4_2 = true := by decide +kernel
theorem safe_4_2 : ∀ m, compatible p_4_2 m → WeightedBound 151 m := sound 151 _ cert_4_2 (by decide) checked_4_2
def p_4_3 := refine p_4 (4,false) (some ⟨true,true,0⟩)
def cert_4_3 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6),(false,4)],[(true,2),(true,6),(true,4)],[(false,3),(false,7),(false,5)],[(true,3),(true,5),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,4),(true,1)],[(false,4),(false,2)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))) (.branch .empty (.branch .empty (.branch .leaf (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .empty)))) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf))))),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)))) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf))))),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .empty)))) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf))))),.empty]⟩)
theorem checked_4_3 : check 151 p_4_3 cert_4_3 = true := by decide +kernel
theorem safe_4_3 : ∀ m, compatible p_4_3 m → WeightedBound 151 m := sound 151 _ cert_4_3 (by decide) checked_4_3
def p_4_4 := refine p_4 (4,false) (some ⟨false,false,1⟩)
def cert_4_4 : Tree := (.side 7 14 false (1))
theorem checked_4_4 : check 151 p_4_4 cert_4_4 = true := by decide +kernel
theorem safe_4_4 : ∀ m, compatible p_4_4 m → WeightedBound 151 m := sound 151 _ cert_4_4 (by decide) checked_4_4
def p_4_5 := refine p_4 (4,false) (some ⟨false,true,1⟩)
def cert_4_5 : Tree := (split 17 (2,true) 6 #[
(.side 7 14 true (-2)),
(.side 20 16 true (-2)),
(.side 7 12 true (-2)),
(.side 20 14 true (-2)),
(.side 20 18 true (2)),
(.side 1 58 true (-2)),
(.side 7 19 false (1)),
(.side 18 39 true (2)),
(.side 0 20 false (2)),
(.side 0 46 true (-2)),
(.side 17 6 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 24 true (-2)),
(.side 7 14 true (-2)),
(.side 8 10 true (-2)),
(.side 6 12 true (-2)),
(.side 7 18 false (1)),
(.side 21 17 true (0)),
(.side 7 18 false (1)),
(.last 19 (5,true)),
(.last 18 (5,true)),
(.last 18 (5,true)),
(.last 18 (5,true)),
(.last 18 (5,true))])
theorem checked_4_5 : check 151 p_4_5 cert_4_5 = true := by decide +kernel
theorem safe_4_5 : ∀ m, compatible p_4_5 m → WeightedBound 151 m := sound 151 _ cert_4_5 (by decide) checked_4_5
def p_4_6 := refine p_4 (4,false) (some ⟨true,false,1⟩)
def cert_4_6 : Tree := (split 17 (2,true) 6 #[
(.side 7 14 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 14 4 true (-2)),
(.side 37 26 false (1)),
(.side 7 19 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 20 false (2)),
(.side 0 58 true (-4)),
(.side 17 6 false (-1)),
(.side 2 16 false (2)),
(.side 8 10 false (0)),
(.side 32 6 true (0)),
(.side 8 10 false (0)),
(.side 4 14 false (2)),
(.side 7 18 false (1)),
(.side 33 3 true (0)),
(.side 7 18 false (1)),
(.side 11 8 true (-2)),
(.last 18 (5,true)),
(.side 1 18 false (2)),
(.last 18 (5,true)),
(.last 23 (5,true))])
theorem checked_4_6 : check 151 p_4_6 cert_4_6 = true := by decide +kernel
theorem safe_4_6 : ∀ m, compatible p_4_6 m → WeightedBound 151 m := sound 151 _ cert_4_6 (by decide) checked_4_6
def p_4_7 := refine p_4 (4,false) (some ⟨true,true,1⟩)
def cert_4_7 : Tree := (split 17 (2,true) 6 #[
(.side 3 15 false (2)),
(.side 20 17 false (3)),
(.side 5 13 false (2)),
(.side 20 15 false (3)),
(.side 11 113 true (-3)),
(.side 1 19 true (-2)),
(.side 1 29 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 21 false (2)),
(.side 0 48 true (-3)),
(.side 16 6 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 11 false (1)),
(.side 4 15 false (2)),
(.side 7 11 false (1)),
(.side 6 13 false (2)),
(.last 19 (5,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 19 (5,true)),
(.last 19 (5,true)),
(.last 18 (5,true)),
(.last 18 (5,true)),
(.last 18 (5,true)),
(.last 18 (5,true))])
theorem checked_4_7 : check 151 p_4_7 cert_4_7 = true := by decide +kernel
theorem safe_4_7 : ∀ m, compatible p_4_7 m → WeightedBound 151 m := sound 151 _ cert_4_7 (by decide) checked_4_7
def p_4_8 := refine p_4 (4,false) (some ⟨false,false,2⟩)
def cert_4_8 : Tree := (.side 0 17 false (2))
theorem checked_4_8 : check 151 p_4_8 cert_4_8 = true := by decide +kernel
theorem safe_4_8 : ∀ m, compatible p_4_8 m → WeightedBound 151 m := sound 151 _ cert_4_8 (by decide) checked_4_8
def p_4_9 := refine p_4 (4,false) (some ⟨false,true,2⟩)
def cert_4_9 : Tree := (split 19 (2,true) 6 #[
(.side 3 17 false (2)),
(.side 22 19 false (3)),
(.side 5 15 false (2)),
(.side 22 17 false (3)),
(.side 7 25 false (2)),
(.side 0 23 true (-2)),
(.side 0 35 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 23 false (2)),
(.side 0 52 true (-3)),
(.side 16 6 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 13 false (1)),
(.side 4 17 false (2)),
(.side 7 13 false (1)),
(.side 6 15 false (2)),
(.last 21 (5,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 21 (5,true)),
(.last 21 (5,true)),
(.last 20 (5,true)),
(.last 20 (5,true)),
(.last 20 (5,true)),
(.last 20 (5,true))])
theorem checked_4_9 : check 151 p_4_9 cert_4_9 = true := by decide +kernel
theorem safe_4_9 : ∀ m, compatible p_4_9 m → WeightedBound 151 m := sound 151 _ cert_4_9 (by decide) checked_4_9
def p_4_10 := refine p_4 (4,false) (some ⟨true,false,2⟩)
def cert_4_10 : Tree := (split 19 (2,true) 6 #[
(.side 3 17 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 5 15 false (2)),
(.side 6 25 false (2)),
(.side 7 19 false (1)),
(.side 38 29 false (2)),
(.side 11 9 false (0)),
(.side 29 27 false (1)),
(.side 0 23 false (2)),
(.side 0 64 true (-6)),
(.side 16 6 false (-1)),
(.side 6 19 false (2)),
(.side 7 13 false (1)),
(.side 2 25 false (2)),
(.side 7 13 false (1)),
(.side 6 17 false (2)),
(.last 21 (5,true)),
(.side 2 19 false (2)),
(.last 21 (5,true)),
(.last 23 (5,true)),
(.last 20 (5,true)),
(.side 6 21 false (2)),
(.last 20 (5,true)),
(.side 2 21 false (2))])
theorem checked_4_10 : check 151 p_4_10 cert_4_10 = true := by decide +kernel
theorem safe_4_10 : ∀ m, compatible p_4_10 m → WeightedBound 151 m := sound 151 _ cert_4_10 (by decide) checked_4_10
def p_4_11 := refine p_4 (4,false) (some ⟨true,true,2⟩)
def cert_4_11 : Tree := (.side 7 13 false (1))
theorem checked_4_11 : check 151 p_4_11 cert_4_11 = true := by decide +kernel
theorem safe_4_11 : ∀ m, compatible p_4_11 m → WeightedBound 151 m := sound 151 _ cert_4_11 (by decide) checked_4_11
def p_4_12 := refine p_4 (4,false) (some ⟨false,false,3⟩)
def cert_4_12 : Tree := (.side 7 15 false (1))
theorem checked_4_12 : check 151 p_4_12 cert_4_12 = true := by decide +kernel
theorem safe_4_12 : ∀ m, compatible p_4_12 m → WeightedBound 151 m := sound 151 _ cert_4_12 (by decide) checked_4_12
def p_4_13 := refine p_4 (4,false) (some ⟨false,true,3⟩)
def cert_4_13 : Tree := (.side 28 4 true (0))
theorem checked_4_13 : check 151 p_4_13 cert_4_13 = true := by decide +kernel
theorem safe_4_13 : ∀ m, compatible p_4_13 m → WeightedBound 151 m := sound 151 _ cert_4_13 (by decide) checked_4_13
def p_4_14 := refine p_4 (4,false) (some ⟨true,false,3⟩)
def cert_4_14 : Tree := (.side 9 7 false (0))
theorem checked_4_14 : check 151 p_4_14 cert_4_14 = true := by decide +kernel
theorem safe_4_14 : ∀ m, compatible p_4_14 m → WeightedBound 151 m := sound 151 _ cert_4_14 (by decide) checked_4_14
def p_4_15 := refine p_4 (4,false) (some ⟨true,true,3⟩)
def cert_4_15 : Tree := (.side 7 11 false (1))
theorem checked_4_15 : check 151 p_4_15 cert_4_15 = true := by decide +kernel
theorem safe_4_15 : ∀ m, compatible p_4_15 m → WeightedBound 151 m := sound 151 _ cert_4_15 (by decide) checked_4_15
def p_4_16 := refine p_4 (4,false) (some ⟨false,false,4⟩)
def cert_4_16 : Tree := (.side 15 1 false (-1))
theorem checked_4_16 : check 151 p_4_16 cert_4_16 = true := by decide +kernel
theorem safe_4_16 : ∀ m, compatible p_4_16 m → WeightedBound 151 m := sound 151 _ cert_4_16 (by decide) checked_4_16
def p_4_17 := refine p_4 (4,false) (some ⟨false,true,4⟩)
def cert_4_17 : Tree := (.side 7 17 false (1))
theorem checked_4_17 : check 151 p_4_17 cert_4_17 = true := by decide +kernel
theorem safe_4_17 : ∀ m, compatible p_4_17 m → WeightedBound 151 m := sound 151 _ cert_4_17 (by decide) checked_4_17
def p_4_18 := refine p_4 (4,false) (some ⟨true,false,4⟩)
def cert_4_18 : Tree := (.side 15 1 false (-1))
theorem checked_4_18 : check 151 p_4_18 cert_4_18 = true := by decide +kernel
theorem safe_4_18 : ∀ m, compatible p_4_18 m → WeightedBound 151 m := sound 151 _ cert_4_18 (by decide) checked_4_18
def p_4_19 := refine p_4 (4,false) (some ⟨true,true,4⟩)
def cert_4_19 : Tree := (split 18 (5,true) 6 #[
(.side 7 15 false (1)),
(.side 21 1 true (3)),
(.side 7 13 false (1)),
(.side 21 1 true (3)),
(.side 25 1 true (1)),
(.last 20 (2,true)),
(.side 7 20 false (1)),
(.last 20 (2,true)),
(.last 19 (2,true)),
(.last 22 (2,true)),
(.last 19 (2,true)),
(.side 2 17 false (2)),
(.side 6 26 false (2)),
(.side 25 1 true (1)),
(.side 8 11 false (1)),
(.side 4 15 false (2)),
(.side 7 19 false (1)),
(.side 22 1 true (2)),
(.side 7 19 false (1)),
(.side 22 1 true (2)),
(.side 7 19 false (1)),
(.side 1 19 false (2)),
(.side 7 19 false (1)),
(.side 26 1 true (2))])
theorem checked_4_19 : check 151 p_4_19 cert_4_19 = true := by decide +kernel
theorem safe_4_19 : ∀ m, compatible p_4_19 m → WeightedBound 151 m := sound 151 _ cert_4_19 (by decide) checked_4_19
def p_4_20 := refine p_4 (4,false) (some ⟨false,false,5⟩)
def cert_4_20 : Tree := (.side 7 15 false (1))
theorem checked_4_20 : check 151 p_4_20 cert_4_20 = true := by decide +kernel
theorem safe_4_20 : ∀ m, compatible p_4_20 m → WeightedBound 151 m := sound 151 _ cert_4_20 (by decide) checked_4_20
def p_4_21 := refine p_4 (4,false) (some ⟨false,true,5⟩)
def cert_4_21 : Tree := (.side 7 15 false (1))
theorem checked_4_21 : check 151 p_4_21 cert_4_21 = true := by decide +kernel
theorem safe_4_21 : ∀ m, compatible p_4_21 m → WeightedBound 151 m := sound 151 _ cert_4_21 (by decide) checked_4_21
def p_4_22 := refine p_4 (4,false) (some ⟨true,false,5⟩)
def cert_4_22 : Tree := (.side 7 15 false (1))
theorem checked_4_22 : check 151 p_4_22 cert_4_22 = true := by decide +kernel
theorem safe_4_22 : ∀ m, compatible p_4_22 m → WeightedBound 151 m := sound 151 _ cert_4_22 (by decide) checked_4_22
def p_4_23 := refine p_4 (4,false) (some ⟨true,true,5⟩)
def cert_4_23 : Tree := (split 19 (5,true) 6 #[
(.side 7 16 true (-2)),
(.side 22 18 true (-2)),
(.side 7 14 true (-2)),
(.side 22 16 true (-2)),
(.side 23 3 true (1)),
(.side 20 3 true (2)),
(.side 7 21 false (1)),
(.side 20 3 true (2)),
(.last 20 (2,true)),
(.last 20 (2,true)),
(.last 20 (2,true)),
(.last 20 (2,true)),
(.side 40 3 true (-1)),
(.side 7 16 true (-2)),
(.side 8 12 true (-2)),
(.side 6 14 true (-2)),
(.side 7 20 false (1)),
(.side 21 3 true (0)),
(.side 7 20 false (1)),
(.side 22 3 true (2)),
(.side 7 20 false (1)),
(.side 1 65 true (-2)),
(.side 7 20 false (1)),
(.side 21 3 true (2))])
theorem checked_4_23 : check 151 p_4_23 cert_4_23 = true := by decide +kernel
theorem safe_4_23 : ∀ m, compatible p_4_23 m → WeightedBound 151 m := sound 151 _ cert_4_23 (by decide) checked_4_23
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 151 m := by
  apply split_safe 151 p_4 15 (4,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_4_0 | exact safe_4_1 | exact safe_4_2 | exact safe_4_3 | exact safe_4_4 | exact safe_4_5 | exact safe_4_6 | exact safe_4_7 | exact safe_4_8 | exact safe_4_9 | exact safe_4_10 | exact safe_4_11 | exact safe_4_12 | exact safe_4_13 | exact safe_4_14 | exact safe_4_15 | exact safe_4_16 | exact safe_4_17 | exact safe_4_18 | exact safe_4_19 | exact safe_4_20 | exact safe_4_21 | exact safe_4_22 | exact safe_4_23
def p_5 := refine parent (5,false) (some ⟨false,true,1⟩)
def p_5_0 := refine p_5 (2,true) (some ⟨false,false,0⟩)
def cert_5_0 : Tree := (.side 7 16 false (1))
theorem checked_5_0 : check 151 p_5_0 cert_5_0 = true := by decide +kernel
theorem safe_5_0 : ∀ m, compatible p_5_0 m → WeightedBound 151 m := sound 151 _ cert_5_0 (by decide) checked_5_0
def p_5_1 := refine p_5 (2,true) (some ⟨false,true,0⟩)
def cert_5_1 : Tree := (.side 18 18 false (3))
theorem checked_5_1 : check 151 p_5_1 cert_5_1 = true := by decide +kernel
theorem safe_5_1 : ∀ m, compatible p_5_1 m → WeightedBound 151 m := sound 151 _ cert_5_1 (by decide) checked_5_1
def p_5_2 := refine p_5 (2,true) (some ⟨true,false,0⟩)
def cert_5_2 : Tree := (.side 7 14 false (1))
theorem checked_5_2 : check 151 p_5_2 cert_5_2 = true := by decide +kernel
theorem safe_5_2 : ∀ m, compatible p_5_2 m → WeightedBound 151 m := sound 151 _ cert_5_2 (by decide) checked_5_2
def p_5_3 := refine p_5 (2,true) (some ⟨true,true,0⟩)
def cert_5_3 : Tree := (.side 18 16 false (3))
theorem checked_5_3 : check 151 p_5_3 cert_5_3 = true := by decide +kernel
theorem safe_5_3 : ∀ m, compatible p_5_3 m → WeightedBound 151 m := sound 151 _ cert_5_3 (by decide) checked_5_3
def p_5_4 := refine p_5 (2,true) (some ⟨false,false,1⟩)
def cert_5_4 : Tree := (split 17 (4,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 32 true (-2)),
(.side 60 3 true (2)),
(.side 3 15 true (-2)),
(.side 7 20 false (1)),
(.side 18 16 true (2)),
(.side 14 4 true (0)),
(.side 1 47 true (-2)),
(.side 6 20 false (2)),
(.side 0 36 true (-2)),
(.side 2 22 false (2)),
(.side 18 15 true (0)),
(.side 4 18 false (2)),
(.side 66 4 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 18 13 true (-1)),
(.side 7 20 false (1)),
(.side 35 1 true (3)),
(.side 25 1 false (-1)),
(.last 19 (5,true)),
(.side 18 17 true (0)),
(.last 18 (5,true)),
(.side 36 3 true (2)),
(.last 18 (5,true))])
theorem checked_5_4 : check 151 p_5_4 cert_5_4 = true := by decide +kernel
theorem safe_5_4 : ∀ m, compatible p_5_4 m → WeightedBound 151 m := sound 151 _ cert_5_4 (by decide) checked_5_4
def p_5_5 := refine p_5 (2,true) (some ⟨false,true,1⟩)
def cert_5_5 : Tree := (split 17 (4,false) 6 #[
(.side 33 45 true (-4)),
(.side 0 18 true (-2)),
(.side 16 3 true (2)),
(.side 163 45 true (9)),
(.side 194 45 true (4)),
(.side 62 45 true (0)),
(.side 119 45 true (3)),
(.side 1 17 true (-2)),
(.side 194 45 true (4)),
(.side 0 19 true (-2)),
(.side 119 45 true (3)),
(.side 70 45 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 16 4 true (2)),
(.side 37 45 true (-4)),
(.side 68 45 true (2)),
(.side 98 45 true (-3)),
(.side 17 1 true (3)),
(.side 82 45 true (2)),
(.side 17 1 true (3)),
(.side 72 45 true (2)),
(.side 11 44 true (-1)),
(.side 16 3 true (2)),
(.side 167 45 true (9))])
theorem checked_5_5 : check 151 p_5_5 cert_5_5 = true := by decide +kernel
theorem safe_5_5 : ∀ m, compatible p_5_5 m → WeightedBound 151 m := sound 151 _ cert_5_5 (by decide) checked_5_5
def p_5_6 := refine p_5 (2,true) (some ⟨true,false,1⟩)
def cert_5_6 : Tree := (.side 16 17 true (0))
theorem checked_5_6 : check 151 p_5_6 cert_5_6 = true := by decide +kernel
theorem safe_5_6 : ∀ m, compatible p_5_6 m → WeightedBound 151 m := sound 151 _ cert_5_6 (by decide) checked_5_6
def p_5_7 := refine p_5 (2,true) (some ⟨true,true,1⟩)
def cert_5_7 : Tree := (split 17 (4,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 18 true (-2)),
(.side 16 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 16 4 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 20 (5,true)),
(.side 17 1 true (3)),
(.last 20 (5,true)),
(.side 17 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 16 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)])
theorem checked_5_7 : check 151 p_5_7 cert_5_7 = true := by decide +kernel
theorem safe_5_7 : ∀ m, compatible p_5_7 m → WeightedBound 151 m := sound 151 _ cert_5_7 (by decide) checked_5_7
def p_5_8 := refine p_5 (2,true) (some ⟨false,false,2⟩)
def cert_5_8 : Tree := (.side 7 14 false (1))
theorem checked_5_8 : check 151 p_5_8 cert_5_8 = true := by decide +kernel
theorem safe_5_8 : ∀ m, compatible p_5_8 m → WeightedBound 151 m := sound 151 _ cert_5_8 (by decide) checked_5_8
def p_5_9 := refine p_5 (2,true) (some ⟨false,true,2⟩)
def cert_5_9 : Tree := (.side 0 48 true (-4))
theorem checked_5_9 : check 151 p_5_9 cert_5_9 = true := by decide +kernel
theorem safe_5_9 : ∀ m, compatible p_5_9 m → WeightedBound 151 m := sound 151 _ cert_5_9 (by decide) checked_5_9
def p_5_10 := refine p_5 (2,true) (some ⟨true,false,2⟩)
def cert_5_10 : Tree := (.side 7 14 false (1))
theorem checked_5_10 : check 151 p_5_10 cert_5_10 = true := by decide +kernel
theorem safe_5_10 : ∀ m, compatible p_5_10 m → WeightedBound 151 m := sound 151 _ cert_5_10 (by decide) checked_5_10
def p_5_11 := refine p_5 (2,true) (some ⟨true,true,2⟩)
def cert_5_11 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),.empty]⟩)
theorem checked_5_11 : check 151 p_5_11 cert_5_11 = true := by decide +kernel
theorem safe_5_11 : ∀ m, compatible p_5_11 m → WeightedBound 151 m := sound 151 _ cert_5_11 (by decide) checked_5_11
def p_5_12 := refine p_5 (2,true) (some ⟨false,false,3⟩)
def cert_5_12 : Tree := (.side 7 12 false (1))
theorem checked_5_12 : check 151 p_5_12 cert_5_12 = true := by decide +kernel
theorem safe_5_12 : ∀ m, compatible p_5_12 m → WeightedBound 151 m := sound 151 _ cert_5_12 (by decide) checked_5_12
def p_5_13 := refine p_5 (2,true) (some ⟨false,true,3⟩)
def cert_5_13 : Tree := (.side 7 16 false (2))
theorem checked_5_13 : check 151 p_5_13 cert_5_13 = true := by decide +kernel
theorem safe_5_13 : ∀ m, compatible p_5_13 m → WeightedBound 151 m := sound 151 _ cert_5_13 (by decide) checked_5_13
def p_5_14 := refine p_5 (2,true) (some ⟨true,false,3⟩)
def cert_5_14 : Tree := (.side 7 12 false (1))
theorem checked_5_14 : check 151 p_5_14 cert_5_14 = true := by decide +kernel
theorem safe_5_14 : ∀ m, compatible p_5_14 m → WeightedBound 151 m := sound 151 _ cert_5_14 (by decide) checked_5_14
def p_5_15 := refine p_5 (2,true) (some ⟨true,true,3⟩)
def cert_5_15 : Tree := (.side 7 14 false (2))
theorem checked_5_15 : check 151 p_5_15 cert_5_15 = true := by decide +kernel
theorem safe_5_15 : ∀ m, compatible p_5_15 m → WeightedBound 151 m := sound 151 _ cert_5_15 (by decide) checked_5_15
def p_5_16 := refine p_5 (2,true) (some ⟨false,false,4⟩)
def cert_5_16 : Tree := (.side 7 20 false (1))
theorem checked_5_16 : check 151 p_5_16 cert_5_16 = true := by decide +kernel
theorem safe_5_16 : ∀ m, compatible p_5_16 m → WeightedBound 151 m := sound 151 _ cert_5_16 (by decide) checked_5_16
def p_5_17 := refine p_5 (2,true) (some ⟨false,true,4⟩)
def cert_5_17 : Tree := (split 48 (4,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 48 3 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 44 15 true (1)),
(.side 46 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 48 4 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(false,0)],[(true,0),(true,3),(true,1)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)),(.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty),.empty]⟩),
(.side 48 1 true (4)),
(.automata ⟨⟨#[[(false,0)],[(false,0)],[(true,0),(true,3),(true,1)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) .empty),.empty]⟩),
(.side 48 1 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 44 16 true (1)),
(.side 48 3 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)])
theorem checked_5_17 : check 151 p_5_17 cert_5_17 = true := by decide +kernel
theorem safe_5_17 : ∀ m, compatible p_5_17 m → WeightedBound 151 m := sound 151 _ cert_5_17 (by decide) checked_5_17
def p_5_18 := refine p_5 (2,true) (some ⟨true,false,4⟩)
def cert_5_18 : Tree := (.side 12 4 true (-1))
theorem checked_5_18 : check 151 p_5_18 cert_5_18 = true := by decide +kernel
theorem safe_5_18 : ∀ m, compatible p_5_18 m → WeightedBound 151 m := sound 151 _ cert_5_18 (by decide) checked_5_18
def p_5_19 := refine p_5 (2,true) (some ⟨true,true,4⟩)
def cert_5_19 : Tree := (split 17 (5,true) 6 #[
(.side 7 18 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,9)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[(false,3)],[(true,3)],[(false,4),(true,4),(false,6),(true,6),(false,7),(true,7),(false,8),(true,8),(false,10),(false,11),(true,11),(false,12),(true,12)],[(false,5)],[(true,5)],[(false,9)],[(true,10)]],#[(0,1),(2,3),(4,5),(6,7),(8,8),(9,10),(8,8),(8,8),(8,8),(11,1),(8,12),(8,8),(8,8)]⟩,⟨#[[(false,0)],[(true,0)],[(true,1),(true,6)],[(true,2)],[(true,3)],[(false,2)],[(true,4)],[(false,4)]],#[(0,1),(0,2),(5,3),(0,4),(7,6),(0,0),(0,2),(0,0)]⟩,#[(.branch (.branch (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))]⟩),
(.side 7 16 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2)],[],[],[],[],[],[(true,5)],[],[],[],[],[],[],[],[],[],[],[],[(true,11),(true,27)],[],[],[],[(true,29)],[],[(true,30)],[(false,23)],[(true,23)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,14)],[],[(true,2)],[],[],[(false,4)],[(true,4)],[],[],[],[],[],[(true,8)],[],[],[],[],[],[],[(false,14)],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,14),(15,16),(3,17),(7,18),(19,10),(20,6),(21,2),(3,22),(3,23),(7,24),(13,25),(26,16),(27,10),(28,6),(3,29),(7,30),(13,31),(21,6),(7,22),(32,16),(33,10),(7,34),(13,35),(21,10),(13,22),(36,16),(13,37),(21,16),(21,22),(21,22)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) .empty) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty))) (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) .empty))) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))) .empty) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) .empty)) (.branch .leaf (.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .leaf) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) .empty))) .empty),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) .empty) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)),(.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))))]⟩),
(.last 19 (4,false)),
(.last 48 (4,false)),
(.last 35 (4,false)),
(.last 46 (4,false)),
(.last 19 (4,false)),
(.last 52 (4,false)),
(.side 7 18 false (2)),
(.side 7 20 false (2)),
(.side 7 14 false (2)),
(.last 21 (4,false)),
(.side 7 14 false (2)),
(.side 7 18 false (2)),
(.side 7 22 false (2)),
(.last 18 (4,false)),
(.last 22 (4,false)),
(.last 18 (4,false)),
(.side 7 22 false (2)),
(.last 33 (4,false)),
(.last 37 (4,false)),
(.last 92 (4,false))])
theorem checked_5_19 : check 151 p_5_19 cert_5_19 = true := by decide +kernel
theorem safe_5_19 : ∀ m, compatible p_5_19 m → WeightedBound 151 m := sound 151 _ cert_5_19 (by decide) checked_5_19
def p_5_20 := refine p_5 (2,true) (some ⟨false,false,5⟩)
def cert_5_20 : Tree := (split 16 (5,true) 6 #[
(.side 6 18 false (2)),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.side 1 16 false (2)),
(.side 17 15 true (0)),
(.side 7 21 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty)]⟩),
(.side 7 14 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty)]⟩),
(.side 7 14 false (1)),
(.side 7 18 false (1)),
(.side 7 12 false (1)),
(.last 64 (4,false)),
(.side 7 12 false (1)),
(.side 7 16 false (1)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.side 7 20 false (1)),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.last 19 (4,false))])
theorem checked_5_20 : check 151 p_5_20 cert_5_20 = true := by decide +kernel
theorem safe_5_20 : ∀ m, compatible p_5_20 m → WeightedBound 151 m := sound 151 _ cert_5_20 (by decide) checked_5_20
def p_5_21 := refine p_5 (2,true) (some ⟨false,true,5⟩)
def cert_5_21 : Tree := (split 16 (5,true) 6 #[
(.side 44 15 true (2)),
(.side 0 17 true (-2)),
(.last 19 (4,false)),
(.side 24 20 false (4)),
(.side 7 20 false (2)),
(.side 17 15 true (1)),
(.side 17 15 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,11)],[(true,1),(true,11)],[(false,2)],[(true,2)],[(false,3)],[(true,3)],[(false,4),(true,4),(false,6),(true,6),(false,7),(true,7),(false,8),(true,8),(false,9),(false,10),(true,10)],[(false,5)],[(true,5)],[(true,9)]],#[(0,1),(2,3),(4,5),(6,7),(8,8),(9,10),(8,8),(8,8),(8,8),(8,11),(8,8),(2,3)]⟩,⟨#[[(false,0)],[(true,0)],[(true,1),(true,6)],[(true,2)],[(true,3)],[(false,2)],[(true,4)]],#[(0,1),(0,2),(5,3),(0,4),(0,6),(0,0),(0,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) .empty),(.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) .empty),(.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))))]⟩),
(.side 7 18 false (2)),
(.side 0 48 true (-4)),
(.side 7 18 false (2)),
(.side 41 15 true (3)),
(.side 7 16 false (2)),
(.last 20 (4,false)),
(.side 7 16 false (2)),
(.side 19 18 false (3)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.side 45 15 true (1)),
(.side 17 15 true (2)),
(.last 19 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)))]⟩)])
theorem checked_5_21 : check 151 p_5_21 cert_5_21 = true := by decide +kernel
theorem safe_5_21 : ∀ m, compatible p_5_21 m → WeightedBound 151 m := sound 151 _ cert_5_21 (by decide) checked_5_21
def p_5_22 := refine p_5 (2,true) (some ⟨true,false,5⟩)
def cert_5_22 : Tree := (split 16 (5,true) 6 #[
(.side 3 18 false (2)),
(.side 17 13 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))]⟩),
(.side 7 16 false (2)),
(.side 1 16 false (2)),
(.last 36 (4,false)),
(.side 23 3 false (0)),
(.last 56 (4,false)),
(.side 7 14 false (1)),
(.last 40 (4,false)),
(.side 7 14 false (1)),
(.side 15 2 true (0)),
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) .empty),(.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))]⟩),
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.last 17 (4,false)),
(.side 17 17 true (0)),
(.last 17 (4,false)),
(.last 19 (4,false)),
(.side 13 4 true (-1)),
(.side 17 17 true (1)),
(.side 18 19 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))]⟩)])
theorem checked_5_22 : check 151 p_5_22 cert_5_22 = true := by decide +kernel
theorem safe_5_22 : ∀ m, compatible p_5_22 m → WeightedBound 151 m := sound 151 _ cert_5_22 (by decide) checked_5_22
def p_5_23 := refine p_5 (2,true) (some ⟨true,true,5⟩)
def cert_5_23 : Tree := (split 16 (5,true) 6 #[
(.side 7 18 false (2)),
(.side 24 20 false (4)),
(.side 7 16 false (2)),
(.side 24 18 false (4)),
(.last 18 (4,false)),
(.side 209 50 true (7)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2)],[],[],[],[],[],[(true,5)],[],[],[],[],[],[],[],[],[],[],[],[(true,11),(true,27)],[],[],[],[(true,29)],[],[(true,30)],[(false,23)],[(true,23)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,8)],[(false,4)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf))) .empty) .empty)) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .empty .leaf)) (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .leaf .leaf))) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) .empty),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .empty .leaf)) .empty)),(.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) .empty)))) .empty)]⟩),
(.side 229 54 true (7)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 15 2 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 7 14 false (2)),
(.last 20 (4,false)),
(.side 7 14 false (2)),
(.side 19 16 false (3)),
(.last 19 (4,false)),
(.last 17 (4,false)),
(.last 19 (4,false)),
(.last 17 (4,false)),
(.side 7 22 false (2)),
(.side 66 44 true (4)),
(.side 11 47 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩)])
theorem checked_5_23 : check 151 p_5_23 cert_5_23 = true := by decide +kernel
theorem safe_5_23 : ∀ m, compatible p_5_23 m → WeightedBound 151 m := sound 151 _ cert_5_23 (by decide) checked_5_23
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 151 m := by
  apply split_safe 151 p_5 15 (2,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_5_0 | exact safe_5_1 | exact safe_5_2 | exact safe_5_3 | exact safe_5_4 | exact safe_5_5 | exact safe_5_6 | exact safe_5_7 | exact safe_5_8 | exact safe_5_9 | exact safe_5_10 | exact safe_5_11 | exact safe_5_12 | exact safe_5_13 | exact safe_5_14 | exact safe_5_15 | exact safe_5_16 | exact safe_5_17 | exact safe_5_18 | exact safe_5_19 | exact safe_5_20 | exact safe_5_21 | exact safe_5_22 | exact safe_5_23
def p_6 := refine parent (5,false) (some ⟨true,false,1⟩)
def p_6_0 := refine p_6 (2,true) (some ⟨false,false,0⟩)
def cert_6_0 : Tree := (.side 7 15 false (1))
theorem checked_6_0 : check 151 p_6_0 cert_6_0 = true := by decide +kernel
theorem safe_6_0 : ∀ m, compatible p_6_0 m → WeightedBound 151 m := sound 151 _ cert_6_0 (by decide) checked_6_0
def p_6_1 := refine p_6 (2,true) (some ⟨false,true,0⟩)
def cert_6_1 : Tree := (.side 24 25 false (3))
theorem checked_6_1 : check 151 p_6_1 cert_6_1 = true := by decide +kernel
theorem safe_6_1 : ∀ m, compatible p_6_1 m → WeightedBound 151 m := sound 151 _ cert_6_1 (by decide) checked_6_1
def p_6_2 := refine p_6 (2,true) (some ⟨true,false,0⟩)
def cert_6_2 : Tree := (.side 7 13 false (1))
theorem checked_6_2 : check 151 p_6_2 cert_6_2 = true := by decide +kernel
theorem safe_6_2 : ∀ m, compatible p_6_2 m → WeightedBound 151 m := sound 151 _ cert_6_2 (by decide) checked_6_2
def p_6_3 := refine p_6 (2,true) (some ⟨true,true,0⟩)
def cert_6_3 : Tree := (.side 24 21 false (3))
theorem checked_6_3 : check 151 p_6_3 cert_6_3 = true := by decide +kernel
theorem safe_6_3 : ∀ m, compatible p_6_3 m → WeightedBound 151 m := sound 151 _ cert_6_3 (by decide) checked_6_3
def p_6_4 := refine p_6 (2,true) (some ⟨false,false,1⟩)
def cert_6_4 : Tree := (split 20 (4,false) 6 #[
(.side 0 21 false (2)),
(.side 28 44 true (-3)),
(.side 77 3 true (-5)),
(.side 28 26 false (3)),
(.side 7 19 false (1)),
(.side 7 19 false (1)),
(.side 17 4 true (-3)),
(.side 1 20 false (2)),
(.side 0 22 false (2)),
(.side 0 22 false (2)),
(.side 7 24 false (1)),
(.side 7 18 false (1)),
(.side 7 20 false (1)),
(.side 55 4 true (-1)),
(.side 9 12 false (0)),
(.side 7 16 false (1)),
(.side 20 1 false (-2)),
(.side 35 1 true (1)),
(.side 20 1 false (-2)),
(.last 24 (5,true)),
(.side 16 5 false (-2)),
(.last 31 (5,true)),
(.side 16 5 false (-2)),
(.side 13 8 true (-3))])
theorem checked_6_4 : check 151 p_6_4 cert_6_4 = true := by decide +kernel
theorem safe_6_4 : ∀ m, compatible p_6_4 m → WeightedBound 151 m := sound 151 _ cert_6_4 (by decide) checked_6_4
def p_6_5 := refine p_6 (2,true) (some ⟨false,true,1⟩)
def cert_6_5 : Tree := (.side 7 21 false (1))
theorem checked_6_5 : check 151 p_6_5 cert_6_5 = true := by decide +kernel
theorem safe_6_5 : ∀ m, compatible p_6_5 m → WeightedBound 151 m := sound 151 _ cert_6_5 (by decide) checked_6_5
def p_6_6 := refine p_6 (2,true) (some ⟨true,false,1⟩)
def cert_6_6 : Tree := (.side 14 5 false (-1))
theorem checked_6_6 : check 151 p_6_6 cert_6_6 = true := by decide +kernel
theorem safe_6_6 : ∀ m, compatible p_6_6 m → WeightedBound 151 m := sound 151 _ cert_6_6 (by decide) checked_6_6
def p_6_7 := refine p_6 (2,true) (some ⟨true,true,1⟩)
def cert_6_7 : Tree := (.side 6 19 false (2))
theorem checked_6_7 : check 151 p_6_7 cert_6_7 = true := by decide +kernel
theorem safe_6_7 : ∀ m, compatible p_6_7 m → WeightedBound 151 m := sound 151 _ cert_6_7 (by decide) checked_6_7
def p_6_8 := refine p_6 (2,true) (some ⟨false,false,2⟩)
def cert_6_8 : Tree := (.side 0 21 false (2))
theorem checked_6_8 : check 151 p_6_8 cert_6_8 = true := by decide +kernel
theorem safe_6_8 : ∀ m, compatible p_6_8 m → WeightedBound 151 m := sound 151 _ cert_6_8 (by decide) checked_6_8
def p_6_9 := refine p_6 (2,true) (some ⟨false,true,2⟩)
def cert_6_9 : Tree := (.side 6 21 false (2))
theorem checked_6_9 : check 151 p_6_9 cert_6_9 = true := by decide +kernel
theorem safe_6_9 : ∀ m, compatible p_6_9 m → WeightedBound 151 m := sound 151 _ cert_6_9 (by decide) checked_6_9
def p_6_10 := refine p_6 (2,true) (some ⟨true,false,2⟩)
def cert_6_10 : Tree := (.side 18 6 false (-2))
theorem checked_6_10 : check 151 p_6_10 cert_6_10 = true := by decide +kernel
theorem safe_6_10 : ∀ m, compatible p_6_10 m → WeightedBound 151 m := sound 151 _ cert_6_10 (by decide) checked_6_10
def p_6_11 := refine p_6 (2,true) (some ⟨true,true,2⟩)
def cert_6_11 : Tree := (.side 2 17 false (2))
theorem checked_6_11 : check 151 p_6_11 cert_6_11 = true := by decide +kernel
theorem safe_6_11 : ∀ m, compatible p_6_11 m → WeightedBound 151 m := sound 151 _ cert_6_11 (by decide) checked_6_11
def p_6_12 := refine p_6 (2,true) (some ⟨false,false,3⟩)
def cert_6_12 : Tree := (.side 8 11 false (0))
theorem checked_6_12 : check 151 p_6_12 cert_6_12 = true := by decide +kernel
theorem safe_6_12 : ∀ m, compatible p_6_12 m → WeightedBound 151 m := sound 151 _ cert_6_12 (by decide) checked_6_12
def p_6_13 := refine p_6 (2,true) (some ⟨false,true,3⟩)
def cert_6_13 : Tree := (split 22 (4,false) 6 #[
(.side 6 25 false (2)),
(.side 153 29 false (1)),
(.side 70 3 true (-4)),
(.side 4 23 false (2)),
(.side 6 23 false (2)),
(.side 74 27 false (1)),
(.side 6 23 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 2 21 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 2 21 false (2)),
(.side 4 25 false (2)),
(.side 4 19 false (2)),
(.side 62 4 true (-1)),
(.side 4 19 false (2)),
(.side 4 21 false (2)),
(.last 25 (5,true)),
(.side 49 1 true (-1)),
(.last 25 (5,true)),
(.last 24 (5,true)),
(.side 11 13 false (0)),
(.last 23 (5,true)),
(.side 11 13 false (0)),
(.last 23 (5,true))])
theorem checked_6_13 : check 151 p_6_13 cert_6_13 = true := by decide +kernel
theorem safe_6_13 : ∀ m, compatible p_6_13 m → WeightedBound 151 m := sound 151 _ cert_6_13 (by decide) checked_6_13
def p_6_14 := refine p_6 (2,true) (some ⟨true,false,3⟩)
def cert_6_14 : Tree := (.side 8 11 false (0))
theorem checked_6_14 : check 151 p_6_14 cert_6_14 = true := by decide +kernel
theorem safe_6_14 : ∀ m, compatible p_6_14 m → WeightedBound 151 m := sound 151 _ cert_6_14 (by decide) checked_6_14
def p_6_15 := refine p_6 (2,true) (some ⟨true,true,3⟩)
def cert_6_15 : Tree := (.side 4 15 false (2))
theorem checked_6_15 : check 151 p_6_15 cert_6_15 = true := by decide +kernel
theorem safe_6_15 : ∀ m, compatible p_6_15 m → WeightedBound 151 m := sound 151 _ cert_6_15 (by decide) checked_6_15
def p_6_16 := refine p_6 (2,true) (some ⟨false,false,4⟩)
def cert_6_16 : Tree := (.side 15 4 false (-1))
theorem checked_6_16 : check 151 p_6_16 cert_6_16 = true := by decide +kernel
theorem safe_6_16 : ∀ m, compatible p_6_16 m → WeightedBound 151 m := sound 151 _ cert_6_16 (by decide) checked_6_16
def p_6_17 := refine p_6 (2,true) (some ⟨false,true,4⟩)
def cert_6_17 : Tree := (split 19 (4,false) 6 #[
(.side 6 21 false (2)),
(.side 21 37 true (-2)),
(.side 69 3 true (-4)),
(.side 45 57 false (1)),
(.side 1 19 false (2)),
(.side 63 21 false (0)),
(.side 67 3 true (-5)),
(.side 4 37 false (2)),
(.side 7 17 false (1)),
(.side 4 41 false (2)),
(.side 7 17 false (1)),
(.side 7 21 false (1)),
(.side 7 15 false (1)),
(.side 41 4 true (1)),
(.side 7 15 false (1)),
(.side 7 19 false (1)),
(.side 15 6 false (-1)),
(.side 30 1 true (2)),
(.side 15 6 false (-1)),
(.last 22 (5,true)),
(.side 13 7 false (-1)),
(.side 38 4 true (-1)),
(.side 13 7 false (-1)),
(.last 27 (5,true))])
theorem checked_6_17 : check 151 p_6_17 cert_6_17 = true := by decide +kernel
theorem safe_6_17 : ∀ m, compatible p_6_17 m → WeightedBound 151 m := sound 151 _ cert_6_17 (by decide) checked_6_17
def p_6_18 := refine p_6 (2,true) (some ⟨true,false,4⟩)
def cert_6_18 : Tree := (.side 15 4 false (-1))
theorem checked_6_18 : check 151 p_6_18 cert_6_18 = true := by decide +kernel
theorem safe_6_18 : ∀ m, compatible p_6_18 m → WeightedBound 151 m := sound 151 _ cert_6_18 (by decide) checked_6_18
def p_6_19 := refine p_6 (2,true) (some ⟨true,true,4⟩)
def cert_6_19 : Tree := (split 19 (4,false) 6 #[
(.side 3 17 false (2)),
(.last 117 (5,true)),
(.side 5 15 false (2)),
(.side 6 42 false (2)),
(.side 1 21 false (2)),
(.last 23 (5,true)),
(.side 11 9 false (0)),
(.last 23 (5,true)),
(.side 18 2 true (-2)),
(.last 25 (5,true)),
(.last 22 (5,true)),
(.side 6 19 false (2)),
(.side 7 13 false (1)),
(.side 51 4 true (1)),
(.side 7 13 false (1)),
(.side 6 17 false (2)),
(.last 21 (5,true)),
(.side 42 1 true (-2)),
(.last 21 (5,true)),
(.last 22 (5,true)),
(.last 20 (5,true)),
(.last 24 (5,true)),
(.last 20 (5,true)),
(.side 11 13 false (0))])
theorem checked_6_19 : check 151 p_6_19 cert_6_19 = true := by decide +kernel
theorem safe_6_19 : ∀ m, compatible p_6_19 m → WeightedBound 151 m := sound 151 _ cert_6_19 (by decide) checked_6_19
def p_6_20 := refine p_6 (2,true) (some ⟨false,false,5⟩)
def cert_6_20 : Tree := (split 19 (5,true) 6 #[
(.side 0 20 false (2)),
(.side 0 20 false (2)),
(.last 22 (4,false)),
(.side 6 21 false (2)),
(.side 7 18 false (1)),
(.side 7 18 false (1)),
(.side 17 3 false (-2)),
(.side 1 19 false (2)),
(.side 0 21 false (2)),
(.side 0 21 false (2)),
(.side 16 10 false (-2)),
(.side 7 17 false (1)),
(.last 23 (4,false)),
(.last 23 (4,false)),
(.side 9 11 false (0)),
(.side 7 15 false (1)),
(.last 20 (4,false)),
(.last 20 (4,false)),
(.last 20 (4,false)),
(.last 20 (4,false)),
(.side 16 4 false (-2)),
(.side 16 4 true (-3)),
(.side 16 4 false (-2)),
(.side 13 7 false (-1))])
theorem checked_6_20 : check 151 p_6_20 cert_6_20 = true := by decide +kernel
theorem safe_6_20 : ∀ m, compatible p_6_20 m → WeightedBound 151 m := sound 151 _ cert_6_20 (by decide) checked_6_20
def p_6_21 := refine p_6 (2,true) (some ⟨false,true,5⟩)
def cert_6_21 : Tree := (split 25 (5,true) 6 #[
(.side 27 3 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6),(false,4)],[(true,2),(true,6),(true,4)],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)))),(.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),.empty,(.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))))]⟩),
(.side 41 3 true (-4)),
(.side 28 27 false (3)),
(.side 6 27 false (2)),
(.last 27 (4,false)),
(.side 29 3 true (1)),
(.last 27 (4,false)),
(.side 6 25 false (2)),
(.side 26 3 true (2)),
(.side 6 25 false (2)),
(.side 26 3 true (2)),
(.side 6 23 false (2)),
(.side 43 3 true (-4)),
(.side 6 23 false (2)),
(.side 6 25 false (2)),
(.last 26 (4,false)),
(.side 27 3 true (0)),
(.last 26 (4,false)),
(.last 28 (4,false)),
(.side 66 3 true (-5)),
(.side 27 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6),(false,4)],[(true,2),(true,6),(true,4)],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),.empty,(.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)))),(.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))))]⟩),
(.side 33 3 true (0))])
theorem checked_6_21 : check 151 p_6_21 cert_6_21 = true := by decide +kernel
theorem safe_6_21 : ∀ m, compatible p_6_21 m → WeightedBound 151 m := sound 151 _ cert_6_21 (by decide) checked_6_21
def p_6_22 := refine p_6 (2,true) (some ⟨true,false,5⟩)
def cert_6_22 : Tree := (split 19 (5,true) 6 #[
(.side 7 20 false (1)),
(.side 7 16 false (1)),
(.side 10 10 false (0)),
(.side 3 17 false (2)),
(.side 7 18 false (1)),
(.last 21 (4,false)),
(.side 17 3 false (-2)),
(.last 21 (4,false)),
(.side 0 21 false (2)),
(.side 16 5 false (-2)),
(.side 16 10 false (-2)),
(.side 18 2 true (-3)),
(.last 23 (4,false)),
(.side 8 12 false (0)),
(.side 9 11 false (0)),
(.side 7 13 false (1)),
(.last 20 (4,false)),
(.side 15 5 false (-1)),
(.last 20 (4,false)),
(.last 22 (4,false)),
(.side 16 4 false (-2)),
(.side 31 5 true (1)),
(.side 16 4 false (-2)),
(.side 11 11 false (0))])
theorem checked_6_22 : check 151 p_6_22 cert_6_22 = true := by decide +kernel
theorem safe_6_22 : ∀ m, compatible p_6_22 m → WeightedBound 151 m := sound 151 _ cert_6_22 (by decide) checked_6_22
def p_6_23 := refine p_6 (2,true) (some ⟨true,true,5⟩)
def cert_6_23 : Tree := (.side 11 9 false (0))
theorem checked_6_23 : check 151 p_6_23 cert_6_23 = true := by decide +kernel
theorem safe_6_23 : ∀ m, compatible p_6_23 m → WeightedBound 151 m := sound 151 _ cert_6_23 (by decide) checked_6_23
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 151 m := by
  apply split_safe 151 p_6 18 (2,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_6_0 | exact safe_6_1 | exact safe_6_2 | exact safe_6_3 | exact safe_6_4 | exact safe_6_5 | exact safe_6_6 | exact safe_6_7 | exact safe_6_8 | exact safe_6_9 | exact safe_6_10 | exact safe_6_11 | exact safe_6_12 | exact safe_6_13 | exact safe_6_14 | exact safe_6_15 | exact safe_6_16 | exact safe_6_17 | exact safe_6_18 | exact safe_6_19 | exact safe_6_20 | exact safe_6_21 | exact safe_6_22 | exact safe_6_23
def p_7 := refine parent (5,false) (some ⟨true,true,1⟩)
def p_7_0 := refine p_7 (2,true) (some ⟨false,false,0⟩)
def cert_7_0 : Tree := (.side 6 14 false (2))
theorem checked_7_0 : check 151 p_7_0 cert_7_0 = true := by decide +kernel
theorem safe_7_0 : ∀ m, compatible p_7_0 m → WeightedBound 151 m := sound 151 _ cert_7_0 (by decide) checked_7_0
def p_7_1 := refine p_7 (2,true) (some ⟨false,true,0⟩)
def cert_7_1 : Tree := (.side 18 16 false (3))
theorem checked_7_1 : check 151 p_7_1 cert_7_1 = true := by decide +kernel
theorem safe_7_1 : ∀ m, compatible p_7_1 m → WeightedBound 151 m := sound 151 _ cert_7_1 (by decide) checked_7_1
def p_7_2 := refine p_7 (2,true) (some ⟨true,false,0⟩)
def cert_7_2 : Tree := (.side 6 12 false (2))
theorem checked_7_2 : check 151 p_7_2 cert_7_2 = true := by decide +kernel
theorem safe_7_2 : ∀ m, compatible p_7_2 m → WeightedBound 151 m := sound 151 _ cert_7_2 (by decide) checked_7_2
def p_7_3 := refine p_7 (2,true) (some ⟨true,true,0⟩)
def cert_7_3 : Tree := (.side 18 14 false (3))
theorem checked_7_3 : check 151 p_7_3 cert_7_3 = true := by decide +kernel
theorem safe_7_3 : ∀ m, compatible p_7_3 m → WeightedBound 151 m := sound 151 _ cert_7_3 (by decide) checked_7_3
def p_7_4 := refine p_7 (2,true) (some ⟨false,false,1⟩)
def cert_7_4 : Tree := (split 17 (4,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 32 true (-2)),
(.side 56 3 true (2)),
(.side 20 18 false (3)),
(.side 6 18 false (2)),
(.side 18 16 true (2)),
(.side 14 4 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 2 16 false (2)),
(.side 4 22 false (2)),
(.side 2 16 false (2)),
(.side 61 44 true (0)),
(.side 4 14 false (2)),
(.side 62 4 true (2)),
(.side 4 14 false (2)),
(.side 4 16 false (2)),
(.last 20 (5,true)),
(.side 53 1 true (3)),
(.last 20 (5,true)),
(.last 19 (5,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 18 (5,true)),
(.side 56 3 true (2)),
(.last 18 (5,true))])
theorem checked_7_4 : check 151 p_7_4 cert_7_4 = true := by decide +kernel
theorem safe_7_4 : ∀ m, compatible p_7_4 m → WeightedBound 151 m := sound 151 _ cert_7_4 (by decide) checked_7_4
def p_7_5 := refine p_7 (2,true) (some ⟨false,true,1⟩)
def cert_7_5 : Tree := (split 17 (4,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 18 true (-2)),
(.side 16 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 1 17 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 19 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 16 4 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 21 (5,true)),
(.side 17 1 true (3)),
(.last 21 (5,true)),
(.side 17 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 1 18 true (-2)),
(.side 16 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)])
theorem checked_7_5 : check 151 p_7_5 cert_7_5 = true := by decide +kernel
theorem safe_7_5 : ∀ m, compatible p_7_5 m → WeightedBound 151 m := sound 151 _ cert_7_5 (by decide) checked_7_5
def p_7_6 := refine p_7 (2,true) (some ⟨true,false,1⟩)
def cert_7_6 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty),.empty]⟩)
theorem checked_7_6 : check 151 p_7_6 cert_7_6 = true := by decide +kernel
theorem safe_7_6 : ∀ m, compatible p_7_6 m → WeightedBound 151 m := sound 151 _ cert_7_6 (by decide) checked_7_6
def p_7_7 := refine p_7 (2,true) (some ⟨true,true,1⟩)
def cert_7_7 : Tree := (split 17 (4,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 18 true (-2)),
(.side 16 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 16 4 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 20 (5,true)),
(.side 17 1 true (3)),
(.last 20 (5,true)),
(.side 17 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 1 18 true (-2)),
(.side 16 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)])
theorem checked_7_7 : check 151 p_7_7 cert_7_7 = true := by decide +kernel
theorem safe_7_7 : ∀ m, compatible p_7_7 m → WeightedBound 151 m := sound 151 _ cert_7_7 (by decide) checked_7_7
def p_7_8 := refine p_7 (2,true) (some ⟨false,false,2⟩)
def cert_7_8 : Tree := (.side 0 20 false (2))
theorem checked_7_8 : check 151 p_7_8 cert_7_8 = true := by decide +kernel
theorem safe_7_8 : ∀ m, compatible p_7_8 m → WeightedBound 151 m := sound 151 _ cert_7_8 (by decide) checked_7_8
def p_7_9 := refine p_7 (2,true) (some ⟨false,true,2⟩)
def cert_7_9 : Tree := (.side 0 46 true (-4))
theorem checked_7_9 : check 151 p_7_9 cert_7_9 = true := by decide +kernel
theorem safe_7_9 : ∀ m, compatible p_7_9 m → WeightedBound 151 m := sound 151 _ cert_7_9 (by decide) checked_7_9
def p_7_10 := refine p_7 (2,true) (some ⟨true,false,2⟩)
def cert_7_10 : Tree := (.side 16 6 false (0))
theorem checked_7_10 : check 151 p_7_10 cert_7_10 = true := by decide +kernel
theorem safe_7_10 : ∀ m, compatible p_7_10 m → WeightedBound 151 m := sound 151 _ cert_7_10 (by decide) checked_7_10
def p_7_11 := refine p_7 (2,true) (some ⟨true,true,2⟩)
def cert_7_11 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),.empty]⟩)
theorem checked_7_11 : check 151 p_7_11 cert_7_11 = true := by decide +kernel
theorem safe_7_11 : ∀ m, compatible p_7_11 m → WeightedBound 151 m := sound 151 _ cert_7_11 (by decide) checked_7_11
def p_7_12 := refine p_7 (2,true) (some ⟨false,false,3⟩)
def cert_7_12 : Tree := (.side 6 10 false (2))
theorem checked_7_12 : check 151 p_7_12 cert_7_12 = true := by decide +kernel
theorem safe_7_12 : ∀ m, compatible p_7_12 m → WeightedBound 151 m := sound 151 _ cert_7_12 (by decide) checked_7_12
def p_7_13 := refine p_7 (2,true) (some ⟨false,true,3⟩)
def cert_7_13 : Tree := (.side 6 14 false (2))
theorem checked_7_13 : check 151 p_7_13 cert_7_13 = true := by decide +kernel
theorem safe_7_13 : ∀ m, compatible p_7_13 m → WeightedBound 151 m := sound 151 _ cert_7_13 (by decide) checked_7_13
def p_7_14 := refine p_7 (2,true) (some ⟨true,false,3⟩)
def cert_7_14 : Tree := (.side 6 10 false (2))
theorem checked_7_14 : check 151 p_7_14 cert_7_14 = true := by decide +kernel
theorem safe_7_14 : ∀ m, compatible p_7_14 m → WeightedBound 151 m := sound 151 _ cert_7_14 (by decide) checked_7_14
def p_7_15 := refine p_7 (2,true) (some ⟨true,true,3⟩)
def cert_7_15 : Tree := (.side 6 12 false (2))
theorem checked_7_15 : check 151 p_7_15 cert_7_15 = true := by decide +kernel
theorem safe_7_15 : ∀ m, compatible p_7_15 m → WeightedBound 151 m := sound 151 _ cert_7_15 (by decide) checked_7_15
def p_7_16 := refine p_7 (2,true) (some ⟨false,false,4⟩)
def cert_7_16 : Tree := (split 17 (5,true) 6 #[
(.side 7 14 false (1)),
(.side 0 23 true (-2)),
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)]⟩),
(.last 19 (4,false)),
(.side 7 20 false (1)),
(.side 1 20 false (2)),
(.side 6 18 false (2)),
(.last 19 (4,false)),
(.side 6 20 false (2)),
(.last 19 (4,false)),
(.side 2 16 false (2)),
(.side 6 24 false (2)),
(.last 21 (4,false)),
(.side 8 10 false (1)),
(.side 4 14 false (2)),
(.side 1 19 false (2)),
(.last 18 (4,false)),
(.last 24 (4,false)),
(.last 18 (4,false)),
(.side 1 19 false (2)),
(.side 1 23 true (-2)),
(.side 6 23 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)]⟩)])
theorem checked_7_16 : check 151 p_7_16 cert_7_16 = true := by decide +kernel
theorem safe_7_16 : ∀ m, compatible p_7_16 m → WeightedBound 151 m := sound 151 _ cert_7_16 (by decide) checked_7_16
def p_7_17 := refine p_7 (2,true) (some ⟨false,true,4⟩)
def cert_7_17 : Tree := (split 44 (4,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 44 3 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 40 15 true (1)),
(.side 42 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 44 4 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 47 (5,true)),
(.side 44 1 true (4)),
(.last 47 (5,true)),
(.side 44 1 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 44 3 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)])
theorem checked_7_17 : check 151 p_7_17 cert_7_17 = true := by decide +kernel
theorem safe_7_17 : ∀ m, compatible p_7_17 m → WeightedBound 151 m := sound 151 _ cert_7_17 (by decide) checked_7_17
def p_7_18 := refine p_7 (2,true) (some ⟨true,false,4⟩)
def cert_7_18 : Tree := (split 17 (5,true) 6 #[
(.side 7 14 false (1)),
(.last 62 (4,false)),
(.side 7 12 false (1)),
(.last 60 (4,false)),
(.last 19 (4,false)),
(.side 12 8 true (-1)),
(.side 1 20 false (2)),
(.side 14 4 true (-1)),
(.last 19 (4,false)),
(.side 14 6 true (-1)),
(.last 19 (4,false)),
(.side 2 16 false (2)),
(.side 6 24 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty),(.branch (.branch .empty (.branch .leaf .leaf)) .empty)]⟩),
(.side 8 10 false (1)),
(.side 4 14 false (2)),
(.side 1 19 false (2)),
(.last 18 (4,false)),
(.last 24 (4,false)),
(.last 18 (4,false)),
(.side 1 19 false (2)),
(.last 62 (4,false)),
(.side 6 23 false (2)),
(.last 60 (4,false))])
theorem checked_7_18 : check 151 p_7_18 cert_7_18 = true := by decide +kernel
theorem safe_7_18 : ∀ m, compatible p_7_18 m → WeightedBound 151 m := sound 151 _ cert_7_18 (by decide) checked_7_18
def p_7_19 := refine p_7 (2,true) (some ⟨true,true,4⟩)
def cert_7_19 : Tree := (split 17 (5,true) 6 #[
(.side 6 16 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[],[(true,3)],[],[],[],[],[],[],[(false,7)],[(true,7)],[],[],[],[],[],[],[],[(true,27)],[],[],[(false,29)],[(true,29)],[],[(true,14),(true,30)],[(false,23)],[(true,23)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,14)],[],[(true,2)],[],[],[(false,4)],[(true,4)],[],[],[],[],[],[(true,8)],[],[],[],[],[],[],[(false,14)],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,14),(15,16),(3,17),(7,18),(19,10),(20,6),(21,2),(3,22),(3,23),(7,24),(13,25),(26,16),(27,10),(28,6),(3,29),(7,30),(13,31),(21,6),(7,22),(32,16),(33,10),(7,34),(13,35),(21,10),(13,22),(36,16),(13,37),(21,16),(21,22),(21,22)]⟩,#[(.branch (.branch (.branch .leaf (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) .empty) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) .empty))))),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .leaf) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) .empty)))) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) .empty)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty .leaf))) .empty) .empty)) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty))) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)))) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))) .leaf) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)))) .empty) .empty)) .empty),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) .empty)) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) .empty)) .empty),(.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) .empty))) .empty)),(.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty)) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))))))]⟩),
(.side 6 14 false (2)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,8)],[(false,2)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,14)],[],[(true,2)],[],[],[(false,4)],[(true,4)],[],[],[],[],[],[(true,8)],[],[],[],[],[],[],[(false,14)],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,14),(15,16),(3,17),(7,18),(19,10),(20,6),(21,2),(3,22),(3,23),(7,24),(13,25),(26,16),(27,10),(28,6),(3,29),(7,30),(13,31),(21,6),(7,22),(32,16),(33,10),(7,34),(13,35),(21,10),(13,22),(36,16),(13,37),(21,16),(21,22),(21,22)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) .empty),(.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)) .empty))]⟩),
(.last 19 (4,false)),
(.last 46 (4,false)),
(.side 6 22 false (2)),
(.last 44 (4,false)),
(.last 19 (4,false)),
(.last 50 (4,false)),
(.last 31 (4,false)),
(.side 6 18 false (2)),
(.side 6 12 false (2)),
(.last 21 (4,false)),
(.side 6 12 false (2)),
(.side 6 16 false (2)),
(.side 1 21 false (2)),
(.last 18 (4,false)),
(.last 24 (4,false)),
(.last 18 (4,false)),
(.side 1 21 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[],[(true,3)],[],[],[],[],[],[],[(false,7)],[(true,7)],[],[],[],[],[],[],[],[(true,27)],[],[],[(false,29)],[(true,29)],[],[(true,14),(true,30)],[(false,23)],[(true,23)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,14)],[],[(true,2)],[],[],[(false,4)],[(true,4)],[],[],[],[],[],[(true,8)],[],[],[],[],[],[],[(false,14)],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,14),(15,16),(3,17),(7,18),(19,10),(20,6),(21,2),(3,22),(3,23),(7,24),(13,25),(26,16),(27,10),(28,6),(3,29),(7,30),(13,31),(21,6),(7,22),(32,16),(33,10),(7,34),(13,35),(21,10),(13,22),(36,16),(13,37),(21,16),(21,22),(21,22)]⟩,#[(.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) .empty))))),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .leaf) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) .empty)))) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) .empty)))) .empty),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty .leaf))) .empty) .empty)) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty))) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)))) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))) .leaf) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)))) .empty) .empty)) .empty),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) .empty)) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) .empty)) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) .empty))) .empty)),(.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty)) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))))))]⟩),
(.side 11 11 false (2)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,8)],[(false,2)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,14)],[],[(true,2)],[],[],[(false,4)],[(true,4)],[],[],[],[],[],[(true,8)],[],[],[],[],[],[],[(false,14)],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,14),(15,16),(3,17),(7,18),(19,10),(20,6),(21,2),(3,22),(3,23),(7,24),(13,25),(26,16),(27,10),(28,6),(3,29),(7,30),(13,31),(21,6),(7,22),(32,16),(33,10),(7,34),(13,35),(21,10),(13,22),(36,16),(13,37),(21,16),(21,22),(21,22)]⟩,#[(.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)) .empty))]⟩)])
theorem checked_7_19 : check 151 p_7_19 cert_7_19 = true := by decide +kernel
theorem safe_7_19 : ∀ m, compatible p_7_19 m → WeightedBound 151 m := sound 151 _ cert_7_19 (by decide) checked_7_19
def p_7_20 := refine p_7 (2,true) (some ⟨false,false,5⟩)
def cert_7_20 : Tree := (split 16 (5,true) 6 #[
(.side 3 14 false (2)),
(.last 19 (4,false)),
(.side 5 12 false (2)),
(.last 19 (4,false)),
(.last 18 (4,false)),
(.side 60 44 true (0)),
(.side 6 20 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)]⟩),
(.side 0 20 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)]⟩),
(.side 21 5 false (-2)),
(.side 6 16 false (2)),
(.side 7 10 false (1)),
(.last 60 (4,false)),
(.side 7 10 false (1)),
(.side 6 14 false (2)),
(.last 19 (4,false)),
(.last 17 (4,false)),
(.last 19 (4,false)),
(.last 17 (4,false)),
(.side 1 19 false (2)),
(.last 19 (4,false)),
(.side 11 9 false (1)),
(.last 19 (4,false))])
theorem checked_7_20 : check 151 p_7_20 cert_7_20 = true := by decide +kernel
theorem safe_7_20 : ∀ m, compatible p_7_20 m → WeightedBound 151 m := sound 151 _ cert_7_20 (by decide) checked_7_20
def p_7_21 := refine p_7 (2,true) (some ⟨false,true,5⟩)
def cert_7_21 : Tree := (split 16 (5,true) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 0 17 true (-2)),
(.last 19 (4,false)),
(.side 24 18 false (4)),
(.side 6 18 false (2)),
(.side 57 27 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[],[(true,3)],[],[],[(false,13)],[(true,13)],[],[(true,14)],[(false,7),(false,15)],[(true,11)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,8)],[(false,4)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) .empty))) (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf) .empty))),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch .empty (.branch .empty .leaf))) .leaf) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty .leaf)) .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .leaf)))) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) .empty) .empty)]⟩),
(.side 6 16 false (2)),
(.side 0 46 true (-4)),
(.side 6 16 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 6 14 false (2)),
(.last 20 (4,false)),
(.side 6 14 false (2)),
(.side 19 16 false (3)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 1 17 true (-2)),
(.last 19 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)))]⟩)])
theorem checked_7_21 : check 151 p_7_21 cert_7_21 = true := by decide +kernel
theorem safe_7_21 : ∀ m, compatible p_7_21 m → WeightedBound 151 m := sound 151 _ cert_7_21 (by decide) checked_7_21
def p_7_22 := refine p_7 (2,true) (some ⟨true,false,5⟩)
def cert_7_22 : Tree := (split 16 (5,true) 6 #[
(.side 3 14 false (2)),
(.side 4 16 false (2)),
(.side 5 12 false (2)),
(.side 6 14 false (2)),
(.last 18 (4,false)),
(.last 54 (4,false)),
(.side 11 6 true (-1)),
(.last 52 (4,false)),
(.side 0 20 false (2)),
(.last 60 (4,false)),
(.side 11 15 false (1)),
(.side 15 2 true (0)),
(.side 7 10 false (1)),
(.side 4 14 false (2)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.last 19 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))]⟩),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.side 1 19 false (2)),
(.side 1 19 true (-2)),
(.side 11 9 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))]⟩)])
theorem checked_7_22 : check 151 p_7_22 cert_7_22 = true := by decide +kernel
theorem safe_7_22 : ∀ m, compatible p_7_22 m → WeightedBound 151 m := sound 151 _ cert_7_22 (by decide) checked_7_22
def p_7_23 := refine p_7 (2,true) (some ⟨true,true,5⟩)
def cert_7_23 : Tree := (split 16 (5,true) 6 #[
(.side 6 16 false (2)),
(.side 24 18 false (4)),
(.side 6 14 false (2)),
(.side 24 16 false (4)),
(.last 18 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[],[(true,3)],[],[],[],[(true,13)],[(false,14)],[(true,14)],[(false,15)],[(true,7),(true,11)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,8)],[(false,4)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)) .empty),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) .empty),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf)))) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty) .empty),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))),(.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) .empty)]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,8)],[(false,2)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,8)],[(false,4)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) .empty) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty),(.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) .empty) .empty)]⟩),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,8)],[(false,2)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,14)],[],[(true,2)],[],[],[(false,4)],[(true,4)],[],[],[],[],[],[(true,8)],[],[],[],[],[],[],[(false,14)],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,14),(15,16),(3,17),(7,18),(19,10),(20,6),(21,2),(3,22),(3,23),(7,24),(13,25),(26,16),(27,10),(28,6),(3,29),(7,30),(13,31),(21,6),(7,22),(32,16),(33,10),(7,34),(13,35),(21,10),(13,22),(36,16),(13,37),(21,16),(21,22),(21,22)]⟩,#[(.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty),.empty,(.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) .empty)]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 15 2 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 6 12 false (2)),
(.last 20 (4,false)),
(.side 6 12 false (2)),
(.side 19 14 false (3)),
(.last 21 (4,false)),
(.last 17 (4,false)),
(.last 21 (4,false)),
(.last 17 (4,false)),
(.side 1 21 false (2)),
(.side 1 46 true (-4)),
(.side 11 11 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩)])
theorem checked_7_23 : check 151 p_7_23 cert_7_23 = true := by decide +kernel
theorem safe_7_23 : ∀ m, compatible p_7_23 m → WeightedBound 151 m := sound 151 _ cert_7_23 (by decide) checked_7_23
theorem safe_7 : ∀ m, compatible p_7 m → WeightedBound 151 m := by
  apply split_safe 151 p_7 15 (2,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_7_0 | exact safe_7_1 | exact safe_7_2 | exact safe_7_3 | exact safe_7_4 | exact safe_7_5 | exact safe_7_6 | exact safe_7_7 | exact safe_7_8 | exact safe_7_9 | exact safe_7_10 | exact safe_7_11 | exact safe_7_12 | exact safe_7_13 | exact safe_7_14 | exact safe_7_15 | exact safe_7_16 | exact safe_7_17 | exact safe_7_18 | exact safe_7_19 | exact safe_7_20 | exact safe_7_21 | exact safe_7_22 | exact safe_7_23
def p_8 := refine parent (5,false) (some ⟨false,false,2⟩)
def p_8_0 := refine p_8 (2,true) (some ⟨false,false,0⟩)
def cert_8_0 : Tree := (.side 0 15 false (2))
theorem checked_8_0 : check 151 p_8_0 cert_8_0 = true := by decide +kernel
theorem safe_8_0 : ∀ m, compatible p_8_0 m → WeightedBound 151 m := sound 151 _ cert_8_0 (by decide) checked_8_0
def p_8_1 := refine p_8 (2,true) (some ⟨false,true,0⟩)
def cert_8_1 : Tree := (.side 20 17 false (3))
theorem checked_8_1 : check 151 p_8_1 cert_8_1 = true := by decide +kernel
theorem safe_8_1 : ∀ m, compatible p_8_1 m → WeightedBound 151 m := sound 151 _ cert_8_1 (by decide) checked_8_1
def p_8_2 := refine p_8 (2,true) (some ⟨true,false,0⟩)
def cert_8_2 : Tree := (split 17 (4,false) 6 #[
(.side 6 19 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 5 21 false (2)),
(.side 7 21 false (2)),
(.side 1 17 false (2)),
(.side 7 23 false (1)),
(.side 5 15 false (2)),
(.side 7 19 false (1)),
(.side 7 15 false (1)),
(.side 7 21 false (1)),
(.side 7 15 false (1)),
(.side 7 19 false (1)),
(.side 7 13 false (1)),
(.side 33 4 true (-1)),
(.side 7 13 false (1)),
(.side 7 17 false (1)),
(.side 0 22 false (2)),
(.side 6 23 false (2)),
(.side 0 22 false (2)),
(.last 20 (5,true)),
(.side 13 5 false (-1)),
(.side 6 21 false (2)),
(.side 13 5 false (-1)),
(.last 23 (5,true))])
theorem checked_8_2 : check 151 p_8_2 cert_8_2 = true := by decide +kernel
theorem safe_8_2 : ∀ m, compatible p_8_2 m → WeightedBound 151 m := sound 151 _ cert_8_2 (by decide) checked_8_2
def p_8_3 := refine p_8 (2,true) (some ⟨true,true,0⟩)
def cert_8_3 : Tree := (.side 20 16 false (3))
theorem checked_8_3 : check 151 p_8_3 cert_8_3 = true := by decide +kernel
theorem safe_8_3 : ∀ m, compatible p_8_3 m → WeightedBound 151 m := sound 151 _ cert_8_3 (by decide) checked_8_3
def p_8_4 := refine p_8 (2,true) (some ⟨false,false,1⟩)
def cert_8_4 : Tree := (.side 7 13 false (1))
theorem checked_8_4 : check 151 p_8_4 cert_8_4 = true := by decide +kernel
theorem safe_8_4 : ∀ m, compatible p_8_4 m → WeightedBound 151 m := sound 151 _ cert_8_4 (by decide) checked_8_4
def p_8_5 := refine p_8 (2,true) (some ⟨false,true,1⟩)
def cert_8_5 : Tree := (.side 7 13 false (1))
theorem checked_8_5 : check 151 p_8_5 cert_8_5 = true := by decide +kernel
theorem safe_8_5 : ∀ m, compatible p_8_5 m → WeightedBound 151 m := sound 151 _ cert_8_5 (by decide) checked_8_5
def p_8_6 := refine p_8 (2,true) (some ⟨true,false,1⟩)
def cert_8_6 : Tree := (.side 0 21 false (2))
theorem checked_8_6 : check 151 p_8_6 cert_8_6 = true := by decide +kernel
theorem safe_8_6 : ∀ m, compatible p_8_6 m → WeightedBound 151 m := sound 151 _ cert_8_6 (by decide) checked_8_6
def p_8_7 := refine p_8 (2,true) (some ⟨true,true,1⟩)
def cert_8_7 : Tree := (.side 1 14 false (2))
theorem checked_8_7 : check 151 p_8_7 cert_8_7 = true := by decide +kernel
theorem safe_8_7 : ∀ m, compatible p_8_7 m → WeightedBound 151 m := sound 151 _ cert_8_7 (by decide) checked_8_7
def p_8_8 := refine p_8 (2,true) (some ⟨false,false,2⟩)
def cert_8_8 : Tree := (.side 0 16 false (2))
theorem checked_8_8 : check 151 p_8_8 cert_8_8 = true := by decide +kernel
theorem safe_8_8 : ∀ m, compatible p_8_8 m → WeightedBound 151 m := sound 151 _ cert_8_8 (by decide) checked_8_8
def p_8_9 := refine p_8 (2,true) (some ⟨false,true,2⟩)
def cert_8_9 : Tree := (.side 0 16 false (2))
theorem checked_8_9 : check 151 p_8_9 cert_8_9 = true := by decide +kernel
theorem safe_8_9 : ∀ m, compatible p_8_9 m → WeightedBound 151 m := sound 151 _ cert_8_9 (by decide) checked_8_9
def p_8_10 := refine p_8 (2,true) (some ⟨true,false,2⟩)
def cert_8_10 : Tree := (.side 14 6 false (-2))
theorem checked_8_10 : check 151 p_8_10 cert_8_10 = true := by decide +kernel
theorem safe_8_10 : ∀ m, compatible p_8_10 m → WeightedBound 151 m := sound 151 _ cert_8_10 (by decide) checked_8_10
def p_8_11 := refine p_8 (2,true) (some ⟨true,true,2⟩)
def cert_8_11 : Tree := (.side 7 12 false (1))
theorem checked_8_11 : check 151 p_8_11 cert_8_11 = true := by decide +kernel
theorem safe_8_11 : ∀ m, compatible p_8_11 m → WeightedBound 151 m := sound 151 _ cert_8_11 (by decide) checked_8_11
def p_8_12 := refine p_8 (2,true) (some ⟨false,false,3⟩)
def cert_8_12 : Tree := (split 18 (4,false) 6 #[
(.side 6 20 false (2)),
(.side 22 26 false (0)),
(.side 6 24 false (2)),
(.side 7 20 false (1)),
(.side 1 18 false (2)),
(.side 8 24 false (0)),
(.side 7 14 false (1)),
(.side 7 22 false (1)),
(.side 7 16 false (1)),
(.side 7 24 false (1)),
(.side 7 16 false (1)),
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 7 26 false (1)),
(.side 7 14 false (1)),
(.side 7 18 false (1)),
(.side 0 23 false (2)),
(.side 7 28 false (1)),
(.side 0 23 false (2)),
(.last 22 (5,true)),
(.side 13 6 false (-1)),
(.side 6 22 false (2)),
(.side 13 6 false (-1)),
(.side 7 16 false (1))])
theorem checked_8_12 : check 151 p_8_12 cert_8_12 = true := by decide +kernel
theorem safe_8_12 : ∀ m, compatible p_8_12 m → WeightedBound 151 m := sound 151 _ cert_8_12 (by decide) checked_8_12
def p_8_13 := refine p_8 (2,true) (some ⟨false,true,3⟩)
def cert_8_13 : Tree := (split 18 (4,false) 6 #[
(.side 6 20 false (2)),
(.side 19 15 true (-1)),
(.side 34 3 true (0)),
(.side 7 18 false (2)),
(.side 1 18 false (2)),
(.side 6 24 false (2)),
(.side 4 18 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 16 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 16 false (1)),
(.side 7 20 false (2)),
(.side 7 14 false (1)),
(.side 37 4 true (0)),
(.side 7 14 false (1)),
(.side 7 16 false (1)),
(.side 0 23 false (2)),
(.side 7 18 false (1)),
(.side 0 23 false (2)),
(.last 20 (5,true)),
(.side 13 6 true (-2)),
(.last 19 (5,true)),
(.side 9 12 true (-2)),
(.last 19 (5,true))])
theorem checked_8_13 : check 151 p_8_13 cert_8_13 = true := by decide +kernel
theorem safe_8_13 : ∀ m, compatible p_8_13 m → WeightedBound 151 m := sound 151 _ cert_8_13 (by decide) checked_8_13
def p_8_14 := refine p_8 (2,true) (some ⟨true,false,3⟩)
def cert_8_14 : Tree := (.side 9 6 false (0))
theorem checked_8_14 : check 151 p_8_14 cert_8_14 = true := by decide +kernel
theorem safe_8_14 : ∀ m, compatible p_8_14 m → WeightedBound 151 m := sound 151 _ cert_8_14 (by decide) checked_8_14
def p_8_15 := refine p_8 (2,true) (some ⟨true,true,3⟩)
def cert_8_15 : Tree := (.side 7 10 false (1))
theorem checked_8_15 : check 151 p_8_15 cert_8_15 = true := by decide +kernel
theorem safe_8_15 : ∀ m, compatible p_8_15 m → WeightedBound 151 m := sound 151 _ cert_8_15 (by decide) checked_8_15
def p_8_16 := refine p_8 (2,true) (some ⟨false,false,4⟩)
def cert_8_16 : Tree := (split 15 (4,false) 6 #[
(.side 0 16 false (2)),
(.side 0 16 false (2)),
(.last 31 (5,true)),
(.side 6 17 false (2)),
(.side 7 14 false (1)),
(.side 7 14 false (1)),
(.side 0 21 false (2)),
(.side 1 15 false (2)),
(.side 0 17 false (2)),
(.side 0 17 false (2)),
(.last 21 (5,true)),
(.side 7 13 false (1)),
(.side 7 15 false (1)),
(.side 37 4 true (-1)),
(.side 9 7 false (0)),
(.side 7 11 false (1)),
(.side 15 1 false (-3)),
(.side 0 22 false (2)),
(.side 15 1 false (-3)),
(.last 20 (5,true)),
(.side 0 18 false (2)),
(.side 0 18 false (2)),
(.side 0 18 false (2)),
(.side 13 3 false (-1))])
theorem checked_8_16 : check 151 p_8_16 cert_8_16 = true := by decide +kernel
theorem safe_8_16 : ∀ m, compatible p_8_16 m → WeightedBound 151 m := sound 151 _ cert_8_16 (by decide) checked_8_16
def p_8_17 := refine p_8 (2,true) (some ⟨false,true,4⟩)
def cert_8_17 : Tree := (split 15 (4,false) 6 #[
(.side 0 16 false (2)),
(.side 0 22 true (-2)),
(.side 33 3 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 14 false (1)),
(.side 20 17 true (0)),
(.side 32 3 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 17 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 2 19 false (2)),
(.side 7 13 false (1)),
(.side 7 15 false (1)),
(.side 29 4 true (1)),
(.side 9 7 false (0)),
(.side 7 11 false (1)),
(.side 15 1 false (-1)),
(.side 0 20 false (2)),
(.side 15 1 false (-1)),
(.last 18 (5,true)),
(.side 0 18 false (2)),
(.side 0 18 false (2)),
(.side 0 18 false (2)),
(.last 19 (5,true))])
theorem checked_8_17 : check 151 p_8_17 cert_8_17 = true := by decide +kernel
theorem safe_8_17 : ∀ m, compatible p_8_17 m → WeightedBound 151 m := sound 151 _ cert_8_17 (by decide) checked_8_17
def p_8_18 := refine p_8 (2,true) (some ⟨true,false,4⟩)
def cert_8_18 : Tree := (split 15 (4,false) 6 #[
(.last 20 (5,true)),
(.side 7 12 false (1)),
(.side 10 6 false (0)),
(.side 3 13 false (2)),
(.side 7 14 false (1)),
(.side 0 23 false (2)),
(.side 0 21 false (2)),
(.last 21 (5,true)),
(.side 0 17 false (2)),
(.side 14 2 true (-3)),
(.last 21 (5,true)),
(.side 0 20 false (2)),
(.side 7 15 false (1)),
(.side 8 8 false (0)),
(.side 9 7 false (0)),
(.side 7 9 false (1)),
(.side 15 1 false (-3)),
(.side 0 19 false (2)),
(.side 15 1 false (-3)),
(.last 17 (5,true)),
(.side 0 18 false (2)),
(.last 16 (5,true)),
(.side 0 18 false (2)),
(.last 16 (5,true))])
theorem checked_8_18 : check 151 p_8_18 cert_8_18 = true := by decide +kernel
theorem safe_8_18 : ∀ m, compatible p_8_18 m → WeightedBound 151 m := sound 151 _ cert_8_18 (by decide) checked_8_18
def p_8_19 := refine p_8 (2,true) (some ⟨true,true,4⟩)
def cert_8_19 : Tree := (split 15 (4,false) 6 #[
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,4),(true,1)],[(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch .empty (.branch (.branch .leaf .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),.empty]⟩),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,4),(true,1)],[(false,2),(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))),.empty]⟩),
(.side 7 16 false (1)),
(.last 19 (5,true)),
(.side 0 20 false (2)),
(.last 19 (5,true)),
(.side 14 2 true (-2)),
(.last 21 (5,true)),
(.last 18 (5,true)),
(.side 2 14 false (2)),
(.side 8 8 false (0)),
(.side 29 4 true (1)),
(.side 8 8 false (0)),
(.side 4 12 false (2)),
(.side 0 19 false (2)),
(.side 7 16 false (1)),
(.side 0 19 false (2)),
(.last 18 (5,true)),
(.last 16 (5,true)),
(.side 7 14 false (1)),
(.last 16 (5,true)),
(.last 19 (5,true))])
theorem checked_8_19 : check 151 p_8_19 cert_8_19 = true := by decide +kernel
theorem safe_8_19 : ∀ m, compatible p_8_19 m → WeightedBound 151 m := sound 151 _ cert_8_19 (by decide) checked_8_19
def p_8_20 := refine p_8 (2,true) (some ⟨false,false,5⟩)
def cert_8_20 : Tree := (.side 0 17 false (2))
theorem checked_8_20 : check 151 p_8_20 cert_8_20 = true := by decide +kernel
theorem safe_8_20 : ∀ m, compatible p_8_20 m → WeightedBound 151 m := sound 151 _ cert_8_20 (by decide) checked_8_20
def p_8_21 := refine p_8 (2,true) (some ⟨false,true,5⟩)
def cert_8_21 : Tree := (.side 0 17 false (2))
theorem checked_8_21 : check 151 p_8_21 cert_8_21 = true := by decide +kernel
theorem safe_8_21 : ∀ m, compatible p_8_21 m → WeightedBound 151 m := sound 151 _ cert_8_21 (by decide) checked_8_21
def p_8_22 := refine p_8 (2,true) (some ⟨true,false,5⟩)
def cert_8_22 : Tree := (.side 0 17 false (2))
theorem checked_8_22 : check 151 p_8_22 cert_8_22 = true := by decide +kernel
theorem safe_8_22 : ∀ m, compatible p_8_22 m → WeightedBound 151 m := sound 151 _ cert_8_22 (by decide) checked_8_22
def p_8_23 := refine p_8 (2,true) (some ⟨true,true,5⟩)
def cert_8_23 : Tree := (.side 13 2 true (-2))
theorem checked_8_23 : check 151 p_8_23 cert_8_23 = true := by decide +kernel
theorem safe_8_23 : ∀ m, compatible p_8_23 m → WeightedBound 151 m := sound 151 _ cert_8_23 (by decide) checked_8_23
theorem safe_8 : ∀ m, compatible p_8 m → WeightedBound 151 m := by
  apply split_safe 151 p_8 14 (2,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_8_0 | exact safe_8_1 | exact safe_8_2 | exact safe_8_3 | exact safe_8_4 | exact safe_8_5 | exact safe_8_6 | exact safe_8_7 | exact safe_8_8 | exact safe_8_9 | exact safe_8_10 | exact safe_8_11 | exact safe_8_12 | exact safe_8_13 | exact safe_8_14 | exact safe_8_15 | exact safe_8_16 | exact safe_8_17 | exact safe_8_18 | exact safe_8_19 | exact safe_8_20 | exact safe_8_21 | exact safe_8_22 | exact safe_8_23
def p_9 := refine parent (5,false) (some ⟨false,true,2⟩)
def p_9_0 := refine p_9 (2,true) (some ⟨false,false,0⟩)
def cert_9_0 : Tree := (.side 6 16 false (2))
theorem checked_9_0 : check 151 p_9_0 cert_9_0 = true := by decide +kernel
theorem safe_9_0 : ∀ m, compatible p_9_0 m → WeightedBound 151 m := sound 151 _ cert_9_0 (by decide) checked_9_0
def p_9_1 := refine p_9 (2,true) (some ⟨false,true,0⟩)
def cert_9_1 : Tree := (.side 20 18 false (3))
theorem checked_9_1 : check 151 p_9_1 cert_9_1 = true := by decide +kernel
theorem safe_9_1 : ∀ m, compatible p_9_1 m → WeightedBound 151 m := sound 151 _ cert_9_1 (by decide) checked_9_1
def p_9_2 := refine p_9 (2,true) (some ⟨true,false,0⟩)
def cert_9_2 : Tree := (.side 6 14 false (2))
theorem checked_9_2 : check 151 p_9_2 cert_9_2 = true := by decide +kernel
theorem safe_9_2 : ∀ m, compatible p_9_2 m → WeightedBound 151 m := sound 151 _ cert_9_2 (by decide) checked_9_2
def p_9_3 := refine p_9 (2,true) (some ⟨true,true,0⟩)
def cert_9_3 : Tree := (.side 20 16 false (3))
theorem checked_9_3 : check 151 p_9_3 cert_9_3 = true := by decide +kernel
theorem safe_9_3 : ∀ m, compatible p_9_3 m → WeightedBound 151 m := sound 151 _ cert_9_3 (by decide) checked_9_3
def p_9_4 := refine p_9 (2,true) (some ⟨false,false,1⟩)
def cert_9_4 : Tree := (split 19 (4,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 36 true (-2)),
(.side 66 3 true (2)),
(.side 22 20 false (3)),
(.side 6 20 false (2)),
(.side 20 18 true (2)),
(.side 16 4 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 2 18 false (2)),
(.side 4 24 false (2)),
(.side 2 18 false (2)),
(.side 67 48 true (0)),
(.side 4 16 false (2)),
(.side 72 4 true (2)),
(.side 4 16 false (2)),
(.side 4 18 false (2)),
(.last 22 (5,true)),
(.side 63 1 true (3)),
(.last 22 (5,true)),
(.last 21 (5,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 20 (5,true)),
(.side 6 22 false (2)),
(.last 20 (5,true))])
theorem checked_9_4 : check 151 p_9_4 cert_9_4 = true := by decide +kernel
theorem safe_9_4 : ∀ m, compatible p_9_4 m → WeightedBound 151 m := sound 151 _ cert_9_4 (by decide) checked_9_4
def p_9_5 := refine p_9 (2,true) (some ⟨false,true,1⟩)
def cert_9_5 : Tree := (split 19 (4,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 20 true (-2)),
(.side 18 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 1 19 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 21 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 18 4 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 23 (5,true)),
(.side 19 1 true (3)),
(.last 23 (5,true)),
(.side 19 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 22 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)])
theorem checked_9_5 : check 151 p_9_5 cert_9_5 = true := by decide +kernel
theorem safe_9_5 : ∀ m, compatible p_9_5 m → WeightedBound 151 m := sound 151 _ cert_9_5 (by decide) checked_9_5
def p_9_6 := refine p_9 (2,true) (some ⟨true,false,1⟩)
def cert_9_6 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty),.empty]⟩)
theorem checked_9_6 : check 151 p_9_6 cert_9_6 = true := by decide +kernel
theorem safe_9_6 : ∀ m, compatible p_9_6 m → WeightedBound 151 m := sound 151 _ cert_9_6 (by decide) checked_9_6
def p_9_7 := refine p_9 (2,true) (some ⟨true,true,1⟩)
def cert_9_7 : Tree := (split 19 (4,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 20 true (-2)),
(.side 18 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 18 4 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 22 (5,true)),
(.side 19 1 true (3)),
(.last 22 (5,true)),
(.side 19 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 22 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)])
theorem checked_9_7 : check 151 p_9_7 cert_9_7 = true := by decide +kernel
theorem safe_9_7 : ∀ m, compatible p_9_7 m → WeightedBound 151 m := sound 151 _ cert_9_7 (by decide) checked_9_7
def p_9_8 := refine p_9 (2,true) (some ⟨false,false,2⟩)
def cert_9_8 : Tree := (.side 0 22 false (2))
theorem checked_9_8 : check 151 p_9_8 cert_9_8 = true := by decide +kernel
theorem safe_9_8 : ∀ m, compatible p_9_8 m → WeightedBound 151 m := sound 151 _ cert_9_8 (by decide) checked_9_8
def p_9_9 := refine p_9 (2,true) (some ⟨false,true,2⟩)
def cert_9_9 : Tree := (.side 0 50 true (-4))
theorem checked_9_9 : check 151 p_9_9 cert_9_9 = true := by decide +kernel
theorem safe_9_9 : ∀ m, compatible p_9_9 m → WeightedBound 151 m := sound 151 _ cert_9_9 (by decide) checked_9_9
def p_9_10 := refine p_9 (2,true) (some ⟨true,false,2⟩)
def cert_9_10 : Tree := (.side 18 6 false (0))
theorem checked_9_10 : check 151 p_9_10 cert_9_10 = true := by decide +kernel
theorem safe_9_10 : ∀ m, compatible p_9_10 m → WeightedBound 151 m := sound 151 _ cert_9_10 (by decide) checked_9_10
def p_9_11 := refine p_9 (2,true) (some ⟨true,true,2⟩)
def cert_9_11 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),.empty]⟩)
theorem checked_9_11 : check 151 p_9_11 cert_9_11 = true := by decide +kernel
theorem safe_9_11 : ∀ m, compatible p_9_11 m → WeightedBound 151 m := sound 151 _ cert_9_11 (by decide) checked_9_11
def p_9_12 := refine p_9 (2,true) (some ⟨false,false,3⟩)
def cert_9_12 : Tree := (.side 6 12 false (2))
theorem checked_9_12 : check 151 p_9_12 cert_9_12 = true := by decide +kernel
theorem safe_9_12 : ∀ m, compatible p_9_12 m → WeightedBound 151 m := sound 151 _ cert_9_12 (by decide) checked_9_12
def p_9_13 := refine p_9 (2,true) (some ⟨false,true,3⟩)
def cert_9_13 : Tree := (.side 6 16 false (2))
theorem checked_9_13 : check 151 p_9_13 cert_9_13 = true := by decide +kernel
theorem safe_9_13 : ∀ m, compatible p_9_13 m → WeightedBound 151 m := sound 151 _ cert_9_13 (by decide) checked_9_13
def p_9_14 := refine p_9 (2,true) (some ⟨true,false,3⟩)
def cert_9_14 : Tree := (.side 6 12 false (2))
theorem checked_9_14 : check 151 p_9_14 cert_9_14 = true := by decide +kernel
theorem safe_9_14 : ∀ m, compatible p_9_14 m → WeightedBound 151 m := sound 151 _ cert_9_14 (by decide) checked_9_14
def p_9_15 := refine p_9 (2,true) (some ⟨true,true,3⟩)
def cert_9_15 : Tree := (.side 6 14 false (2))
theorem checked_9_15 : check 151 p_9_15 cert_9_15 = true := by decide +kernel
theorem safe_9_15 : ∀ m, compatible p_9_15 m → WeightedBound 151 m := sound 151 _ cert_9_15 (by decide) checked_9_15
def p_9_16 := refine p_9 (2,true) (some ⟨false,false,4⟩)
def cert_9_16 : Tree := (split 19 (5,true) 6 #[
(.side 7 16 false (1)),
(.side 0 25 true (-2)),
(.side 7 14 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)]⟩),
(.last 21 (4,false)),
(.side 7 22 false (1)),
(.side 0 24 false (2)),
(.side 6 20 false (2)),
(.last 21 (4,false)),
(.side 6 22 false (2)),
(.last 21 (4,false)),
(.side 2 18 false (2)),
(.side 6 28 false (2)),
(.last 23 (4,false)),
(.side 8 12 false (1)),
(.side 4 16 false (2)),
(.side 0 23 false (2)),
(.last 20 (4,false)),
(.last 28 (4,false)),
(.last 20 (4,false)),
(.side 0 23 false (2)),
(.side 0 29 true (-2)),
(.last 23 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)]⟩)])
theorem checked_9_16 : check 151 p_9_16 cert_9_16 = true := by decide +kernel
theorem safe_9_16 : ∀ m, compatible p_9_16 m → WeightedBound 151 m := sound 151 _ cert_9_16 (by decide) checked_9_16
def p_9_17 := refine p_9 (2,true) (some ⟨false,true,4⟩)
def cert_9_17 : Tree := (split 54 (4,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 54 3 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 48 17 true (1)),
(.side 52 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 54 4 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 57 (5,true)),
(.side 54 1 true (4)),
(.last 57 (5,true)),
(.side 54 1 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 53 3 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)])
theorem checked_9_17 : check 151 p_9_17 cert_9_17 = true := by decide +kernel
theorem safe_9_17 : ∀ m, compatible p_9_17 m → WeightedBound 151 m := sound 151 _ cert_9_17 (by decide) checked_9_17
def p_9_18 := refine p_9 (2,true) (some ⟨true,false,4⟩)
def cert_9_18 : Tree := (split 19 (5,true) 6 #[
(.side 7 16 false (1)),
(.last 72 (4,false)),
(.side 7 14 false (1)),
(.last 70 (4,false)),
(.last 21 (4,false)),
(.side 12 10 true (-1)),
(.side 0 24 false (2)),
(.side 16 4 true (-1)),
(.last 21 (4,false)),
(.side 14 6 true (-1)),
(.last 21 (4,false)),
(.side 2 18 false (2)),
(.side 6 28 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty),(.branch (.branch .empty (.branch .leaf .leaf)) .empty)]⟩),
(.side 8 12 false (1)),
(.side 4 16 false (2)),
(.side 0 23 false (2)),
(.last 20 (4,false)),
(.last 28 (4,false)),
(.last 20 (4,false)),
(.side 0 23 false (2)),
(.last 22 (4,false)),
(.last 23 (4,false)),
(.last 22 (4,false))])
theorem checked_9_18 : check 151 p_9_18 cert_9_18 = true := by decide +kernel
theorem safe_9_18 : ∀ m, compatible p_9_18 m → WeightedBound 151 m := sound 151 _ cert_9_18 (by decide) checked_9_18
def p_9_19 := refine p_9 (2,true) (some ⟨true,true,4⟩)
def cert_9_19 : Tree := (split 19 (5,true) 6 #[
(.side 6 18 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[],[(true,3)],[],[],[],[],[],[],[(false,7)],[(true,7)],[],[],[],[],[],[],[],[(true,27)],[],[],[(false,29)],[(true,29)],[],[(true,14),(true,30)],[(false,23)],[(true,23)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,14)],[],[(true,2)],[],[],[(false,4)],[(true,4)],[],[],[],[],[],[(true,8)],[],[],[],[],[],[],[(false,14)],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,14),(15,16),(3,17),(7,18),(19,10),(20,6),(21,2),(3,22),(3,23),(7,24),(13,25),(26,16),(27,10),(28,6),(3,29),(7,30),(13,31),(21,6),(7,22),(32,16),(33,10),(7,34),(13,35),(21,10),(13,22),(36,16),(13,37),(21,16),(21,22),(21,22)]⟩,#[(.branch (.branch (.branch .leaf (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) .empty) (.branch .empty .leaf))) (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) .empty))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) .empty))))),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .leaf) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) .empty)))) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) .empty)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty .leaf))) .empty) .empty)) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty))) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)))) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))) .leaf) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) .empty)))) .empty) .empty)) .empty),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) .empty)) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) .empty)) .empty),(.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)) (.branch (.branch .empty .leaf) .empty))) .empty)),(.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty)) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))))))]⟩),
(.side 6 16 false (2)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,8)],[(false,2)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,14)],[],[(true,2)],[],[],[(false,4)],[(true,4)],[],[],[],[],[],[(true,8)],[],[],[],[],[],[],[(false,14)],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,14),(15,16),(3,17),(7,18),(19,10),(20,6),(21,2),(3,22),(3,23),(7,24),(13,25),(26,16),(27,10),(28,6),(3,29),(7,30),(13,31),(21,6),(7,22),(32,16),(33,10),(7,34),(13,35),(21,10),(13,22),(36,16),(13,37),(21,16),(21,22),(21,22)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) .empty),(.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)) .empty))]⟩),
(.last 21 (4,false)),
(.last 50 (4,false)),
(.side 6 26 false (2)),
(.last 48 (4,false)),
(.last 21 (4,false)),
(.last 54 (4,false)),
(.last 33 (4,false)),
(.side 6 20 false (2)),
(.side 6 14 false (2)),
(.last 23 (4,false)),
(.side 6 14 false (2)),
(.side 6 18 false (2)),
(.side 0 25 false (2)),
(.last 20 (4,false)),
(.last 28 (4,false)),
(.last 20 (4,false)),
(.side 0 25 false (2)),
(.side 0 58 true (-4)),
(.last 29 (4,false)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[],[(true,9),(true,10)],[(false,4)],[],[(false,12),(false,6)],[(true,6)],[],[(true,7),(true,18)],[],[],[],[],[],[(true,12)],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,2),(3,8),(9,10),(11,12),(13,14),(15,6),(16,6),(7,17),(9,18),(19,6),(20,8),(9,8),(21,12),(13,22),(16,12),(13,8),(23,12),(16,17),(20,17),(20,17)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,4),(false,8)],[(true,2)],[],[(true,4),(true,8)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,6),(7,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch (.branch .empty .leaf) .empty))) .empty))) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty .leaf) .empty))) .empty) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) (.branch .empty (.branch .leaf .leaf))))) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch (.branch .empty .leaf) .empty))) .empty))) .empty),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) (.branch .empty (.branch .leaf .leaf))))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) (.branch .empty (.branch .leaf .leaf))))) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch (.branch .empty .leaf) .empty))) .empty))))]⟩)])
theorem checked_9_19 : check 151 p_9_19 cert_9_19 = true := by decide +kernel
theorem safe_9_19 : ∀ m, compatible p_9_19 m → WeightedBound 151 m := sound 151 _ cert_9_19 (by decide) checked_9_19
def p_9_20 := refine p_9 (2,true) (some ⟨false,false,5⟩)
def cert_9_20 : Tree := (split 18 (5,true) 6 #[
(.side 3 16 false (2)),
(.last 21 (4,false)),
(.side 5 14 false (2)),
(.last 21 (4,false)),
(.last 20 (4,false)),
(.side 66 48 true (0)),
(.side 6 24 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)]⟩),
(.side 0 22 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)]⟩),
(.side 21 7 false (-2)),
(.side 6 18 false (2)),
(.side 7 12 false (1)),
(.last 70 (4,false)),
(.side 7 12 false (1)),
(.side 6 16 false (2)),
(.last 21 (4,false)),
(.last 19 (4,false)),
(.last 21 (4,false)),
(.last 19 (4,false)),
(.side 0 23 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty)]⟩),
(.side 19 9 false (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)]⟩)])
theorem checked_9_20 : check 151 p_9_20 cert_9_20 = true := by decide +kernel
theorem safe_9_20 : ∀ m, compatible p_9_20 m → WeightedBound 151 m := sound 151 _ cert_9_20 (by decide) checked_9_20
def p_9_21 := refine p_9 (2,true) (some ⟨false,true,5⟩)
def cert_9_21 : Tree := (split 18 (5,true) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 0 19 true (-2)),
(.last 21 (4,false)),
(.side 26 20 false (4)),
(.side 6 20 false (2)),
(.side 65 33 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[],[(true,3)],[],[],[(false,13)],[(true,13)],[],[(true,14)],[(false,7),(false,15)],[(true,11)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,8)],[(false,4)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) .empty))) (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf) .empty))),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch .empty (.branch .empty .leaf))) .leaf) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .leaf)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch .empty (.branch .leaf (.branch (.branch .empty (.branch .empty .leaf)) .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .leaf)))) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .leaf)) .empty) .empty) .empty),(.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) .empty) .empty)]⟩),
(.side 6 18 false (2)),
(.side 0 50 true (-4)),
(.side 6 18 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 6 16 false (2)),
(.last 22 (4,false)),
(.side 6 16 false (2)),
(.side 21 18 false (3)),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 0 21 true (-2)),
(.side 0 23 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)))]⟩)])
theorem checked_9_21 : check 151 p_9_21 cert_9_21 = true := by decide +kernel
theorem safe_9_21 : ∀ m, compatible p_9_21 m → WeightedBound 151 m := sound 151 _ cert_9_21 (by decide) checked_9_21
def p_9_22 := refine p_9 (2,true) (some ⟨true,false,5⟩)
def cert_9_22 : Tree := (split 18 (5,true) 6 #[
(.side 3 16 false (2)),
(.side 4 18 false (2)),
(.side 5 14 false (2)),
(.side 6 16 false (2)),
(.last 20 (4,false)),
(.last 64 (4,false)),
(.side 11 8 true (-1)),
(.last 62 (4,false)),
(.side 0 22 false (2)),
(.side 19 2 true (0)),
(.side 26 2 true (-5)),
(.side 17 2 true (0)),
(.side 7 12 false (1)),
(.side 4 16 false (2)),
(.side 7 12 false (1)),
(.side 6 14 false (2)),
(.last 21 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))]⟩),
(.last 21 (4,false)),
(.last 21 (4,false)),
(.side 0 23 false (2)),
(.side 0 23 true (-2)),
(.side 21 2 true (-3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))]⟩)])
theorem checked_9_22 : check 151 p_9_22 cert_9_22 = true := by decide +kernel
theorem safe_9_22 : ∀ m, compatible p_9_22 m → WeightedBound 151 m := sound 151 _ cert_9_22 (by decide) checked_9_22
def p_9_23 := refine p_9 (2,true) (some ⟨true,true,5⟩)
def cert_9_23 : Tree := (split 18 (5,true) 6 #[
(.side 6 18 false (2)),
(.side 26 20 false (4)),
(.side 6 16 false (2)),
(.side 26 18 false (4)),
(.last 20 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[],[(true,3)],[],[],[],[(true,13)],[(false,14)],[(true,14)],[(false,15)],[(true,7),(true,11)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,8)],[(false,4)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) .empty),(.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .leaf (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .leaf .leaf) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf)))) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty) .empty),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))),(.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) .empty)]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,8)],[(false,2)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,8)],[(false,4)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) .empty) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty),(.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty) .empty) .empty)]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 17 2 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 6 14 false (2)),
(.last 22 (4,false)),
(.side 6 14 false (2)),
(.side 21 16 false (3)),
(.last 23 (4,false)),
(.last 19 (4,false)),
(.last 23 (4,false)),
(.last 19 (4,false)),
(.side 0 25 false (2)),
(.side 0 54 true (-4)),
(.side 21 4 true (-3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩)])
theorem checked_9_23 : check 151 p_9_23 cert_9_23 = true := by decide +kernel
theorem safe_9_23 : ∀ m, compatible p_9_23 m → WeightedBound 151 m := sound 151 _ cert_9_23 (by decide) checked_9_23
theorem safe_9 : ∀ m, compatible p_9 m → WeightedBound 151 m := by
  apply split_safe 151 p_9 17 (2,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_9_0 | exact safe_9_1 | exact safe_9_2 | exact safe_9_3 | exact safe_9_4 | exact safe_9_5 | exact safe_9_6 | exact safe_9_7 | exact safe_9_8 | exact safe_9_9 | exact safe_9_10 | exact safe_9_11 | exact safe_9_12 | exact safe_9_13 | exact safe_9_14 | exact safe_9_15 | exact safe_9_16 | exact safe_9_17 | exact safe_9_18 | exact safe_9_19 | exact safe_9_20 | exact safe_9_21 | exact safe_9_22 | exact safe_9_23
def p_10 := refine parent (5,false) (some ⟨true,false,2⟩)
def p_10_0 := refine p_10 (2,true) (some ⟨false,false,0⟩)
def cert_10_0 : Tree := (.side 3 15 false (2))
theorem checked_10_0 : check 151 p_10_0 cert_10_0 = true := by decide +kernel
theorem safe_10_0 : ∀ m, compatible p_10_0 m → WeightedBound 151 m := sound 151 _ cert_10_0 (by decide) checked_10_0
def p_10_1 := refine p_10 (2,true) (some ⟨false,true,0⟩)
def cert_10_1 : Tree := (.side 7 11 false (1))
theorem checked_10_1 : check 151 p_10_1 cert_10_1 = true := by decide +kernel
theorem safe_10_1 : ∀ m, compatible p_10_1 m → WeightedBound 151 m := sound 151 _ cert_10_1 (by decide) checked_10_1
def p_10_2 := refine p_10 (2,true) (some ⟨true,false,0⟩)
def cert_10_2 : Tree := (.side 10 5 false (0))
theorem checked_10_2 : check 151 p_10_2 cert_10_2 = true := by decide +kernel
theorem safe_10_2 : ∀ m, compatible p_10_2 m → WeightedBound 151 m := sound 151 _ cert_10_2 (by decide) checked_10_2
def p_10_3 := refine p_10 (2,true) (some ⟨true,true,0⟩)
def cert_10_3 : Tree := (.side 3 12 false (2))
theorem checked_10_3 : check 151 p_10_3 cert_10_3 = true := by decide +kernel
theorem safe_10_3 : ∀ m, compatible p_10_3 m → WeightedBound 151 m := sound 151 _ cert_10_3 (by decide) checked_10_3
def p_10_4 := refine p_10 (2,true) (some ⟨false,false,1⟩)
def cert_10_4 : Tree := (.side 7 13 false (1))
theorem checked_10_4 : check 151 p_10_4 cert_10_4 = true := by decide +kernel
theorem safe_10_4 : ∀ m, compatible p_10_4 m → WeightedBound 151 m := sound 151 _ cert_10_4 (by decide) checked_10_4
def p_10_5 := refine p_10 (2,true) (some ⟨false,true,1⟩)
def cert_10_5 : Tree := (split 16 (4,false) 6 #[
(.side 31 21 false (2)),
(.side 17 13 true (-1)),
(.side 29 3 true (1)),
(.side 5 12 true (-2)),
(.side 7 15 false (1)),
(.side 53 17 true (3)),
(.side 7 19 false (2)),
(.side 1 22 true (-2)),
(.side 0 18 false (2)),
(.side 0 21 true (-2)),
(.side 2 22 false (2)),
(.side 7 55 true (-2)),
(.side 7 16 false (1)),
(.side 33 4 true (1)),
(.side 9 8 true (-2)),
(.side 7 10 true (-2)),
(.side 16 1 false (0)),
(.side 32 30 false (2)),
(.side 16 1 false (0)),
(.last 18 (5,true)),
(.side 26 29 false (2)),
(.last 17 (5,true)),
(.side 2 23 false (2)),
(.last 17 (5,true))])
theorem checked_10_5 : check 151 p_10_5 cert_10_5 = true := by decide +kernel
theorem safe_10_5 : ∀ m, compatible p_10_5 m → WeightedBound 151 m := sound 151 _ cert_10_5 (by decide) checked_10_5
def p_10_6 := refine p_10 (2,true) (some ⟨true,false,1⟩)
def cert_10_6 : Tree := (.side 11 13 false (0))
theorem checked_10_6 : check 151 p_10_6 cert_10_6 = true := by decide +kernel
theorem safe_10_6 : ∀ m, compatible p_10_6 m → WeightedBound 151 m := sound 151 _ cert_10_6 (by decide) checked_10_6
def p_10_7 := refine p_10 (2,true) (some ⟨true,true,1⟩)
def cert_10_7 : Tree := (split 16 (4,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 17 13 true (-1)),
(.side 29 3 true (1)),
(.side 7 16 false (2)),
(.side 1 16 false (2)),
(.side 56 17 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 14 false (1)),
(.side 1 49 true (-2)),
(.side 7 14 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 12 false (1)),
(.side 33 4 true (1)),
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 6 25 false (2)),
(.side 7 16 false (1)),
(.last 34 (5,true)),
(.last 18 (5,true)),
(.side 13 4 true (-2)),
(.last 17 (5,true)),
(.side 11 8 true (-2)),
(.last 17 (5,true))])
theorem checked_10_7 : check 151 p_10_7 cert_10_7 = true := by decide +kernel
theorem safe_10_7 : ∀ m, compatible p_10_7 m → WeightedBound 151 m := sound 151 _ cert_10_7 (by decide) checked_10_7
def p_10_8 := refine p_10 (2,true) (some ⟨false,false,2⟩)
def cert_10_8 : Tree := (.side 0 16 false (2))
theorem checked_10_8 : check 151 p_10_8 cert_10_8 = true := by decide +kernel
theorem safe_10_8 : ∀ m, compatible p_10_8 m → WeightedBound 151 m := sound 151 _ cert_10_8 (by decide) checked_10_8
def p_10_9 := refine p_10 (2,true) (some ⟨false,true,2⟩)
def cert_10_9 : Tree := (.side 0 52 true (-3))
theorem checked_10_9 : check 151 p_10_9 cert_10_9 = true := by decide +kernel
theorem safe_10_9 : ∀ m, compatible p_10_9 m → WeightedBound 151 m := sound 151 _ cert_10_9 (by decide) checked_10_9
def p_10_10 := refine p_10 (2,true) (some ⟨true,false,2⟩)
def cert_10_10 : Tree := (.side 14 6 false (-2))
theorem checked_10_10 : check 151 p_10_10 cert_10_10 = true := by decide +kernel
theorem safe_10_10 : ∀ m, compatible p_10_10 m → WeightedBound 151 m := sound 151 _ cert_10_10 (by decide) checked_10_10
def p_10_11 := refine p_10 (2,true) (some ⟨true,true,2⟩)
def cert_10_11 : Tree := (.side 2 14 false (2))
theorem checked_10_11 : check 151 p_10_11 cert_10_11 = true := by decide +kernel
theorem safe_10_11 : ∀ m, compatible p_10_11 m → WeightedBound 151 m := sound 151 _ cert_10_11 (by decide) checked_10_11
def p_10_12 := refine p_10 (2,true) (some ⟨false,false,3⟩)
def cert_10_12 : Tree := (split 18 (4,false) 6 #[
(.side 6 16 false (2)),
(.side 8 22 false (0)),
(.side 8 16 false (0)),
(.side 7 20 false (1)),
(.side 1 18 false (2)),
(.side 6 92 false (2)),
(.side 7 14 false (1)),
(.side 7 24 false (2)),
(.side 7 16 false (1)),
(.side 4 26 false (2)),
(.side 7 16 false (1)),
(.side 7 16 false (1)),
(.side 7 14 false (1)),
(.side 8 18 false (0)),
(.side 7 14 false (1)),
(.side 7 16 false (1)),
(.side 7 19 false (1)),
(.side 7 18 false (1)),
(.side 7 19 false (1)),
(.last 20 (5,true)),
(.side 13 6 false (-1)),
(.last 19 (5,true)),
(.side 13 6 false (-1)),
(.last 19 (5,true))])
theorem checked_10_12 : check 151 p_10_12 cert_10_12 = true := by decide +kernel
theorem safe_10_12 : ∀ m, compatible p_10_12 m → WeightedBound 151 m := sound 151 _ cert_10_12 (by decide) checked_10_12
def p_10_13 := refine p_10 (2,true) (some ⟨false,true,3⟩)
def cert_10_13 : Tree := (.side 8 7 false (0))
theorem checked_10_13 : check 151 p_10_13 cert_10_13 = true := by decide +kernel
theorem safe_10_13 : ∀ m, compatible p_10_13 m → WeightedBound 151 m := sound 151 _ cert_10_13 (by decide) checked_10_13
def p_10_14 := refine p_10 (2,true) (some ⟨true,false,3⟩)
def cert_10_14 : Tree := (.side 9 6 false (0))
theorem checked_10_14 : check 151 p_10_14 cert_10_14 = true := by decide +kernel
theorem safe_10_14 : ∀ m, compatible p_10_14 m → WeightedBound 151 m := sound 151 _ cert_10_14 (by decide) checked_10_14
def p_10_15 := refine p_10 (2,true) (some ⟨true,true,3⟩)
def cert_10_15 : Tree := (.side 7 8 false (1))
theorem checked_10_15 : check 151 p_10_15 cert_10_15 = true := by decide +kernel
theorem safe_10_15 : ∀ m, compatible p_10_15 m → WeightedBound 151 m := sound 151 _ cert_10_15 (by decide) checked_10_15
def p_10_16 := refine p_10 (2,true) (some ⟨false,false,4⟩)
def cert_10_16 : Tree := (split 15 (4,false) 6 #[
(.side 0 16 false (2)),
(.last 35 (5,true)),
(.last 31 (5,true)),
(.side 4 19 false (2)),
(.side 7 14 false (1)),
(.last 25 (5,true)),
(.last 25 (5,true)),
(.last 19 (5,true)),
(.side 0 17 false (2)),
(.last 21 (5,true)),
(.last 21 (5,true)),
(.side 7 13 false (1)),
(.side 7 15 false (1)),
(.side 9 7 false (0)),
(.side 9 7 false (0)),
(.side 7 11 false (1)),
(.side 15 1 false (-3)),
(.last 24 (5,true)),
(.side 15 1 false (-3)),
(.last 18 (5,true)),
(.last 22 (5,true)),
(.last 22 (5,true)),
(.last 22 (5,true)),
(.side 13 3 false (-1))])
theorem checked_10_16 : check 151 p_10_16 cert_10_16 = true := by decide +kernel
theorem safe_10_16 : ∀ m, compatible p_10_16 m → WeightedBound 151 m := sound 151 _ cert_10_16 (by decide) checked_10_16
def p_10_17 := refine p_10 (2,true) (some ⟨false,true,4⟩)
def cert_10_17 : Tree := (split 21 (4,false) 6 #[
(.side 6 24 false (2)),
(.side 52 28 false (0)),
(.side 87 3 true (-6)),
(.side 2 30 false (2)),
(.side 6 22 false (2)),
(.side 50 26 false (0)),
(.side 85 3 true (-7)),
(.side 2 30 false (2)),
(.side 2 20 false (2)),
(.side 2 32 false (2)),
(.side 2 20 false (2)),
(.side 4 24 false (2)),
(.side 4 18 false (2)),
(.side 2 28 false (2)),
(.side 4 18 false (2)),
(.side 4 22 false (2)),
(.last 24 (5,true)),
(.side 6 32 false (2)),
(.last 24 (5,true)),
(.last 24 (5,true)),
(.side 12 12 false (0)),
(.last 58 (5,true)),
(.side 12 12 false (0)),
(.side 2 24 false (2))])
theorem checked_10_17 : check 151 p_10_17 cert_10_17 = true := by decide +kernel
theorem safe_10_17 : ∀ m, compatible p_10_17 m → WeightedBound 151 m := sound 151 _ cert_10_17 (by decide) checked_10_17
def p_10_18 := refine p_10 (2,true) (some ⟨true,false,4⟩)
def cert_10_18 : Tree := (split 15 (4,false) 6 #[
(.last 20 (5,true)),
(.side 7 10 false (1)),
(.side 10 6 false (0)),
(.side 5 11 false (2)),
(.side 7 14 false (1)),
(.last 24 (5,true)),
(.last 25 (5,true)),
(.side 11 5 false (0)),
(.side 0 17 false (2)),
(.side 14 2 true (-3)),
(.last 21 (5,true)),
(.last 24 (5,true)),
(.side 7 15 false (1)),
(.side 8 8 false (0)),
(.side 9 7 false (0)),
(.side 7 9 false (1)),
(.side 15 1 false (-3)),
(.last 23 (5,true)),
(.side 15 1 false (-3)),
(.last 17 (5,true)),
(.last 22 (5,true)),
(.last 16 (5,true)),
(.last 22 (5,true)),
(.last 16 (5,true))])
theorem checked_10_18 : check 151 p_10_18 cert_10_18 = true := by decide +kernel
theorem safe_10_18 : ∀ m, compatible p_10_18 m → WeightedBound 151 m := sound 151 _ cert_10_18 (by decide) checked_10_18
def p_10_19 := refine p_10 (2,true) (some ⟨true,true,4⟩)
def cert_10_19 : Tree := (split 16 (5,true) 6 #[
(.side 0 17 false (2)),
(.last 59 (4,false)),
(.last 19 (4,false)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,8)],[(false,2)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,14)],[],[(true,2)],[],[(true,7)],[(false,4)],[(true,4)],[],[],[],[(false,7)],[],[(true,8)],[],[],[],[],[],[],[(false,14)],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,14),(15,16),(3,17),(7,18),(19,10),(20,6),(21,2),(3,22),(3,23),(7,24),(13,25),(26,16),(27,10),(28,6),(3,29),(7,30),(13,31),(21,6),(7,22),(32,16),(33,10),(7,34),(13,35),(21,10),(13,22),(36,16),(13,37),(21,16),(21,22),(21,22)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),(.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),(.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)) .empty))]⟩),
(.side 7 15 false (1)),
(.side 7 15 false (1)),
(.last 19 (4,false)),
(.side 1 16 false (2)),
(.side 0 18 false (2)),
(.side 0 18 false (2)),
(.last 21 (4,false)),
(.side 7 14 false (1)),
(.last 20 (4,false)),
(.last 20 (4,false)),
(.side 9 8 false (0)),
(.side 7 12 false (1)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 22 (4,false)),
(.last 22 (4,false)),
(.side 16 9 false (-2)),
(.side 13 4 true (-2))])
theorem checked_10_19 : check 151 p_10_19 cert_10_19 = true := by decide +kernel
theorem safe_10_19 : ∀ m, compatible p_10_19 m → WeightedBound 151 m := sound 151 _ cert_10_19 (by decide) checked_10_19
def p_10_20 := refine p_10 (2,true) (some ⟨false,false,5⟩)
def cert_10_20 : Tree := (split 20 (5,true) 6 #[
(.side 7 17 false (1)),
(.last 31 (4,false)),
(.side 7 15 false (1)),
(.last 31 (4,false)),
(.last 22 (4,false)),
(.side 7 23 false (1)),
(.side 15 8 false (-3)),
(.side 6 21 false (2)),
(.side 14 7 false (-2)),
(.side 6 23 false (2)),
(.side 14 7 false (-2)),
(.side 2 19 false (2)),
(.side 8 13 false (0)),
(.last 24 (4,false)),
(.side 8 13 false (0)),
(.side 4 17 false (2)),
(.side 15 7 false (-3)),
(.last 21 (4,false)),
(.side 15 7 false (-3)),
(.last 21 (4,false)),
(.side 15 7 false (-3)),
(.side 7 19 false (1)),
(.side 15 7 false (-3)),
(.side 13 11 false (-1))])
theorem checked_10_20 : check 151 p_10_20 cert_10_20 = true := by decide +kernel
theorem safe_10_20 : ∀ m, compatible p_10_20 m → WeightedBound 151 m := sound 151 _ cert_10_20 (by decide) checked_10_20
def p_10_21 := refine p_10 (2,true) (some ⟨false,true,5⟩)
def cert_10_21 : Tree := (split 15 (5,true) 6 #[
(.side 0 16 false (2)),
(.side 0 22 true (-2)),
(.last 18 (4,false)),
(.last 57 (4,false)),
(.side 7 14 false (1)),
(.side 7 33 true (-2)),
(.side 7 16 false (1)),
(.last 68 (4,false)),
(.side 0 17 false (2)),
(.side 0 112 true (-3)),
(.side 2 19 false (2)),
(.side 7 13 false (1)),
(.last 19 (4,false)),
(.last 33 (4,false)),
(.side 9 7 false (0)),
(.side 7 11 false (1)),
(.last 16 (4,false)),
(.last 16 (4,false)),
(.last 16 (4,false)),
(.last 16 (4,false)),
(.side 2 20 false (2)),
(.side 56 28 true (1)),
(.side 13 12 false (-1)),
(.side 20 3 true (2))])
theorem checked_10_21 : check 151 p_10_21 cert_10_21 = true := by decide +kernel
theorem safe_10_21 : ∀ m, compatible p_10_21 m → WeightedBound 151 m := sound 151 _ cert_10_21 (by decide) checked_10_21
def p_10_22 := refine p_10 (2,true) (some ⟨true,false,5⟩)
def cert_10_22 : Tree := (split 20 (5,true) 6 #[
(.side 7 17 false (1)),
(.side 7 19 false (1)),
(.side 7 15 false (1)),
(.side 6 17 false (2)),
(.last 22 (4,false)),
(.side 7 21 false (1)),
(.side 15 8 false (-3)),
(.side 11 15 false (0)),
(.side 14 7 false (-2)),
(.side 13 9 false (-1)),
(.side 14 7 false (-2)),
(.side 19 2 true (-4)),
(.side 8 13 false (0)),
(.side 7 17 false (1)),
(.side 8 13 false (0)),
(.side 6 15 false (2)),
(.side 15 7 false (-3)),
(.side 12 9 false (0)),
(.side 15 7 false (-3)),
(.last 23 (4,false)),
(.side 15 7 false (-3)),
(.side 31 7 true (1)),
(.side 15 7 false (-3)),
(.side 28 5 true (0))])
theorem checked_10_22 : check 151 p_10_22 cert_10_22 = true := by decide +kernel
theorem safe_10_22 : ∀ m, compatible p_10_22 m → WeightedBound 151 m := sound 151 _ cert_10_22 (by decide) checked_10_22
def p_10_23 := refine p_10 (2,true) (some ⟨true,true,5⟩)
def cert_10_23 : Tree := (split 15 (5,true) 6 #[
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[],[(true,2),(true,8)],[],[(true,7)],[(false,4)],[(true,4)],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,4),(5,14),(3,15),(7,16),(17,10),(18,6),(3,19),(7,20),(13,11),(12,14),(21,10),(7,22),(13,15),(18,14),(13,19)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),(.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),.empty,(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)),(.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))]⟩),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[],[(true,2),(true,8)],[],[(true,7)],[(false,4)],[(true,4)],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,4),(5,14),(3,15),(7,16),(17,10),(18,6),(3,19),(7,20),(13,11),(12,14),(21,10),(7,22),(13,15),(18,14),(13,19)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),.empty,(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)),(.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))))]⟩),
(.last 17 (4,false)),
(.side 26 24 false (2)),
(.side 11 20 false (0)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,8)],[(false,2)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,14)],[],[(true,2)],[],[(true,7)],[(false,4)],[(true,4)],[],[],[],[],[],[(true,8)],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,14),(15,16),(3,17),(7,18),(19,10),(20,6),(21,2),(3,22),(3,23),(7,24),(13,25),(26,16),(27,10),(28,6),(3,29),(7,30),(13,31),(21,6),(7,22),(32,16),(33,10),(7,34),(13,35),(21,10),(13,22),(36,16),(13,37),(21,16),(21,22),(21,22)]⟩,#[(.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty),.empty,(.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) .empty),(.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)))]⟩),
(.side 13 4 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2),(true,6)],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),.empty,(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))))]⟩),
(.side 14 2 true (-2)),
(.side 2 14 false (2)),
(.side 8 8 false (0)),
(.last 33 (4,false)),
(.side 8 8 false (0)),
(.side 4 12 false (2)),
(.side 15 11 false (-1)),
(.last 16 (4,false)),
(.side 15 11 false (-1)),
(.last 16 (4,false)),
(.side 15 11 false (-1)),
(.side 7 14 false (1)),
(.side 15 9 false (-1)),
(.side 20 3 true (2))])
theorem checked_10_23 : check 151 p_10_23 cert_10_23 = true := by decide +kernel
theorem safe_10_23 : ∀ m, compatible p_10_23 m → WeightedBound 151 m := sound 151 _ cert_10_23 (by decide) checked_10_23
theorem safe_10 : ∀ m, compatible p_10 m → WeightedBound 151 m := by
  apply split_safe 151 p_10 14 (2,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_10_0 | exact safe_10_1 | exact safe_10_2 | exact safe_10_3 | exact safe_10_4 | exact safe_10_5 | exact safe_10_6 | exact safe_10_7 | exact safe_10_8 | exact safe_10_9 | exact safe_10_10 | exact safe_10_11 | exact safe_10_12 | exact safe_10_13 | exact safe_10_14 | exact safe_10_15 | exact safe_10_16 | exact safe_10_17 | exact safe_10_18 | exact safe_10_19 | exact safe_10_20 | exact safe_10_21 | exact safe_10_22 | exact safe_10_23
def p_11 := refine parent (5,false) (some ⟨true,true,2⟩)
def cert_11 : Tree := (.side 2 12 false (2))
theorem checked_11 : check 151 p_11 cert_11 = true := by decide +kernel
theorem safe_11 : ∀ m, compatible p_11 m → WeightedBound 151 m := sound 151 _ cert_11 (by decide) checked_11
def p_12 := refine parent (5,false) (some ⟨false,false,3⟩)
def cert_12 : Tree := (.side 8 6 false (0))
theorem checked_12 : check 151 p_12 cert_12 = true := by decide +kernel
theorem safe_12 : ∀ m, compatible p_12 m → WeightedBound 151 m := sound 151 _ cert_12 (by decide) checked_12
def p_13 := refine parent (5,false) (some ⟨false,true,3⟩)
def p_13_0 := refine p_13 (4,false) (some ⟨false,false,0⟩)
def cert_13_0 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_13_0 : check 151 p_13_0 cert_13_0 = true := by decide +kernel
theorem safe_13_0 : ∀ m, compatible p_13_0 m → WeightedBound 151 m := sound 151 _ cert_13_0 (by decide) checked_13_0
def p_13_1 := refine p_13 (4,false) (some ⟨false,true,0⟩)
def cert_13_1 : Tree := (.side 0 28 true (-2))
theorem checked_13_1 : check 151 p_13_1 cert_13_1 = true := by decide +kernel
theorem safe_13_1 : ∀ m, compatible p_13_1 m → WeightedBound 151 m := sound 151 _ cert_13_1 (by decide) checked_13_1
def p_13_2 := refine p_13 (4,false) (some ⟨true,false,0⟩)
def cert_13_2 : Tree := (.side 25 3 true (1))
theorem checked_13_2 : check 151 p_13_2 cert_13_2 = true := by decide +kernel
theorem safe_13_2 : ∀ m, compatible p_13_2 m → WeightedBound 151 m := sound 151 _ cert_13_2 (by decide) checked_13_2
def p_13_3 := refine p_13 (4,false) (some ⟨true,true,0⟩)
def cert_13_3 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_13_3 : check 151 p_13_3 cert_13_3 = true := by decide +kernel
theorem safe_13_3 : ∀ m, compatible p_13_3 m → WeightedBound 151 m := sound 151 _ cert_13_3 (by decide) checked_13_3
def p_13_4 := refine p_13 (4,false) (some ⟨false,false,1⟩)
def cert_13_4 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_13_4 : check 151 p_13_4 cert_13_4 = true := by decide +kernel
theorem safe_13_4 : ∀ m, compatible p_13_4 m → WeightedBound 151 m := sound 151 _ cert_13_4 (by decide) checked_13_4
def p_13_5 := refine p_13 (4,false) (some ⟨false,true,1⟩)
def cert_13_5 : Tree := (.side 14 21 true (-1))
theorem checked_13_5 : check 151 p_13_5 cert_13_5 = true := by decide +kernel
theorem safe_13_5 : ∀ m, compatible p_13_5 m → WeightedBound 151 m := sound 151 _ cert_13_5 (by decide) checked_13_5
def p_13_6 := refine p_13 (4,false) (some ⟨true,false,1⟩)
def cert_13_6 : Tree := (split 29 (2,true) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 26 4 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 21 9 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 36 false (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 32 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 24 6 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 31 (5,true)),
(.side 27 3 true (2)),
(.last 31 (5,true)),
(.side 21 10 true (1)),
(.last 30 (5,true)),
(.side 23 7 true (1)),
(.last 30 (5,true)),
(.side 23 7 true (1))])
theorem checked_13_6 : check 151 p_13_6 cert_13_6 = true := by decide +kernel
theorem safe_13_6 : ∀ m, compatible p_13_6 m → WeightedBound 151 m := sound 151 _ cert_13_6 (by decide) checked_13_6
def p_13_7 := refine p_13 (4,false) (some ⟨true,true,1⟩)
def cert_13_7 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_13_7 : check 151 p_13_7 cert_13_7 = true := by decide +kernel
theorem safe_13_7 : ∀ m, compatible p_13_7 m → WeightedBound 151 m := sound 151 _ cert_13_7 (by decide) checked_13_7
def p_13_8 := refine p_13 (4,false) (some ⟨false,false,2⟩)
def cert_13_8 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_13_8 : check 151 p_13_8 cert_13_8 = true := by decide +kernel
theorem safe_13_8 : ∀ m, compatible p_13_8 m → WeightedBound 151 m := sound 151 _ cert_13_8 (by decide) checked_13_8
def p_13_9 := refine p_13 (4,false) (some ⟨false,true,2⟩)
def cert_13_9 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_13_9 : check 151 p_13_9 cert_13_9 = true := by decide +kernel
theorem safe_13_9 : ∀ m, compatible p_13_9 m → WeightedBound 151 m := sound 151 _ cert_13_9 (by decide) checked_13_9
def p_13_10 := refine p_13 (4,false) (some ⟨true,false,2⟩)
def cert_13_10 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_13_10 : check 151 p_13_10 cert_13_10 = true := by decide +kernel
theorem safe_13_10 : ∀ m, compatible p_13_10 m → WeightedBound 151 m := sound 151 _ cert_13_10 (by decide) checked_13_10
def p_13_11 := refine p_13 (4,false) (some ⟨true,true,2⟩)
def cert_13_11 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_13_11 : check 151 p_13_11 cert_13_11 = true := by decide +kernel
theorem safe_13_11 : ∀ m, compatible p_13_11 m → WeightedBound 151 m := sound 151 _ cert_13_11 (by decide) checked_13_11
def p_13_12 := refine p_13 (4,false) (some ⟨false,false,3⟩)
def cert_13_12 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_13_12 : check 151 p_13_12 cert_13_12 = true := by decide +kernel
theorem safe_13_12 : ∀ m, compatible p_13_12 m → WeightedBound 151 m := sound 151 _ cert_13_12 (by decide) checked_13_12
def p_13_13 := refine p_13 (4,false) (some ⟨false,true,3⟩)
def cert_13_13 : Tree := (.side 24 4 true (1))
theorem checked_13_13 : check 151 p_13_13 cert_13_13 = true := by decide +kernel
theorem safe_13_13 : ∀ m, compatible p_13_13 m → WeightedBound 151 m := sound 151 _ cert_13_13 (by decide) checked_13_13
def p_13_14 := refine p_13 (4,false) (some ⟨true,false,3⟩)
def cert_13_14 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_13_14 : check 151 p_13_14 cert_13_14 = true := by decide +kernel
theorem safe_13_14 : ∀ m, compatible p_13_14 m → WeightedBound 151 m := sound 151 _ cert_13_14 (by decide) checked_13_14
def p_13_15 := refine p_13 (4,false) (some ⟨true,true,3⟩)
def cert_13_15 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_13_15 : check 151 p_13_15 cert_13_15 = true := by decide +kernel
theorem safe_13_15 : ∀ m, compatible p_13_15 m → WeightedBound 151 m := sound 151 _ cert_13_15 (by decide) checked_13_15
def p_13_16 := refine p_13 (4,false) (some ⟨false,false,4⟩)
def cert_13_16 : Tree := (split 30 (5,true) 6 #[
(.side 3 28 false (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))]⟩),
(.side 5 26 false (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .leaf (.branch (.branch .empty .leaf) .leaf)),(.branch .leaf (.branch .empty .leaf))]⟩),
(.side 31 7 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))]⟩),
(.last 42 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .leaf (.branch (.branch .empty .leaf) .leaf)),(.branch .leaf (.branch .empty .leaf))]⟩),
(.last 31 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .leaf (.branch (.branch .empty .leaf) .leaf)),(.branch .leaf (.branch .empty .leaf))]⟩),
(.last 31 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .leaf (.branch (.branch .empty .leaf) .leaf)),(.branch .leaf (.branch .empty .leaf))]⟩),
(.side 63 7 false (-6)),
(.side 45 7 false (0)),
(.side 7 24 false (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .leaf (.branch (.branch .empty .leaf) .leaf)),(.branch .leaf (.branch .empty .leaf))]⟩),
(.side 33 1 false (-3)),
(.side 35 1 false (-1)),
(.side 33 1 false (-3)),
(.side 37 7 false (-1)),
(.side 33 7 false (-1)),
(.side 61 7 false (1)),
(.side 8 26 false (3)),
(.side 23 8 true (0))])
theorem checked_13_16 : check 151 p_13_16 cert_13_16 = true := by decide +kernel
theorem safe_13_16 : ∀ m, compatible p_13_16 m → WeightedBound 151 m := sound 151 _ cert_13_16 (by decide) checked_13_16
def p_13_17 := refine p_13 (4,false) (some ⟨false,true,4⟩)
def cert_13_17 : Tree := (.side 27 1 true (3))
theorem checked_13_17 : check 151 p_13_17 cert_13_17 = true := by decide +kernel
theorem safe_13_17 : ∀ m, compatible p_13_17 m → WeightedBound 151 m := sound 151 _ cert_13_17 (by decide) checked_13_17
def p_13_18 := refine p_13 (4,false) (some ⟨true,false,4⟩)
def cert_13_18 : Tree := (split 30 (5,true) 6 #[
(.side 3 28 false (3)),
(.side 20 11 true (0)),
(.side 5 26 false (3)),
(.side 20 11 true (0)),
(.side 54 1 false (-2)),
(.last 32 (2,true)),
(.last 42 (2,true)),
(.last 32 (2,true)),
(.last 31 (2,true)),
(.last 34 (2,true)),
(.last 31 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.side 33 37 false (0)),
(.side 14 17 true (-1)),
(.side 7 24 false (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.side 33 1 false (-3)),
(.side 35 1 false (-1)),
(.side 33 1 false (-3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩),
(.side 31 26 false (0)),
(.side 14 19 true (-1)),
(.side 8 26 false (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))]⟩)])
theorem checked_13_18 : check 151 p_13_18 cert_13_18 = true := by decide +kernel
theorem safe_13_18 : ∀ m, compatible p_13_18 m → WeightedBound 151 m := sound 151 _ cert_13_18 (by decide) checked_13_18
def p_13_19 := refine p_13 (4,false) (some ⟨true,true,4⟩)
def cert_13_19 : Tree := (.side 27 1 true (3))
theorem checked_13_19 : check 151 p_13_19 cert_13_19 = true := by decide +kernel
theorem safe_13_19 : ∀ m, compatible p_13_19 m → WeightedBound 151 m := sound 151 _ cert_13_19 (by decide) checked_13_19
def p_13_20 := refine p_13 (4,false) (some ⟨false,false,5⟩)
def cert_13_20 : Tree := (.side 23 5 true (1))
theorem checked_13_20 : check 151 p_13_20 cert_13_20 = true := by decide +kernel
theorem safe_13_20 : ∀ m, compatible p_13_20 m → WeightedBound 151 m := sound 151 _ cert_13_20 (by decide) checked_13_20
def p_13_21 := refine p_13 (4,false) (some ⟨false,true,5⟩)
def cert_13_21 : Tree := (.side 23 5 true (1))
theorem checked_13_21 : check 151 p_13_21 cert_13_21 = true := by decide +kernel
theorem safe_13_21 : ∀ m, compatible p_13_21 m → WeightedBound 151 m := sound 151 _ cert_13_21 (by decide) checked_13_21
def p_13_22 := refine p_13 (4,false) (some ⟨true,false,5⟩)
def cert_13_22 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_13_22 : check 151 p_13_22 cert_13_22 = true := by decide +kernel
theorem safe_13_22 : ∀ m, compatible p_13_22 m → WeightedBound 151 m := sound 151 _ cert_13_22 (by decide) checked_13_22
def p_13_23 := refine p_13 (4,false) (some ⟨true,true,5⟩)
def cert_13_23 : Tree := (.side 23 5 true (1))
theorem checked_13_23 : check 151 p_13_23 cert_13_23 = true := by decide +kernel
theorem safe_13_23 : ∀ m, compatible p_13_23 m → WeightedBound 151 m := sound 151 _ cert_13_23 (by decide) checked_13_23
theorem safe_13 : ∀ m, compatible p_13 m → WeightedBound 151 m := by
  apply split_safe 151 p_13 27 (4,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_13_0 | exact safe_13_1 | exact safe_13_2 | exact safe_13_3 | exact safe_13_4 | exact safe_13_5 | exact safe_13_6 | exact safe_13_7 | exact safe_13_8 | exact safe_13_9 | exact safe_13_10 | exact safe_13_11 | exact safe_13_12 | exact safe_13_13 | exact safe_13_14 | exact safe_13_15 | exact safe_13_16 | exact safe_13_17 | exact safe_13_18 | exact safe_13_19 | exact safe_13_20 | exact safe_13_21 | exact safe_13_22 | exact safe_13_23
def p_14 := refine parent (5,false) (some ⟨true,false,3⟩)
def cert_14 : Tree := (.side 8 6 false (0))
theorem checked_14 : check 151 p_14 cert_14 = true := by decide +kernel
theorem safe_14 : ∀ m, compatible p_14 m → WeightedBound 151 m := sound 151 _ cert_14 (by decide) checked_14
def p_15 := refine parent (5,false) (some ⟨true,true,3⟩)
def cert_15 : Tree := (.side 4 10 false (2))
theorem checked_15 : check 151 p_15 cert_15 = true := by decide +kernel
theorem safe_15 : ∀ m, compatible p_15 m → WeightedBound 151 m := sound 151 _ cert_15 (by decide) checked_15
def p_16 := refine parent (5,false) (some ⟨false,false,4⟩)
def p_16_0 := refine p_16 (4,false) (some ⟨false,false,0⟩)
def cert_16_0 : Tree := (.side 0 17 false (2))
theorem checked_16_0 : check 151 p_16_0 cert_16_0 = true := by decide +kernel
theorem safe_16_0 : ∀ m, compatible p_16_0 m → WeightedBound 151 m := sound 151 _ cert_16_0 (by decide) checked_16_0
def p_16_1 := refine p_16 (4,false) (some ⟨false,true,0⟩)
def cert_16_1 : Tree := (.side 0 17 false (2))
theorem checked_16_1 : check 151 p_16_1 cert_16_1 = true := by decide +kernel
theorem safe_16_1 : ∀ m, compatible p_16_1 m → WeightedBound 151 m := sound 151 _ cert_16_1 (by decide) checked_16_1
def p_16_2 := refine p_16 (4,false) (some ⟨true,false,0⟩)
def cert_16_2 : Tree := (split 34 (5,true) 6 #[
(.side 6 33 false (2)),
(.side 6 41 false (2)),
(.side 6 31 false (2)),
(.side 6 39 false (2)),
(.side 52 3 true (-2)),
(.side 6 39 false (2)),
(.last 41 (2,true)),
(.side 6 37 false (2)),
(.last 35 (2,true)),
(.side 6 39 false (2)),
(.last 35 (2,true)),
(.side 6 35 false (2)),
(.side 6 29 false (2)),
(.side 49 3 true (-1)),
(.side 6 29 false (2)),
(.side 6 33 false (2)),
(.side 78 3 true (-11)),
(.side 48 3 true (-1)),
(.side 35 15 false (-3)),
(.side 6 33 false (2)),
(.side 78 3 true (-11)),
(.side 6 33 false (2)),
(.side 37 11 false (-5)),
(.side 102 3 true (-11))])
theorem checked_16_2 : check 151 p_16_2 cert_16_2 = true := by decide +kernel
theorem safe_16_2 : ∀ m, compatible p_16_2 m → WeightedBound 151 m := sound 151 _ cert_16_2 (by decide) checked_16_2
def p_16_3 := refine p_16 (4,false) (some ⟨true,true,0⟩)
def cert_16_3 : Tree := (.side 6 18 false (2))
theorem checked_16_3 : check 151 p_16_3 cert_16_3 = true := by decide +kernel
theorem safe_16_3 : ∀ m, compatible p_16_3 m → WeightedBound 151 m := sound 151 _ cert_16_3 (by decide) checked_16_3
def p_16_4 := refine p_16 (4,false) (some ⟨false,false,1⟩)
def cert_16_4 : Tree := (.side 7 15 false (1))
theorem checked_16_4 : check 151 p_16_4 cert_16_4 = true := by decide +kernel
theorem safe_16_4 : ∀ m, compatible p_16_4 m → WeightedBound 151 m := sound 151 _ cert_16_4 (by decide) checked_16_4
def p_16_5 := refine p_16 (4,false) (some ⟨false,true,1⟩)
def cert_16_5 : Tree := (.side 7 15 false (1))
theorem checked_16_5 : check 151 p_16_5 cert_16_5 = true := by decide +kernel
theorem safe_16_5 : ∀ m, compatible p_16_5 m → WeightedBound 151 m := sound 151 _ cert_16_5 (by decide) checked_16_5
def p_16_6 := refine p_16 (4,false) (some ⟨true,false,1⟩)
def cert_16_6 : Tree := (split 18 (2,true) 6 #[
(.side 7 15 false (1)),
(.side 7 23 false (1)),
(.side 7 13 false (1)),
(.side 6 21 false (2)),
(.side 16 4 true (-5)),
(.side 7 21 false (1)),
(.side 14 6 false (-2)),
(.side 6 19 false (2)),
(.side 0 21 false (2)),
(.side 6 21 false (2)),
(.side 18 6 false (-4)),
(.side 2 17 false (2)),
(.side 8 11 false (0)),
(.side 6 31 false (2)),
(.side 8 11 false (0)),
(.side 4 15 false (2)),
(.side 14 5 false (-2)),
(.last 34 (5,true)),
(.side 14 5 false (-2)),
(.side 11 9 false (0)),
(.last 19 (5,true)),
(.side 14 8 false (-2)),
(.last 19 (5,true)),
(.last 21 (5,true))])
theorem checked_16_6 : check 151 p_16_6 cert_16_6 = true := by decide +kernel
theorem safe_16_6 : ∀ m, compatible p_16_6 m → WeightedBound 151 m := sound 151 _ cert_16_6 (by decide) checked_16_6
def p_16_7 := refine p_16 (4,false) (some ⟨true,true,1⟩)
def cert_16_7 : Tree := (.side 1 16 false (2))
theorem checked_16_7 : check 151 p_16_7 cert_16_7 = true := by decide +kernel
theorem safe_16_7 : ∀ m, compatible p_16_7 m → WeightedBound 151 m := sound 151 _ cert_16_7 (by decide) checked_16_7
def p_16_8 := refine p_16 (4,false) (some ⟨false,false,2⟩)
def cert_16_8 : Tree := (.side 0 18 false (2))
theorem checked_16_8 : check 151 p_16_8 cert_16_8 = true := by decide +kernel
theorem safe_16_8 : ∀ m, compatible p_16_8 m → WeightedBound 151 m := sound 151 _ cert_16_8 (by decide) checked_16_8
def p_16_9 := refine p_16 (4,false) (some ⟨false,true,2⟩)
def cert_16_9 : Tree := (.side 0 18 false (2))
theorem checked_16_9 : check 151 p_16_9 cert_16_9 = true := by decide +kernel
theorem safe_16_9 : ∀ m, compatible p_16_9 m → WeightedBound 151 m := sound 151 _ cert_16_9 (by decide) checked_16_9
def p_16_10 := refine p_16 (4,false) (some ⟨true,false,2⟩)
def cert_16_10 : Tree := (split 20 (2,true) 6 #[
(.side 3 18 false (2)),
(.side 4 26 false (2)),
(.side 5 16 false (2)),
(.side 6 24 false (2)),
(.side 7 20 false (1)),
(.side 4 24 false (2)),
(.side 11 10 false (0)),
(.side 6 22 false (2)),
(.side 0 24 false (2)),
(.side 6 24 false (2)),
(.side 17 6 false (-4)),
(.side 6 20 false (2)),
(.side 7 14 false (1)),
(.side 6 24 false (2)),
(.side 7 14 false (1)),
(.side 6 18 false (2)),
(.last 22 (5,true)),
(.side 2 20 false (2)),
(.last 22 (5,true)),
(.last 24 (5,true)),
(.last 21 (5,true)),
(.last 24 (5,true)),
(.last 21 (5,true)),
(.last 23 (5,true))])
theorem checked_16_10 : check 151 p_16_10 cert_16_10 = true := by decide +kernel
theorem safe_16_10 : ∀ m, compatible p_16_10 m → WeightedBound 151 m := sound 151 _ cert_16_10 (by decide) checked_16_10
def p_16_11 := refine p_16 (4,false) (some ⟨true,true,2⟩)
def cert_16_11 : Tree := (.side 7 14 false (1))
theorem checked_16_11 : check 151 p_16_11 cert_16_11 = true := by decide +kernel
theorem safe_16_11 : ∀ m, compatible p_16_11 m → WeightedBound 151 m := sound 151 _ cert_16_11 (by decide) checked_16_11
def p_16_12 := refine p_16 (4,false) (some ⟨false,false,3⟩)
def cert_16_12 : Tree := (.side 7 16 false (1))
theorem checked_16_12 : check 151 p_16_12 cert_16_12 = true := by decide +kernel
theorem safe_16_12 : ∀ m, compatible p_16_12 m → WeightedBound 151 m := sound 151 _ cert_16_12 (by decide) checked_16_12
def p_16_13 := refine p_16 (4,false) (some ⟨false,true,3⟩)
def cert_16_13 : Tree := (split 32 (5,true) 6 #[
(.side 6 34 false (2)),
(.side 0 49 false (2)),
(.side 48 4 true (-2)),
(.side 7 38 false (1)),
(.side 1 32 false (2)),
(.side 7 45 false (1)),
(.last 34 (2,true)),
(.side 7 36 false (1)),
(.side 7 30 false (1)),
(.side 7 38 false (1)),
(.side 7 30 false (1)),
(.side 7 34 false (1)),
(.side 7 28 false (1)),
(.side 48 4 true (-6)),
(.side 7 28 false (1)),
(.side 7 32 false (1)),
(.side 50 4 true (-2)),
(.side 46 4 true (0)),
(.side 7 30 false (1)),
(.side 46 4 true (0)),
(.side 62 4 true (-8)),
(.side 50 4 true (-6)),
(.side 82 4 true (-10)),
(.side 64 4 true (-8))])
theorem checked_16_13 : check 151 p_16_13 cert_16_13 = true := by decide +kernel
theorem safe_16_13 : ∀ m, compatible p_16_13 m → WeightedBound 151 m := sound 151 _ cert_16_13 (by decide) checked_16_13
def p_16_14 := refine p_16 (4,false) (some ⟨true,false,3⟩)
def cert_16_14 : Tree := (.side 9 8 false (0))
theorem checked_16_14 : check 151 p_16_14 cert_16_14 = true := by decide +kernel
theorem safe_16_14 : ∀ m, compatible p_16_14 m → WeightedBound 151 m := sound 151 _ cert_16_14 (by decide) checked_16_14
def p_16_15 := refine p_16 (4,false) (some ⟨true,true,3⟩)
def cert_16_15 : Tree := (.side 7 12 false (1))
theorem checked_16_15 : check 151 p_16_15 cert_16_15 = true := by decide +kernel
theorem safe_16_15 : ∀ m, compatible p_16_15 m → WeightedBound 151 m := sound 151 _ cert_16_15 (by decide) checked_16_15
def p_16_16 := refine p_16 (4,false) (some ⟨false,false,4⟩)
def cert_16_16 : Tree := (.side 16 1 false (-4))
theorem checked_16_16 : check 151 p_16_16 cert_16_16 = true := by decide +kernel
theorem safe_16_16 : ∀ m, compatible p_16_16 m → WeightedBound 151 m := sound 151 _ cert_16_16 (by decide) checked_16_16
def p_16_17 := refine p_16 (4,false) (some ⟨false,true,4⟩)
def cert_16_17 : Tree := (.side 28 1 true (0))
theorem checked_16_17 : check 151 p_16_17 cert_16_17 = true := by decide +kernel
theorem safe_16_17 : ∀ m, compatible p_16_17 m → WeightedBound 151 m := sound 151 _ cert_16_17 (by decide) checked_16_17
def p_16_18 := refine p_16 (4,false) (some ⟨true,false,4⟩)
def cert_16_18 : Tree := (.side 16 1 false (-4))
theorem checked_16_18 : check 151 p_16_18 cert_16_18 = true := by decide +kernel
theorem safe_16_18 : ∀ m, compatible p_16_18 m → WeightedBound 151 m := sound 151 _ cert_16_18 (by decide) checked_16_18
def p_16_19 := refine p_16 (4,false) (some ⟨true,true,4⟩)
def cert_16_19 : Tree := (split 22 (5,true) 6 #[
(.side 6 22 false (2)),
(.side 25 1 true (3)),
(.side 6 20 false (2)),
(.side 25 1 true (3)),
(.side 29 1 true (1)),
(.last 24 (2,true)),
(.last 51 (2,true)),
(.last 24 (2,true)),
(.last 23 (2,true)),
(.last 26 (2,true)),
(.last 23 (2,true)),
(.side 6 24 false (2)),
(.side 6 18 false (2)),
(.side 33 1 true (1)),
(.side 6 18 false (2)),
(.side 6 22 false (2)),
(.side 42 1 true (-6)),
(.side 26 1 true (2)),
(.side 25 3 false (-3)),
(.side 26 1 true (2)),
(.side 46 1 true (-8)),
(.side 29 1 true (1)),
(.side 25 6 false (-3)),
(.side 72 1 true (-8))])
theorem checked_16_19 : check 151 p_16_19 cert_16_19 = true := by decide +kernel
theorem safe_16_19 : ∀ m, compatible p_16_19 m → WeightedBound 151 m := sound 151 _ cert_16_19 (by decide) checked_16_19
def p_16_20 := refine p_16 (4,false) (some ⟨false,false,5⟩)
def cert_16_20 : Tree := (.side 15 2 false (-3))
theorem checked_16_20 : check 151 p_16_20 cert_16_20 = true := by decide +kernel
theorem safe_16_20 : ∀ m, compatible p_16_20 m → WeightedBound 151 m := sound 151 _ cert_16_20 (by decide) checked_16_20
def p_16_21 := refine p_16 (4,false) (some ⟨false,true,5⟩)
def cert_16_21 : Tree := (.side 15 2 true (-4))
theorem checked_16_21 : check 151 p_16_21 cert_16_21 = true := by decide +kernel
theorem safe_16_21 : ∀ m, compatible p_16_21 m → WeightedBound 151 m := sound 151 _ cert_16_21 (by decide) checked_16_21
def p_16_22 := refine p_16 (4,false) (some ⟨true,false,5⟩)
def cert_16_22 : Tree := (.side 15 2 false (-3))
theorem checked_16_22 : check 151 p_16_22 cert_16_22 = true := by decide +kernel
theorem safe_16_22 : ∀ m, compatible p_16_22 m → WeightedBound 151 m := sound 151 _ cert_16_22 (by decide) checked_16_22
def p_16_23 := refine p_16 (4,false) (some ⟨true,true,5⟩)
def cert_16_23 : Tree := (.side 13 4 false (-1))
theorem checked_16_23 : check 151 p_16_23 cert_16_23 = true := by decide +kernel
theorem safe_16_23 : ∀ m, compatible p_16_23 m → WeightedBound 151 m := sound 151 _ cert_16_23 (by decide) checked_16_23
theorem safe_16 : ∀ m, compatible p_16 m → WeightedBound 151 m := by
  apply split_safe 151 p_16 16 (4,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_16_0 | exact safe_16_1 | exact safe_16_2 | exact safe_16_3 | exact safe_16_4 | exact safe_16_5 | exact safe_16_6 | exact safe_16_7 | exact safe_16_8 | exact safe_16_9 | exact safe_16_10 | exact safe_16_11 | exact safe_16_12 | exact safe_16_13 | exact safe_16_14 | exact safe_16_15 | exact safe_16_16 | exact safe_16_17 | exact safe_16_18 | exact safe_16_19 | exact safe_16_20 | exact safe_16_21 | exact safe_16_22 | exact safe_16_23
def p_17 := refine parent (5,false) (some ⟨false,true,4⟩)
def p_17_0 := refine p_17 (4,false) (some ⟨false,false,0⟩)
def cert_17_0 : Tree := (split 17 (2,true) 6 #[
(.side 6 16 false (2)),
(.side 20 18 false (3)),
(.side 6 14 false (2)),
(.side 20 16 false (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 22 false (2)),
(.side 0 50 true (-4)),
(.side 18 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 6 12 false (2)),
(.side 6 16 false (2)),
(.side 6 12 false (2)),
(.side 6 14 false (2)),
(.last 19 (5,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 19 (5,true)),
(.last 19 (5,true)),
(.last 18 (5,true)),
(.last 18 (5,true)),
(.last 18 (5,true)),
(.last 18 (5,true))])
theorem checked_17_0 : check 151 p_17_0 cert_17_0 = true := by decide +kernel
theorem safe_17_0 : ∀ m, compatible p_17_0 m → WeightedBound 151 m := sound 151 _ cert_17_0 (by decide) checked_17_0
def p_17_1 := refine p_17 (4,false) (some ⟨false,true,0⟩)
def cert_17_1 : Tree := (.side 15 11 true (-1))
theorem checked_17_1 : check 151 p_17_1 cert_17_1 = true := by decide +kernel
theorem safe_17_1 : ∀ m, compatible p_17_1 m → WeightedBound 151 m := sound 151 _ cert_17_1 (by decide) checked_17_1
def p_17_2 := refine p_17 (4,false) (some ⟨true,false,0⟩)
def cert_17_2 : Tree := (.side 24 3 true (1))
theorem checked_17_2 : check 151 p_17_2 cert_17_2 = true := by decide +kernel
theorem safe_17_2 : ∀ m, compatible p_17_2 m → WeightedBound 151 m := sound 151 _ cert_17_2 (by decide) checked_17_2
def p_17_3 := refine p_17 (4,false) (some ⟨true,true,0⟩)
def cert_17_3 : Tree := (.side 7 14 false (2))
theorem checked_17_3 : check 151 p_17_3 cert_17_3 = true := by decide +kernel
theorem safe_17_3 : ∀ m, compatible p_17_3 m → WeightedBound 151 m := sound 151 _ cert_17_3 (by decide) checked_17_3
def p_17_4 := refine p_17 (4,false) (some ⟨false,false,1⟩)
def cert_17_4 : Tree := (.side 1 14 false (2))
theorem checked_17_4 : check 151 p_17_4 cert_17_4 = true := by decide +kernel
theorem safe_17_4 : ∀ m, compatible p_17_4 m → WeightedBound 151 m := sound 151 _ cert_17_4 (by decide) checked_17_4
def p_17_5 := refine p_17 (4,false) (some ⟨false,true,1⟩)
def cert_17_5 : Tree := (.side 18 15 true (1))
theorem checked_17_5 : check 151 p_17_5 cert_17_5 = true := by decide +kernel
theorem safe_17_5 : ∀ m, compatible p_17_5 m → WeightedBound 151 m := sound 151 _ cert_17_5 (by decide) checked_17_5
def p_17_6 := refine p_17 (4,false) (some ⟨true,false,1⟩)
def cert_17_6 : Tree := (split 16 (2,true) 6 #[
(.side 3 14 false (2)),
(.side 4 16 false (2)),
(.side 5 12 false (2)),
(.side 6 14 false (2)),
(.side 14 4 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 11 6 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 20 false (2)),
(.side 0 20 true (-2)),
(.side 15 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 10 false (1)),
(.side 4 14 false (2)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.last 18 (5,true)),
(.side 24 3 true (1)),
(.last 18 (5,true)),
(.last 18 (5,true)),
(.last 17 (5,true)),
(.last 17 (5,true)),
(.last 17 (5,true)),
(.last 17 (5,true))])
theorem checked_17_6 : check 151 p_17_6 cert_17_6 = true := by decide +kernel
theorem safe_17_6 : ∀ m, compatible p_17_6 m → WeightedBound 151 m := sound 151 _ cert_17_6 (by decide) checked_17_6
def p_17_7 := refine p_17 (4,false) (some ⟨true,true,1⟩)
def cert_17_7 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_17_7 : check 151 p_17_7 cert_17_7 = true := by decide +kernel
theorem safe_17_7 : ∀ m, compatible p_17_7 m → WeightedBound 151 m := sound 151 _ cert_17_7 (by decide) checked_17_7
def p_17_8 := refine p_17 (4,false) (some ⟨false,false,2⟩)
def cert_17_8 : Tree := (.side 7 12 false (1))
theorem checked_17_8 : check 151 p_17_8 cert_17_8 = true := by decide +kernel
theorem safe_17_8 : ∀ m, compatible p_17_8 m → WeightedBound 151 m := sound 151 _ cert_17_8 (by decide) checked_17_8
def p_17_9 := refine p_17 (4,false) (some ⟨false,true,2⟩)
def cert_17_9 : Tree := (split 15 (2,true) 6 #[
(.side 7 20 false (2)),
(.side 0 28 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 3 13 true (-2)),
(.side 7 18 false (1)),
(.side 0 19 true (-2)),
(.side 0 30 true (-2)),
(.side 1 43 true (-2)),
(.side 6 18 false (2)),
(.side 0 18 true (-2)),
(.side 20 6 false (0)),
(.side 2 15 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 16 11 true (-1)),
(.last 22 (5,true)),
(.side 0 20 true (-2)),
(.side 14 2 true (0)),
(.last 17 (5,true)),
(.side 0 22 true (-2)),
(.last 16 (5,true)),
(.side 0 26 true (-2)),
(.last 16 (5,true))])
theorem checked_17_9 : check 151 p_17_9 cert_17_9 = true := by decide +kernel
theorem safe_17_9 : ∀ m, compatible p_17_9 m → WeightedBound 151 m := sound 151 _ cert_17_9 (by decide) checked_17_9
def p_17_10 := refine p_17 (4,false) (some ⟨true,false,2⟩)
def cert_17_10 : Tree := (.side 7 12 false (1))
theorem checked_17_10 : check 151 p_17_10 cert_17_10 = true := by decide +kernel
theorem safe_17_10 : ∀ m, compatible p_17_10 m → WeightedBound 151 m := sound 151 _ cert_17_10 (by decide) checked_17_10
def p_17_11 := refine p_17 (4,false) (some ⟨true,true,2⟩)
def cert_17_11 : Tree := (split 15 (2,true) 6 #[
(.side 7 16 false (1)),
(.side 18 18 false (3)),
(.side 7 14 false (1)),
(.side 18 16 false (3)),
(.side 17 15 true (0)),
(.side 69 45 true (2)),
(.side 16 17 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 14 false (1)),
(.side 0 48 true (-4)),
(.side 7 14 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 12 false (1)),
(.side 7 16 false (2)),
(.side 7 12 false (1)),
(.side 7 14 false (2)),
(.side 7 20 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 12 4 true (-1)),
(.last 17 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true))])
theorem checked_17_11 : check 151 p_17_11 cert_17_11 = true := by decide +kernel
theorem safe_17_11 : ∀ m, compatible p_17_11 m → WeightedBound 151 m := sound 151 _ cert_17_11 (by decide) checked_17_11
def p_17_12 := refine p_17 (4,false) (some ⟨false,false,3⟩)
def cert_17_12 : Tree := (.side 7 10 false (1))
theorem checked_17_12 : check 151 p_17_12 cert_17_12 = true := by decide +kernel
theorem safe_17_12 : ∀ m, compatible p_17_12 m → WeightedBound 151 m := sound 151 _ cert_17_12 (by decide) checked_17_12
def p_17_13 := refine p_17 (4,false) (some ⟨false,true,3⟩)
def cert_17_13 : Tree := (.side 28 4 true (2))
theorem checked_17_13 : check 151 p_17_13 cert_17_13 = true := by decide +kernel
theorem safe_17_13 : ∀ m, compatible p_17_13 m → WeightedBound 151 m := sound 151 _ cert_17_13 (by decide) checked_17_13
def p_17_14 := refine p_17 (4,false) (some ⟨true,false,3⟩)
def cert_17_14 : Tree := (.side 7 10 false (1))
theorem checked_17_14 : check 151 p_17_14 cert_17_14 = true := by decide +kernel
theorem safe_17_14 : ∀ m, compatible p_17_14 m → WeightedBound 151 m := sound 151 _ cert_17_14 (by decide) checked_17_14
def p_17_15 := refine p_17 (4,false) (some ⟨true,true,3⟩)
def cert_17_15 : Tree := (.side 7 12 false (1))
theorem checked_17_15 : check 151 p_17_15 cert_17_15 = true := by decide +kernel
theorem safe_17_15 : ∀ m, compatible p_17_15 m → WeightedBound 151 m := sound 151 _ cert_17_15 (by decide) checked_17_15
def p_17_16 := refine p_17 (4,false) (some ⟨false,false,4⟩)
def cert_17_16 : Tree := (.side 18 1 false (-2))
theorem checked_17_16 : check 151 p_17_16 cert_17_16 = true := by decide +kernel
theorem safe_17_16 : ∀ m, compatible p_17_16 m → WeightedBound 151 m := sound 151 _ cert_17_16 (by decide) checked_17_16
def p_17_17 := refine p_17 (4,false) (some ⟨false,true,4⟩)
def cert_17_17 : Tree := (.side 20 1 true (2))
theorem checked_17_17 : check 151 p_17_17 cert_17_17 = true := by decide +kernel
theorem safe_17_17 : ∀ m, compatible p_17_17 m → WeightedBound 151 m := sound 151 _ cert_17_17 (by decide) checked_17_17
def p_17_18 := refine p_17 (4,false) (some ⟨true,false,4⟩)
def cert_17_18 : Tree := (.side 18 1 false (-2))
theorem checked_17_18 : check 151 p_17_18 cert_17_18 = true := by decide +kernel
theorem safe_17_18 : ∀ m, compatible p_17_18 m → WeightedBound 151 m := sound 151 _ cert_17_18 (by decide) checked_17_18
def p_17_19 := refine p_17 (4,false) (some ⟨true,true,4⟩)
def cert_17_19 : Tree := (split 16 (5,true) 6 #[
(.side 6 18 false (2)),
(.side 19 1 true (3)),
(.side 24 1 true (2)),
(.side 19 1 true (3)),
(.side 1 16 false (2)),
(.last 18 (2,true)),
(.last 18 (2,true)),
(.last 18 (2,true)),
(.side 7 14 false (1)),
(.last 20 (2,true)),
(.side 7 14 false (1)),
(.side 7 18 false (1)),
(.side 7 12 false (1)),
(.side 22 1 true (2)),
(.side 7 12 false (1)),
(.side 7 16 false (1)),
(.side 26 1 true (-2)),
(.side 20 1 true (2)),
(.side 22 3 false (-1)),
(.side 20 1 true (2)),
(.side 24 1 true (0)),
(.side 20 1 true (2)),
(.side 34 1 true (0)),
(.side 20 1 true (2))])
theorem checked_17_19 : check 151 p_17_19 cert_17_19 = true := by decide +kernel
theorem safe_17_19 : ∀ m, compatible p_17_19 m → WeightedBound 151 m := sound 151 _ cert_17_19 (by decide) checked_17_19
def p_17_20 := refine p_17 (4,false) (some ⟨false,false,5⟩)
def cert_17_20 : Tree := (.side 13 2 true (-1))
theorem checked_17_20 : check 151 p_17_20 cert_17_20 = true := by decide +kernel
theorem safe_17_20 : ∀ m, compatible p_17_20 m → WeightedBound 151 m := sound 151 _ cert_17_20 (by decide) checked_17_20
def p_17_21 := refine p_17 (4,false) (some ⟨false,true,5⟩)
def cert_17_21 : Tree := (split 15 (5,true) 6 #[
(.last 18 (2,true)),
(.side 0 28 true (-2)),
(.side 19 2 true (1)),
(.side 3 13 true (-2)),
(.side 7 18 false (1)),
(.side 17 2 true (3)),
(.last 17 (2,true)),
(.side 17 2 true (3)),
(.side 6 18 false (2)),
(.last 16 (2,true)),
(.last 19 (2,true)),
(.last 16 (2,true)),
(.side 24 2 true (2)),
(.side 21 2 true (1)),
(.side 27 2 true (1)),
(.side 16 11 true (-1)),
(.side 19 2 true (1)),
(.side 17 2 true (1)),
(.side 14 2 true (0)),
(.side 18 2 true (2)),
(.side 19 2 true (1)),
(.side 17 2 true (3)),
(.side 23 2 true (1)),
(.side 17 2 true (3))])
theorem checked_17_21 : check 151 p_17_21 cert_17_21 = true := by decide +kernel
theorem safe_17_21 : ∀ m, compatible p_17_21 m → WeightedBound 151 m := sound 151 _ cert_17_21 (by decide) checked_17_21
def p_17_22 := refine p_17 (4,false) (some ⟨true,false,5⟩)
def cert_17_22 : Tree := (.side 12 4 true (-1))
theorem checked_17_22 : check 151 p_17_22 cert_17_22 = true := by decide +kernel
theorem safe_17_22 : ∀ m, compatible p_17_22 m → WeightedBound 151 m := sound 151 _ cert_17_22 (by decide) checked_17_22
def p_17_23 := refine p_17 (4,false) (some ⟨true,true,5⟩)
def cert_17_23 : Tree := (split 15 (5,true) 6 #[
(.side 7 16 false (1)),
(.side 18 18 false (3)),
(.side 7 14 false (1)),
(.side 18 16 false (3)),
(.side 20 2 true (2)),
(.side 17 2 true (3)),
(.side 23 2 true (1)),
(.side 17 2 true (3)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.side 7 12 false (1)),
(.side 7 16 false (2)),
(.side 7 12 false (1)),
(.side 7 14 false (2)),
(.side 21 2 true (1)),
(.side 17 2 true (1)),
(.side 12 4 true (-1)),
(.side 18 2 true (2)),
(.side 21 2 true (1)),
(.side 17 2 true (3)),
(.side 12 6 true (-1)),
(.side 17 2 true (3))])
theorem checked_17_23 : check 151 p_17_23 cert_17_23 = true := by decide +kernel
theorem safe_17_23 : ∀ m, compatible p_17_23 m → WeightedBound 151 m := sound 151 _ cert_17_23 (by decide) checked_17_23
theorem safe_17 : ∀ m, compatible p_17 m → WeightedBound 151 m := by
  apply split_safe 151 p_17 14 (4,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_17_0 | exact safe_17_1 | exact safe_17_2 | exact safe_17_3 | exact safe_17_4 | exact safe_17_5 | exact safe_17_6 | exact safe_17_7 | exact safe_17_8 | exact safe_17_9 | exact safe_17_10 | exact safe_17_11 | exact safe_17_12 | exact safe_17_13 | exact safe_17_14 | exact safe_17_15 | exact safe_17_16 | exact safe_17_17 | exact safe_17_18 | exact safe_17_19 | exact safe_17_20 | exact safe_17_21 | exact safe_17_22 | exact safe_17_23
def p_18 := refine parent (5,false) (some ⟨true,false,4⟩)
def p_18_0 := refine p_18 (4,false) (some ⟨false,false,0⟩)
def cert_18_0 : Tree := (split 19 (2,true) 6 #[
(.side 3 17 false (2)),
(.side 28 31 false (3)),
(.side 5 15 false (2)),
(.side 28 27 false (3)),
(.side 6 23 false (2)),
(.side 35 33 false (1)),
(.side 11 9 false (0)),
(.last 61 (5,true)),
(.side 0 23 false (2)),
(.last 132 (5,true)),
(.side 17 6 false (-3)),
(.side 6 19 false (2)),
(.side 7 13 false (1)),
(.last 26 (5,true)),
(.side 7 13 false (1)),
(.side 6 17 false (2)),
(.last 21 (5,true)),
(.last 31 (5,true)),
(.last 21 (5,true)),
(.side 6 19 false (2)),
(.last 20 (5,true)),
(.side 3 19 false (2)),
(.last 20 (5,true)),
(.last 22 (5,true))])
theorem checked_18_0 : check 151 p_18_0 cert_18_0 = true := by decide +kernel
theorem safe_18_0 : ∀ m, compatible p_18_0 m → WeightedBound 151 m := sound 151 _ cert_18_0 (by decide) checked_18_0
def p_18_1 := refine p_18 (4,false) (some ⟨false,true,0⟩)
def cert_18_1 : Tree := (.side 7 13 false (1))
theorem checked_18_1 : check 151 p_18_1 cert_18_1 = true := by decide +kernel
theorem safe_18_1 : ∀ m, compatible p_18_1 m → WeightedBound 151 m := sound 151 _ cert_18_1 (by decide) checked_18_1
def p_18_2 := refine p_18 (4,false) (some ⟨true,false,0⟩)
def cert_18_2 : Tree := (.side 10 7 false (0))
theorem checked_18_2 : check 151 p_18_2 cert_18_2 = true := by decide +kernel
theorem safe_18_2 : ∀ m, compatible p_18_2 m → WeightedBound 151 m := sound 151 _ cert_18_2 (by decide) checked_18_2
def p_18_3 := refine p_18 (4,false) (some ⟨true,true,0⟩)
def cert_18_3 : Tree := (.side 3 14 false (2))
theorem checked_18_3 : check 151 p_18_3 cert_18_3 = true := by decide +kernel
theorem safe_18_3 : ∀ m, compatible p_18_3 m → WeightedBound 151 m := sound 151 _ cert_18_3 (by decide) checked_18_3
def p_18_4 := refine p_18 (4,false) (some ⟨false,false,1⟩)
def cert_18_4 : Tree := (.side 7 15 false (1))
theorem checked_18_4 : check 151 p_18_4 cert_18_4 = true := by decide +kernel
theorem safe_18_4 : ∀ m, compatible p_18_4 m → WeightedBound 151 m := sound 151 _ cert_18_4 (by decide) checked_18_4
def p_18_5 := refine p_18 (4,false) (some ⟨false,true,1⟩)
def cert_18_5 : Tree := (.side 24 21 true (-1))
theorem checked_18_5 : check 151 p_18_5 cert_18_5 = true := by decide +kernel
theorem safe_18_5 : ∀ m, compatible p_18_5 m → WeightedBound 151 m := sound 151 _ cert_18_5 (by decide) checked_18_5
def p_18_6 := refine p_18 (4,false) (some ⟨true,false,1⟩)
def cert_18_6 : Tree := (split 18 (2,true) 6 #[
(.side 7 15 false (1)),
(.side 7 19 false (1)),
(.side 7 13 false (1)),
(.side 6 17 false (2)),
(.side 16 4 true (-5)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,6),(false,2)],[(true,6),(true,2)],[(false,3),(false,5)],[]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch .leaf .leaf) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .leaf) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 14 6 false (-2)),
(.last 31 (5,true)),
(.side 0 21 false (2)),
(.last 136 (5,true)),
(.side 18 6 false (-4)),
(.side 6 19 false (2)),
(.side 8 11 false (0)),
(.side 7 15 false (1)),
(.side 8 11 false (0)),
(.side 6 13 false (2)),
(.side 14 5 false (-2)),
(.side 12 7 false (0)),
(.side 14 5 false (-2)),
(.last 20 (5,true)),
(.last 19 (5,true)),
(.last 19 (5,true)),
(.last 19 (5,true)),
(.last 19 (5,true))])
theorem checked_18_6 : check 151 p_18_6 cert_18_6 = true := by decide +kernel
theorem safe_18_6 : ∀ m, compatible p_18_6 m → WeightedBound 151 m := sound 151 _ cert_18_6 (by decide) checked_18_6
def p_18_7 := refine p_18 (4,false) (some ⟨true,true,1⟩)
def cert_18_7 : Tree := (.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2),(true,6)],[(false,3),(false,7),(false,5)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .leaf (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))) .empty),.empty]⟩)
theorem checked_18_7 : check 151 p_18_7 cert_18_7 = true := by decide +kernel
theorem safe_18_7 : ∀ m, compatible p_18_7 m → WeightedBound 151 m := sound 151 _ cert_18_7 (by decide) checked_18_7
def p_18_8 := refine p_18 (4,false) (some ⟨false,false,2⟩)
def cert_18_8 : Tree := (.side 0 18 false (2))
theorem checked_18_8 : check 151 p_18_8 cert_18_8 = true := by decide +kernel
theorem safe_18_8 : ∀ m, compatible p_18_8 m → WeightedBound 151 m := sound 151 _ cert_18_8 (by decide) checked_18_8
def p_18_9 := refine p_18 (4,false) (some ⟨false,true,2⟩)
def cert_18_9 : Tree := (split 17 (2,true) 6 #[
(.side 0 18 false (2)),
(.side 10 64 true (-4)),
(.automata ⟨⟨#[[(false,0)],[(false,0)],[(true,0),(true,3)],[(false,2)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) .empty),.empty]⟩),
(.last 34 (5,true)),
(.side 7 16 false (1)),
(.last 40 (5,true)),
(.side 14 7 false (-2)),
(.last 59 (5,true)),
(.side 0 19 false (2)),
(.last 120 (5,true)),
(.side 17 6 false (-3)),
(.side 7 15 false (1)),
(.side 7 23 false (1)),
(.side 9 9 false (0)),
(.side 9 9 false (0)),
(.side 7 13 false (1)),
(.side 0 20 false (2)),
(.side 0 28 true (-4)),
(.side 16 2 true (-4)),
(.last 23 (5,true)),
(.side 15 3 false (-3)),
(.last 21 (5,true)),
(.side 15 3 false (-3)),
(.side 13 5 false (-1))])
theorem checked_18_9 : check 151 p_18_9 cert_18_9 = true := by decide +kernel
theorem safe_18_9 : ∀ m, compatible p_18_9 m → WeightedBound 151 m := sound 151 _ cert_18_9 (by decide) checked_18_9
def p_18_10 := refine p_18 (4,false) (some ⟨true,false,2⟩)
def cert_18_10 : Tree := (split 20 (2,true) 6 #[
(.side 3 18 false (2)),
(.side 4 22 false (2)),
(.side 5 16 false (2)),
(.side 6 20 false (2)),
(.side 7 20 false (1)),
(.side 6 82 false (2)),
(.side 11 10 false (0)),
(.side 6 22 false (2)),
(.side 0 24 false (2)),
(.last 145 (5,true)),
(.side 17 6 false (-4)),
(.side 6 22 false (2)),
(.side 7 14 false (1)),
(.side 4 18 false (2)),
(.side 7 14 false (1)),
(.side 6 16 false (2)),
(.last 22 (5,true)),
(.last 24 (5,true)),
(.last 22 (5,true)),
(.last 22 (5,true)),
(.last 21 (5,true)),
(.last 21 (5,true)),
(.last 21 (5,true)),
(.last 21 (5,true))])
theorem checked_18_10 : check 151 p_18_10 cert_18_10 = true := by decide +kernel
theorem safe_18_10 : ∀ m, compatible p_18_10 m → WeightedBound 151 m := sound 151 _ cert_18_10 (by decide) checked_18_10
def p_18_11 := refine p_18 (4,false) (some ⟨true,true,2⟩)
def cert_18_11 : Tree := (split 17 (2,true) 6 #[
(.side 7 14 false (1)),
(.side 24 28 false (3)),
(.side 7 12 false (1)),
(.side 24 24 false (3)),
(.side 7 17 false (1)),
(.last 36 (5,true)),
(.side 14 5 false (-2)),
(.last 56 (5,true)),
(.side 0 20 false (2)),
(.last 123 (5,true)),
(.side 17 6 false (-3)),
(.side 2 16 false (2)),
(.side 8 10 false (0)),
(.last 24 (5,true)),
(.side 8 10 false (0)),
(.side 4 14 false (2)),
(.side 14 4 false (-2)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch .leaf (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) .empty),.empty]⟩),
(.side 14 4 false (-2)),
(.last 23 (5,true)),
(.last 18 (5,true)),
(.last 21 (5,true)),
(.last 18 (5,true)),
(.last 20 (5,true))])
theorem checked_18_11 : check 151 p_18_11 cert_18_11 = true := by decide +kernel
theorem safe_18_11 : ∀ m, compatible p_18_11 m → WeightedBound 151 m := sound 151 _ cert_18_11 (by decide) checked_18_11
def p_18_12 := refine p_18 (4,false) (some ⟨false,false,3⟩)
def cert_18_12 : Tree := (.side 7 16 false (1))
theorem checked_18_12 : check 151 p_18_12 cert_18_12 = true := by decide +kernel
theorem safe_18_12 : ∀ m, compatible p_18_12 m → WeightedBound 151 m := sound 151 _ cert_18_12 (by decide) checked_18_12
def p_18_13 := refine p_18 (4,false) (some ⟨false,true,3⟩)
def cert_18_13 : Tree := (.side 8 9 false (0))
theorem checked_18_13 : check 151 p_18_13 cert_18_13 = true := by decide +kernel
theorem safe_18_13 : ∀ m, compatible p_18_13 m → WeightedBound 151 m := sound 151 _ cert_18_13 (by decide) checked_18_13
def p_18_14 := refine p_18 (4,false) (some ⟨true,false,3⟩)
def cert_18_14 : Tree := (.side 9 8 false (0))
theorem checked_18_14 : check 151 p_18_14 cert_18_14 = true := by decide +kernel
theorem safe_18_14 : ∀ m, compatible p_18_14 m → WeightedBound 151 m := sound 151 _ cert_18_14 (by decide) checked_18_14
def p_18_15 := refine p_18 (4,false) (some ⟨true,true,3⟩)
def cert_18_15 : Tree := (.side 7 10 false (1))
theorem checked_18_15 : check 151 p_18_15 cert_18_15 = true := by decide +kernel
theorem safe_18_15 : ∀ m, compatible p_18_15 m → WeightedBound 151 m := sound 151 _ cert_18_15 (by decide) checked_18_15
def p_18_16 := refine p_18 (4,false) (some ⟨false,false,4⟩)
def cert_18_16 : Tree := (.side 16 1 false (-4))
theorem checked_18_16 : check 151 p_18_16 cert_18_16 = true := by decide +kernel
theorem safe_18_16 : ∀ m, compatible p_18_16 m → WeightedBound 151 m := sound 151 _ cert_18_16 (by decide) checked_18_16
def p_18_17 := refine p_18 (4,false) (some ⟨false,true,4⟩)
def cert_18_17 : Tree := (.side 14 3 false (-2))
theorem checked_18_17 : check 151 p_18_17 cert_18_17 = true := by decide +kernel
theorem safe_18_17 : ∀ m, compatible p_18_17 m → WeightedBound 151 m := sound 151 _ cert_18_17 (by decide) checked_18_17
def p_18_18 := refine p_18 (4,false) (some ⟨true,false,4⟩)
def cert_18_18 : Tree := (.side 16 1 false (-4))
theorem checked_18_18 : check 151 p_18_18 cert_18_18 = true := by decide +kernel
theorem safe_18_18 : ∀ m, compatible p_18_18 m → WeightedBound 151 m := sound 151 _ cert_18_18 (by decide) checked_18_18
def p_18_19 := refine p_18 (4,false) (some ⟨true,true,4⟩)
def cert_18_19 : Tree := (split 18 (5,true) 6 #[
(.side 0 19 false (2)),
(.last 21 (2,true)),
(.side 7 23 false (1)),
(.last 21 (2,true)),
(.side 7 17 false (1)),
(.side 7 17 false (1)),
(.last 20 (2,true)),
(.side 1 18 false (2)),
(.side 0 20 false (2)),
(.side 0 20 false (2)),
(.last 22 (2,true)),
(.side 7 16 false (1)),
(.side 7 24 false (1)),
(.side 66 1 true (2)),
(.side 9 10 false (0)),
(.side 7 14 false (1)),
(.side 74 1 true (-10)),
(.side 30 1 true (2)),
(.side 16 3 false (-3)),
(.side 30 1 true (2)),
(.side 15 4 false (-3)),
(.side 15 4 true (-4)),
(.side 15 4 false (-3)),
(.side 13 6 false (-1))])
theorem checked_18_19 : check 151 p_18_19 cert_18_19 = true := by decide +kernel
theorem safe_18_19 : ∀ m, compatible p_18_19 m → WeightedBound 151 m := sound 151 _ cert_18_19 (by decide) checked_18_19
def p_18_20 := refine p_18 (4,false) (some ⟨false,false,5⟩)
def cert_18_20 : Tree := (.side 15 2 false (-3))
theorem checked_18_20 : check 151 p_18_20 cert_18_20 = true := by decide +kernel
theorem safe_18_20 : ∀ m, compatible p_18_20 m → WeightedBound 151 m := sound 151 _ cert_18_20 (by decide) checked_18_20
def p_18_21 := refine p_18 (4,false) (some ⟨false,true,5⟩)
def cert_18_21 : Tree := (split 17 (5,true) 6 #[
(.side 0 18 false (2)),
(.side 40 38 true (0)),
(.side 48 6 true (0)),
(.side 17 17 true (-3)),
(.side 7 16 false (1)),
(.last 19 (2,true)),
(.last 19 (2,true)),
(.last 19 (2,true)),
(.side 0 19 false (2)),
(.last 21 (2,true)),
(.last 21 (2,true)),
(.side 7 15 false (1)),
(.side 45 7 true (0)),
(.side 9 9 false (0)),
(.side 9 9 false (0)),
(.side 7 13 false (1)),
(.side 15 4 true (-4)),
(.side 23 4 true (0)),
(.side 16 2 true (-4)),
(.side 23 4 true (1)),
(.side 15 3 false (-3)),
(.side 26 3 true (2)),
(.side 15 3 false (-3)),
(.side 13 5 false (-1))])
theorem checked_18_21 : check 151 p_18_21 cert_18_21 = true := by decide +kernel
theorem safe_18_21 : ∀ m, compatible p_18_21 m → WeightedBound 151 m := sound 151 _ cert_18_21 (by decide) checked_18_21
def p_18_22 := refine p_18 (4,false) (some ⟨true,false,5⟩)
def cert_18_22 : Tree := (.side 15 2 false (-3))
theorem checked_18_22 : check 151 p_18_22 cert_18_22 = true := by decide +kernel
theorem safe_18_22 : ∀ m, compatible p_18_22 m → WeightedBound 151 m := sound 151 _ cert_18_22 (by decide) checked_18_22
def p_18_23 := refine p_18 (4,false) (some ⟨true,true,5⟩)
def cert_18_23 : Tree := (split 17 (5,true) 6 #[
(.side 7 14 false (1)),
(.side 24 28 false (3)),
(.side 7 12 false (1)),
(.side 24 24 false (3)),
(.side 13 7 false (-1)),
(.last 19 (2,true)),
(.side 14 5 false (-2)),
(.last 19 (2,true)),
(.last 18 (2,true)),
(.last 21 (2,true)),
(.last 18 (2,true)),
(.side 2 16 false (2)),
(.side 8 10 false (0)),
(.side 9 16 false (0)),
(.side 8 10 false (0)),
(.side 4 14 false (2)),
(.side 14 4 false (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 14 4 false (-2)),
(.side 23 6 true (1)),
(.side 15 4 false (-3)),
(.side 26 3 true (2)),
(.side 15 4 false (-3)),
(.side 13 8 false (-1))])
theorem checked_18_23 : check 151 p_18_23 cert_18_23 = true := by decide +kernel
theorem safe_18_23 : ∀ m, compatible p_18_23 m → WeightedBound 151 m := sound 151 _ cert_18_23 (by decide) checked_18_23
theorem safe_18 : ∀ m, compatible p_18 m → WeightedBound 151 m := by
  apply split_safe 151 p_18 16 (4,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_18_0 | exact safe_18_1 | exact safe_18_2 | exact safe_18_3 | exact safe_18_4 | exact safe_18_5 | exact safe_18_6 | exact safe_18_7 | exact safe_18_8 | exact safe_18_9 | exact safe_18_10 | exact safe_18_11 | exact safe_18_12 | exact safe_18_13 | exact safe_18_14 | exact safe_18_15 | exact safe_18_16 | exact safe_18_17 | exact safe_18_18 | exact safe_18_19 | exact safe_18_20 | exact safe_18_21 | exact safe_18_22 | exact safe_18_23
def p_19 := refine parent (5,false) (some ⟨true,true,4⟩)
def p_19_0 := refine p_19 (4,false) (some ⟨false,false,0⟩)
def cert_19_0 : Tree := (.side 3 12 false (2))
theorem checked_19_0 : check 151 p_19_0 cert_19_0 = true := by decide +kernel
theorem safe_19_0 : ∀ m, compatible p_19_0 m → WeightedBound 151 m := sound 151 _ cert_19_0 (by decide) checked_19_0
def p_19_1 := refine p_19 (4,false) (some ⟨false,true,0⟩)
def cert_19_1 : Tree := (.side 4 14 false (2))
theorem checked_19_1 : check 151 p_19_1 cert_19_1 = true := by decide +kernel
theorem safe_19_1 : ∀ m, compatible p_19_1 m → WeightedBound 151 m := sound 151 _ cert_19_1 (by decide) checked_19_1
def p_19_2 := refine p_19 (4,false) (some ⟨true,false,0⟩)
def cert_19_2 : Tree := (.side 5 10 false (2))
theorem checked_19_2 : check 151 p_19_2 cert_19_2 = true := by decide +kernel
theorem safe_19_2 : ∀ m, compatible p_19_2 m → WeightedBound 151 m := sound 151 _ cert_19_2 (by decide) checked_19_2
def p_19_3 := refine p_19 (4,false) (some ⟨true,true,0⟩)
def cert_19_3 : Tree := (.side 6 12 false (2))
theorem checked_19_3 : check 151 p_19_3 cert_19_3 = true := by decide +kernel
theorem safe_19_3 : ∀ m, compatible p_19_3 m → WeightedBound 151 m := sound 151 _ cert_19_3 (by decide) checked_19_3
def p_19_4 := refine p_19 (4,false) (some ⟨false,false,1⟩)
def cert_19_4 : Tree := (.side 1 16 false (2))
theorem checked_19_4 : check 151 p_19_4 cert_19_4 = true := by decide +kernel
theorem safe_19_4 : ∀ m, compatible p_19_4 m → WeightedBound 151 m := sound 151 _ cert_19_4 (by decide) checked_19_4
def p_19_5 := refine p_19 (4,false) (some ⟨false,true,1⟩)
def cert_19_5 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_19_5 : check 151 p_19_5 cert_19_5 = true := by decide +kernel
theorem safe_19_5 : ∀ m, compatible p_19_5 m → WeightedBound 151 m := sound 151 _ cert_19_5 (by decide) checked_19_5
def p_19_6 := refine p_19 (4,false) (some ⟨true,false,1⟩)
def cert_19_6 : Tree := (.side 11 4 true (-1))
theorem checked_19_6 : check 151 p_19_6 cert_19_6 = true := by decide +kernel
theorem safe_19_6 : ∀ m, compatible p_19_6 m → WeightedBound 151 m := sound 151 _ cert_19_6 (by decide) checked_19_6
def p_19_7 := refine p_19 (4,false) (some ⟨true,true,1⟩)
def cert_19_7 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩)
theorem checked_19_7 : check 151 p_19_7 cert_19_7 = true := by decide +kernel
theorem safe_19_7 : ∀ m, compatible p_19_7 m → WeightedBound 151 m := sound 151 _ cert_19_7 (by decide) checked_19_7
def p_19_8 := refine p_19 (4,false) (some ⟨false,false,2⟩)
def cert_19_8 : Tree := (split 15 (2,true) 6 #[
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 19 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 15 7 false (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 18 false (2)),
(.side 0 54 true (-4)),
(.side 15 6 false (-1)),
(.side 2 14 false (2)),
(.side 8 8 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 8 8 false (0)),
(.side 4 12 false (2)),
(.side 0 22 false (2)),
(.side 7 14 false (1)),
(.side 0 22 false (2)),
(.side 14 2 true (-1)),
(.last 16 (5,true)),
(.last 18 (5,true)),
(.last 16 (5,true)),
(.last 18 (5,true))])
theorem checked_19_8 : check 151 p_19_8 cert_19_8 = true := by decide +kernel
theorem safe_19_8 : ∀ m, compatible p_19_8 m → WeightedBound 151 m := sound 151 _ cert_19_8 (by decide) checked_19_8
def p_19_9 := refine p_19 (4,false) (some ⟨false,true,2⟩)
def cert_19_9 : Tree := (split 15 (2,true) 6 #[
(.side 6 18 false (2)),
(.side 0 28 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 18 16 false (3)),
(.side 6 16 false (2)),
(.side 0 19 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 2 14 false (2)),
(.side 0 18 true (-2)),
(.side 2 14 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 4 12 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 4 12 false (2)),
(.side 4 14 false (2)),
(.last 22 (5,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 14 2 true (0)),
(.last 17 (5,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 16 (5,true)),
(.last 18 (5,true)),
(.last 16 (5,true))])
theorem checked_19_9 : check 151 p_19_9 cert_19_9 = true := by decide +kernel
theorem safe_19_9 : ∀ m, compatible p_19_9 m → WeightedBound 151 m := sound 151 _ cert_19_9 (by decide) checked_19_9
def p_19_10 := refine p_19 (4,false) (some ⟨true,false,2⟩)
def cert_19_10 : Tree := (split 15 (2,true) 6 #[
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.side 7 21 false (1)),
(.side 11 45 true (-1)),
(.side 15 7 false (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) .leaf),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 18 false (2)),
(.side 0 20 true (-2)),
(.side 15 6 false (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 8 8 false (0)),
(.side 7 12 false (1)),
(.side 8 8 false (0)),
(.side 6 10 false (2)),
(.last 26 (5,true)),
(.side 12 4 true (-1)),
(.last 26 (5,true)),
(.last 17 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true))])
theorem checked_19_10 : check 151 p_19_10 cert_19_10 = true := by decide +kernel
theorem safe_19_10 : ∀ m, compatible p_19_10 m → WeightedBound 151 m := sound 151 _ cert_19_10 (by decide) checked_19_10
def p_19_11 := refine p_19 (4,false) (some ⟨true,true,2⟩)
def cert_19_11 : Tree := (split 15 (2,true) 6 #[
(.side 6 14 false (2)),
(.side 18 16 false (3)),
(.side 6 12 false (2)),
(.side 18 14 false (3)),
(.side 60 44 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 0 20 false (2)),
(.side 0 46 true (-4)),
(.side 16 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.side 6 10 false (2)),
(.side 6 14 false (2)),
(.side 6 10 false (2)),
(.side 6 12 false (2)),
(.last 17 (5,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),.empty]⟩),
(.last 17 (5,true)),
(.last 17 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true)),
(.last 16 (5,true))])
theorem checked_19_11 : check 151 p_19_11 cert_19_11 = true := by decide +kernel
theorem safe_19_11 : ∀ m, compatible p_19_11 m → WeightedBound 151 m := sound 151 _ cert_19_11 (by decide) checked_19_11
def p_19_12 := refine p_19 (4,false) (some ⟨false,false,3⟩)
def cert_19_12 : Tree := (.side 7 8 false (1))
theorem checked_19_12 : check 151 p_19_12 cert_19_12 = true := by decide +kernel
theorem safe_19_12 : ∀ m, compatible p_19_12 m → WeightedBound 151 m := sound 151 _ cert_19_12 (by decide) checked_19_12
def p_19_13 := refine p_19 (4,false) (some ⟨false,true,3⟩)
def cert_19_13 : Tree := (.side 4 12 false (2))
theorem checked_19_13 : check 151 p_19_13 cert_19_13 = true := by decide +kernel
theorem safe_19_13 : ∀ m, compatible p_19_13 m → WeightedBound 151 m := sound 151 _ cert_19_13 (by decide) checked_19_13
def p_19_14 := refine p_19 (4,false) (some ⟨true,false,3⟩)
def cert_19_14 : Tree := (.side 7 8 false (1))
theorem checked_19_14 : check 151 p_19_14 cert_19_14 = true := by decide +kernel
theorem safe_19_14 : ∀ m, compatible p_19_14 m → WeightedBound 151 m := sound 151 _ cert_19_14 (by decide) checked_19_14
def p_19_15 := refine p_19 (4,false) (some ⟨true,true,3⟩)
def cert_19_15 : Tree := (.side 6 10 false (2))
theorem checked_19_15 : check 151 p_19_15 cert_19_15 = true := by decide +kernel
theorem safe_19_15 : ∀ m, compatible p_19_15 m → WeightedBound 151 m := sound 151 _ cert_19_15 (by decide) checked_19_15
def p_19_16 := refine p_19 (4,false) (some ⟨false,false,4⟩)
def cert_19_16 : Tree := (split 16 (5,true) 6 #[
(.side 0 17 false (2)),
(.last 19 (2,true)),
(.side 20 3 false (-2)),
(.last 19 (2,true)),
(.side 7 15 false (1)),
(.side 7 15 false (1)),
(.last 18 (2,true)),
(.side 1 16 false (2)),
(.side 0 18 false (2)),
(.side 0 18 false (2)),
(.last 20 (2,true)),
(.side 7 14 false (1)),
(.side 21 3 false (-3)),
(.side 21 3 false (-1)),
(.side 9 8 false (0)),
(.side 7 12 false (1)),
(.side 17 1 false (-3)),
(.side 17 1 false (-1)),
(.side 17 1 false (-3)),
(.side 17 3 false (-1)),
(.side 17 3 false (-2)),
(.side 17 3 false (0)),
(.side 15 3 false (-1)),
(.side 13 4 true (-2))])
theorem checked_19_16 : check 151 p_19_16 cert_19_16 = true := by decide +kernel
theorem safe_19_16 : ∀ m, compatible p_19_16 m → WeightedBound 151 m := sound 151 _ cert_19_16 (by decide) checked_19_16
def p_19_17 := refine p_19 (4,false) (some ⟨false,true,4⟩)
def cert_19_17 : Tree := (.side 20 1 true (2))
theorem checked_19_17 : check 151 p_19_17 cert_19_17 = true := by decide +kernel
theorem safe_19_17 : ∀ m, compatible p_19_17 m → WeightedBound 151 m := sound 151 _ cert_19_17 (by decide) checked_19_17
def p_19_18 := refine p_19 (4,false) (some ⟨true,false,4⟩)
def cert_19_18 : Tree := (split 16 (5,true) 6 #[
(.side 0 17 false (2)),
(.side 34 3 false (2)),
(.side 20 3 false (-2)),
(.side 21 13 true (-1)),
(.side 7 15 false (1)),
(.last 18 (2,true)),
(.last 18 (2,true)),
(.last 18 (2,true)),
(.side 0 18 false (2)),
(.last 20 (2,true)),
(.last 20 (2,true)),
(.side 7 14 false (1)),
(.side 21 3 false (-3)),
(.side 9 8 true (-2)),
(.side 9 8 false (0)),
(.side 7 12 false (1)),
(.side 17 1 false (-3)),
(.side 17 1 false (-1)),
(.side 17 1 false (-3)),
(.side 17 3 false (-1)),
(.side 17 3 false (-2)),
(.side 26 3 false (3)),
(.side 15 3 false (-1)),
(.side 21 7 true (0))])
theorem checked_19_18 : check 151 p_19_18 cert_19_18 = true := by decide +kernel
theorem safe_19_18 : ∀ m, compatible p_19_18 m → WeightedBound 151 m := sound 151 _ cert_19_18 (by decide) checked_19_18
def p_19_19 := refine p_19 (4,false) (some ⟨true,true,4⟩)
def cert_19_19 : Tree := (split 16 (5,true) 6 #[
(.side 3 14 false (2)),
(.side 19 1 true (3)),
(.side 5 12 false (2)),
(.side 19 1 true (3)),
(.side 23 1 true (1)),
(.last 18 (2,true)),
(.side 27 1 true (1)),
(.last 18 (2,true)),
(.last 17 (2,true)),
(.last 20 (2,true)),
(.last 17 (2,true)),
(.side 6 16 false (2)),
(.side 7 10 false (1)),
(.side 22 1 true (2)),
(.side 7 10 false (1)),
(.side 6 14 false (2)),
(.side 30 1 true (-4)),
(.side 20 1 true (2)),
(.side 17 3 false (-1)),
(.side 20 1 true (2)),
(.side 31 1 true (-3)),
(.side 21 1 true (3)),
(.side 18 3 false (-2)),
(.side 21 1 true (3))])
theorem checked_19_19 : check 151 p_19_19 cert_19_19 = true := by decide +kernel
theorem safe_19_19 : ∀ m, compatible p_19_19 m → WeightedBound 151 m := sound 151 _ cert_19_19 (by decide) checked_19_19
def p_19_20 := refine p_19 (4,false) (some ⟨false,false,5⟩)
def cert_19_20 : Tree := (split 15 (5,true) 6 #[
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 7 19 false (1)),
(.last 17 (2,true)),
(.last 22 (2,true)),
(.last 17 (2,true)),
(.last 16 (2,true)),
(.last 19 (2,true)),
(.last 16 (2,true)),
(.side 2 14 false (2)),
(.side 8 8 false (0)),
(.side 27 7 true (1)),
(.side 8 8 false (0)),
(.side 4 12 false (2)),
(.side 17 4 false (-2)),
(.side 13 4 true (-1)),
(.side 17 4 false (-2)),
(.side 14 2 true (-1)),
(.side 16 3 false (-2)),
(.side 21 3 true (1)),
(.side 16 3 false (-2)),
(.side 21 3 true (1))])
theorem checked_19_20 : check 151 p_19_20 cert_19_20 = true := by decide +kernel
theorem safe_19_20 : ∀ m, compatible p_19_20 m → WeightedBound 151 m := sound 151 _ cert_19_20 (by decide) checked_19_20
def p_19_21 := refine p_19 (4,false) (some ⟨false,true,5⟩)
def cert_19_21 : Tree := (split 15 (5,true) 6 #[
(.last 18 (2,true)),
(.side 0 28 true (-2)),
(.side 19 2 true (1)),
(.side 18 16 false (3)),
(.side 6 16 false (2)),
(.side 17 2 true (3)),
(.last 17 (2,true)),
(.side 17 2 true (3)),
(.side 2 14 false (2)),
(.last 16 (2,true)),
(.side 2 14 false (2)),
(.last 16 (2,true)),
(.side 4 12 false (2)),
(.side 21 2 true (1)),
(.side 4 12 false (2)),
(.side 4 14 false (2)),
(.side 20 2 true (0)),
(.side 17 2 true (1)),
(.side 14 2 true (0)),
(.side 18 2 true (2)),
(.side 19 2 true (1)),
(.side 17 2 true (3)),
(.side 20 3 false (-2)),
(.side 17 2 true (3))])
theorem checked_19_21 : check 151 p_19_21 cert_19_21 = true := by decide +kernel
theorem safe_19_21 : ∀ m, compatible p_19_21 m → WeightedBound 151 m := sound 151 _ cert_19_21 (by decide) checked_19_21
def p_19_22 := refine p_19 (4,false) (some ⟨true,false,5⟩)
def cert_19_22 : Tree := (split 15 (5,true) 6 #[
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.side 7 19 false (1)),
(.side 16 24 true (0)),
(.last 22 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))]⟩),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.side 8 8 false (0)),
(.side 7 12 false (1)),
(.side 8 8 false (0)),
(.side 6 10 false (2)),
(.side 19 4 false (-3)),
(.side 12 4 true (-1)),
(.side 19 4 false (-3)),
(.side 14 4 true (-1)),
(.side 16 3 false (-2)),
(.side 17 4 true (1)),
(.side 16 3 false (-2)),
(.side 17 4 true (1))])
theorem checked_19_22 : check 151 p_19_22 cert_19_22 = true := by decide +kernel
theorem safe_19_22 : ∀ m, compatible p_19_22 m → WeightedBound 151 m := sound 151 _ cert_19_22 (by decide) checked_19_22
def p_19_23 := refine p_19 (4,false) (some ⟨true,true,5⟩)
def cert_19_23 : Tree := (split 15 (5,true) 6 #[
(.side 6 14 false (2)),
(.side 18 16 false (3)),
(.side 6 12 false (2)),
(.side 18 14 false (3)),
(.side 20 2 true (2)),
(.side 17 2 true (3)),
(.side 23 2 true (1)),
(.side 17 2 true (3)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.last 16 (2,true)),
(.side 6 10 false (2)),
(.side 6 14 false (2)),
(.side 6 10 false (2)),
(.side 6 12 false (2)),
(.side 30 2 true (-4)),
(.side 17 2 true (1)),
(.side 17 8 false (-1)),
(.side 18 2 true (2)),
(.side 30 2 true (-4)),
(.side 17 2 true (3)),
(.side 18 3 false (-2)),
(.side 17 2 true (3))])
theorem checked_19_23 : check 151 p_19_23 cert_19_23 = true := by decide +kernel
theorem safe_19_23 : ∀ m, compatible p_19_23 m → WeightedBound 151 m := sound 151 _ cert_19_23 (by decide) checked_19_23
theorem safe_19 : ∀ m, compatible p_19 m → WeightedBound 151 m := by
  apply split_safe 151 p_19 14 (4,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_19_0 | exact safe_19_1 | exact safe_19_2 | exact safe_19_3 | exact safe_19_4 | exact safe_19_5 | exact safe_19_6 | exact safe_19_7 | exact safe_19_8 | exact safe_19_9 | exact safe_19_10 | exact safe_19_11 | exact safe_19_12 | exact safe_19_13 | exact safe_19_14 | exact safe_19_15 | exact safe_19_16 | exact safe_19_17 | exact safe_19_18 | exact safe_19_19 | exact safe_19_20 | exact safe_19_21 | exact safe_19_22 | exact safe_19_23
def p_20 := refine parent (5,false) (some ⟨false,false,5⟩)
def p_20_0 := refine p_20 (5,true) (some ⟨false,false,0⟩)
def cert_20_0 : Tree := (.side 0 15 false (2))
theorem checked_20_0 : check 151 p_20_0 cert_20_0 = true := by decide +kernel
theorem safe_20_0 : ∀ m, compatible p_20_0 m → WeightedBound 151 m := sound 151 _ cert_20_0 (by decide) checked_20_0
def p_20_1 := refine p_20 (5,true) (some ⟨false,true,0⟩)
def cert_20_1 : Tree := (split 17 (2,true) 6 #[
(.side 3 15 false (2)),
(.side 20 17 false (3)),
(.side 5 13 false (2)),
(.side 20 15 false (3)),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.side 0 29 true (-2)),
(.last 19 (4,false)),
(.side 0 21 false (2)),
(.side 0 48 true (-3)),
(.side 15 6 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6),(false,4)],[(true,2),(true,6),(true,4)],[(false,3),(false,7),(false,5)],[(true,3),(true,7),(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),.empty,(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))) .empty),(.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) .empty) .empty)]⟩),
(.side 7 11 false (1)),
(.side 4 15 false (2)),
(.side 7 11 false (1)),
(.side 6 13 false (2)),
(.side 0 25 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[(false,2),(false,6),(false,8)],[(true,2)],[(false,3),(false,5)],[(true,3)],[(false,4),(false,9),(false,11)],[(true,5)],[(true,6)],[],[(true,8)]],#[(1,2),(1,2),(3,4),(5,6),(7,4),(5,8),(3,9),(10,6),(3,11),(7,9),(10,8),(7,11)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,4),(true,1)],[(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))))),(.branch (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .leaf) (.branch (.branch (.branch .empty .leaf) .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .leaf)) .empty) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty))),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .leaf)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .leaf)))),(.branch .empty (.branch (.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf)))))]⟩),
(.side 0 25 true (-2)),
(.last 53 (4,false)),
(.last 21 (4,false)),
(.side 0 19 true (-2)),
(.side 7 17 false (2)),
(.side 26 19 false (4))])
theorem checked_20_1 : check 151 p_20_1 cert_20_1 = true := by decide +kernel
theorem safe_20_1 : ∀ m, compatible p_20_1 m → WeightedBound 151 m := sound 151 _ cert_20_1 (by decide) checked_20_1
def p_20_2 := refine p_20 (5,true) (some ⟨true,false,0⟩)
def cert_20_2 : Tree := (split 17 (4,false) 6 #[
(.side 6 19 false (2)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,5),(true,3),(true,4)],[(false,2),(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,4),(true,1),(true,5)],[(false,4),(false,5),(false,2)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf)))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)))),(.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))))]⟩),
(.side 5 21 false (2)),
(.side 7 21 false (2)),
(.side 1 17 false (2)),
(.last 19 (2,true)),
(.last 19 (2,true)),
(.last 19 (2,true)),
(.side 7 15 false (1)),
(.last 21 (2,true)),
(.side 7 15 false (1)),
(.side 7 19 false (1)),
(.side 7 13 false (1)),
(.side 33 4 true (-1)),
(.side 7 13 false (1)),
(.side 7 17 false (1)),
(.side 20 1 false (-4)),
(.side 39 1 true (-3)),
(.side 20 1 false (-4)),
(.side 7 19 false (1)),
(.side 13 5 false (-1)),
(.side 13 7 false (0)),
(.side 13 5 false (-1)),
(.side 4 23 false (2))])
theorem checked_20_2 : check 151 p_20_2 cert_20_2 = true := by decide +kernel
theorem safe_20_2 : ∀ m, compatible p_20_2 m → WeightedBound 151 m := sound 151 _ cert_20_2 (by decide) checked_20_2
def p_20_3 := refine p_20 (5,true) (some ⟨true,true,0⟩)
def cert_20_3 : Tree := (split 17 (2,true) 6 #[
(.side 6 16 false (2)),
(.side 20 18 false (3)),
(.side 6 14 false (2)),
(.side 20 16 false (3)),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6),(false,4)],[(true,2),(true,6),(true,4)],[(false,3),(false,7),(false,5)],[(true,3),(true,7),(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),.empty,(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)))),(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)]⟩),
(.last 19 (4,false)),
(.side 0 22 false (2)),
(.side 0 50 true (-4)),
(.side 18 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch .leaf (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),.empty,(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty)]⟩),
(.side 6 12 false (2)),
(.side 6 16 false (2)),
(.side 6 12 false (2)),
(.side 6 14 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6),(false,4)],[(true,2),(true,6),(true,4)],[(false,3),(false,7),(false,5)],[(true,3),(true,7),(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch .leaf (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty)]⟩),
(.last 54 (4,false)),
(.last 70 (4,false)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,8)],[(false,2)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,14)],[],[(true,2)],[],[],[(false,4)],[(true,4)],[],[],[],[(false,7)],[],[(true,8)],[],[],[],[],[],[],[(false,14)],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,14),(15,16),(3,17),(7,18),(19,10),(20,6),(21,2),(3,22),(3,23),(7,24),(13,25),(26,16),(27,10),(28,6),(3,29),(7,30),(13,31),(21,6),(7,22),(32,16),(33,10),(7,34),(13,35),(21,10),(13,22),(36,16),(13,37),(21,16),(21,22),(21,22)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)),(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) .empty),(.branch .empty (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))),(.branch (.branch (.branch .empty (.branch .empty (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)) .empty))]⟩),
(.last 21 (4,false)),
(.side 26 20 false (4)),
(.side 6 16 false (2)),
(.side 26 18 false (4))])
theorem checked_20_3 : check 151 p_20_3 cert_20_3 = true := by decide +kernel
theorem safe_20_3 : ∀ m, compatible p_20_3 m → WeightedBound 151 m := sound 151 _ cert_20_3 (by decide) checked_20_3
def p_20_4 := refine p_20 (5,true) (some ⟨false,false,1⟩)
def cert_20_4 : Tree := (.side 7 13 false (1))
theorem checked_20_4 : check 151 p_20_4 cert_20_4 = true := by decide +kernel
theorem safe_20_4 : ∀ m, compatible p_20_4 m → WeightedBound 151 m := sound 151 _ cert_20_4 (by decide) checked_20_4
def p_20_5 := refine p_20 (5,true) (some ⟨false,true,1⟩)
def cert_20_5 : Tree := (.side 7 13 false (1))
theorem checked_20_5 : check 151 p_20_5 cert_20_5 = true := by decide +kernel
theorem safe_20_5 : ∀ m, compatible p_20_5 m → WeightedBound 151 m := sound 151 _ cert_20_5 (by decide) checked_20_5
def p_20_6 := refine p_20 (5,true) (some ⟨true,false,1⟩)
def cert_20_6 : Tree := (split 16 (2,true) 6 #[
(.side 7 13 false (1)),
(.side 22 23 false (3)),
(.side 7 11 false (1)),
(.side 22 19 false (3)),
(.last 18 (4,false)),
(.side 7 19 false (1)),
(.side 19 1 false (-3)),
(.side 6 17 false (2)),
(.side 0 19 false (2)),
(.side 6 19 false (2)),
(.side 16 6 false (-2)),
(.side 2 15 false (2)),
(.side 8 9 false (0)),
(.last 20 (4,false)),
(.side 8 9 false (0)),
(.side 4 13 false (2)),
(.side 18 1 false (-4)),
(.last 17 (4,false)),
(.side 18 1 false (-4)),
(.last 17 (4,false)),
(.side 14 3 false (-2)),
(.side 13 5 false (-1)),
(.side 14 3 false (-2)),
(.side 21 1 false (-3))])
theorem checked_20_6 : check 151 p_20_6 cert_20_6 = true := by decide +kernel
theorem safe_20_6 : ∀ m, compatible p_20_6 m → WeightedBound 151 m := sound 151 _ cert_20_6 (by decide) checked_20_6
def p_20_7 := refine p_20 (5,true) (some ⟨true,true,1⟩)
def cert_20_7 : Tree := (.side 1 14 false (2))
theorem checked_20_7 : check 151 p_20_7 cert_20_7 = true := by decide +kernel
theorem safe_20_7 : ∀ m, compatible p_20_7 m → WeightedBound 151 m := sound 151 _ cert_20_7 (by decide) checked_20_7
def p_20_8 := refine p_20 (5,true) (some ⟨false,false,2⟩)
def cert_20_8 : Tree := (.side 0 16 false (2))
theorem checked_20_8 : check 151 p_20_8 cert_20_8 = true := by decide +kernel
theorem safe_20_8 : ∀ m, compatible p_20_8 m → WeightedBound 151 m := sound 151 _ cert_20_8 (by decide) checked_20_8
def p_20_9 := refine p_20 (5,true) (some ⟨false,true,2⟩)
def cert_20_9 : Tree := (.side 0 16 false (2))
theorem checked_20_9 : check 151 p_20_9 cert_20_9 = true := by decide +kernel
theorem safe_20_9 : ∀ m, compatible p_20_9 m → WeightedBound 151 m := sound 151 _ cert_20_9 (by decide) checked_20_9
def p_20_10 := refine p_20 (5,true) (some ⟨true,false,2⟩)
def cert_20_10 : Tree := (split 18 (2,true) 6 #[
(.side 3 16 false (2)),
(.side 24 26 false (3)),
(.side 5 14 false (2)),
(.side 24 22 false (3)),
(.last 20 (4,false)),
(.side 4 22 false (2)),
(.side 11 8 false (0)),
(.side 6 20 false (2)),
(.side 0 22 false (2)),
(.side 6 22 false (2)),
(.side 15 6 false (-2)),
(.side 6 18 false (2)),
(.side 7 12 false (1)),
(.last 22 (4,false)),
(.side 7 12 false (1)),
(.side 6 16 false (2)),
(.side 14 6 false (-2)),
(.last 19 (4,false)),
(.side 14 6 false (-2)),
(.last 19 (4,false)),
(.side 21 1 false (-5)),
(.side 14 9 false (-1)),
(.side 21 1 false (-5)),
(.side 20 2 true (-3))])
theorem checked_20_10 : check 151 p_20_10 cert_20_10 = true := by decide +kernel
theorem safe_20_10 : ∀ m, compatible p_20_10 m → WeightedBound 151 m := sound 151 _ cert_20_10 (by decide) checked_20_10
def p_20_11 := refine p_20 (5,true) (some ⟨true,true,2⟩)
def cert_20_11 : Tree := (.side 7 12 false (1))
theorem checked_20_11 : check 151 p_20_11 cert_20_11 = true := by decide +kernel
theorem safe_20_11 : ∀ m, compatible p_20_11 m → WeightedBound 151 m := sound 151 _ cert_20_11 (by decide) checked_20_11
def p_20_12 := refine p_20 (5,true) (some ⟨false,false,3⟩)
def cert_20_12 : Tree := (split 18 (4,false) 6 #[
(.side 6 20 false (2)),
(.last 21 (2,true)),
(.side 6 24 false (2)),
(.last 21 (2,true)),
(.side 1 18 false (2)),
(.side 8 24 false (0)),
(.last 20 (2,true)),
(.side 7 22 false (1)),
(.side 7 16 false (1)),
(.side 7 24 false (1)),
(.side 7 16 false (1)),
(.side 7 20 false (1)),
(.side 7 14 false (1)),
(.side 7 26 false (1)),
(.side 7 14 false (1)),
(.side 7 18 false (1)),
(.side 21 1 false (-5)),
(.side 48 1 true (-6)),
(.side 21 1 false (-5)),
(.side 7 20 false (1)),
(.side 13 6 false (-1)),
(.side 13 8 false (-1)),
(.side 13 6 false (-1)),
(.side 7 16 false (1))])
theorem checked_20_12 : check 151 p_20_12 cert_20_12 = true := by decide +kernel
theorem safe_20_12 : ∀ m, compatible p_20_12 m → WeightedBound 151 m := sound 151 _ cert_20_12 (by decide) checked_20_12
def p_20_13 := refine p_20 (5,true) (some ⟨false,true,3⟩)
def cert_20_13 : Tree := (split 18 (4,false) 6 #[
(.last 21 (2,true)),
(.side 19 15 true (-1)),
(.side 34 3 true (0)),
(.side 7 18 false (2)),
(.side 1 18 false (2)),
(.side 27 19 true (-1)),
(.last 20 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(false,0)],[(true,0),(true,3)],[(false,2)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[(true,2),(true,6)],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .leaf (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch (.branch .leaf .leaf) .empty)))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) .empty) .empty)]⟩),
(.side 7 16 false (1)),
(.last 19 (2,true)),
(.side 7 16 false (1)),
(.last 19 (2,true)),
(.side 7 14 false (1)),
(.side 37 4 true (0)),
(.side 7 14 false (1)),
(.side 7 16 false (1)),
(.side 21 1 false (-3)),
(.side 36 1 true (0)),
(.side 21 1 false (-3)),
(.side 30 1 true (2)),
(.side 13 6 true (-2)),
(.side 25 8 true (0)),
(.side 9 12 true (-2)),
(.side 7 20 false (2))])
theorem checked_20_13 : check 151 p_20_13 cert_20_13 = true := by decide +kernel
theorem safe_20_13 : ∀ m, compatible p_20_13 m → WeightedBound 151 m := sound 151 _ cert_20_13 (by decide) checked_20_13
def p_20_14 := refine p_20 (5,true) (some ⟨true,false,3⟩)
def cert_20_14 : Tree := (.side 9 6 false (0))
theorem checked_20_14 : check 151 p_20_14 cert_20_14 = true := by decide +kernel
theorem safe_20_14 : ∀ m, compatible p_20_14 m → WeightedBound 151 m := sound 151 _ cert_20_14 (by decide) checked_20_14
def p_20_15 := refine p_20 (5,true) (some ⟨true,true,3⟩)
def cert_20_15 : Tree := (.side 7 10 false (1))
theorem checked_20_15 : check 151 p_20_15 cert_20_15 = true := by decide +kernel
theorem safe_20_15 : ∀ m, compatible p_20_15 m → WeightedBound 151 m := sound 151 _ cert_20_15 (by decide) checked_20_15
def p_20_16 := refine p_20 (5,true) (some ⟨false,false,4⟩)
def cert_20_16 : Tree := (split 15 (4,false) 6 #[
(.side 0 16 false (2)),
(.side 0 16 false (2)),
(.side 33 1 false (-5)),
(.side 6 17 false (2)),
(.side 7 14 false (1)),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.side 1 15 false (2)),
(.side 0 17 false (2)),
(.side 0 17 false (2)),
(.last 19 (2,true)),
(.side 7 13 false (1)),
(.side 7 15 false (1)),
(.side 37 4 true (-1)),
(.side 9 7 false (0)),
(.side 7 11 false (1)),
(.side 15 1 false (-3)),
(.side 20 1 false (0)),
(.side 15 1 false (-3)),
(.side 24 1 false (-4)),
(.side 16 1 false (-4)),
(.side 16 1 false (-2)),
(.side 16 1 false (-4)),
(.side 13 3 false (-1))])
theorem checked_20_16 : check 151 p_20_16 cert_20_16 = true := by decide +kernel
theorem safe_20_16 : ∀ m, compatible p_20_16 m → WeightedBound 151 m := sound 151 _ cert_20_16 (by decide) checked_20_16
def p_20_17 := refine p_20 (5,true) (some ⟨false,true,4⟩)
def cert_20_17 : Tree := (split 15 (4,false) 6 #[
(.side 0 16 false (2)),
(.side 0 22 true (-2)),
(.side 33 3 true (0)),
(.automata ⟨⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1),(true,4),(true,3),(true,5)],[(false,2),(false,4),(false,5)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,4),(true,1),(true,5)],[(false,4),(false,5),(false,2)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty)),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty)),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .empty .leaf))))),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))))),(.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf)))))]⟩),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.last 17 (2,true)),
(.last 17 (2,true)),
(.side 0 17 false (2)),
(.last 19 (2,true)),
(.last 19 (2,true)),
(.side 7 13 false (1)),
(.side 7 15 false (1)),
(.side 29 4 true (1)),
(.side 9 7 false (0)),
(.side 7 11 false (1)),
(.side 15 1 false (-1)),
(.side 18 1 false (0)),
(.side 15 1 false (-1)),
(.side 22 1 true (2)),
(.side 16 1 false (-2)),
(.side 16 1 false (0)),
(.side 16 1 false (-2)),
(.side 21 3 true (0))])
theorem checked_20_17 : check 151 p_20_17 cert_20_17 = true := by decide +kernel
theorem safe_20_17 : ∀ m, compatible p_20_17 m → WeightedBound 151 m := sound 151 _ cert_20_17 (by decide) checked_20_17
def p_20_18 := refine p_20 (5,true) (some ⟨true,false,4⟩)
def cert_20_18 : Tree := (split 15 (4,false) 6 #[
(.last 18 (2,true)),
(.side 7 12 false (1)),
(.side 10 6 false (0)),
(.side 3 13 false (2)),
(.side 7 14 false (1)),
(.last 19 (2,true)),
(.last 17 (2,true)),
(.last 19 (2,true)),
(.side 0 17 false (2)),
(.last 16 (2,true)),
(.last 19 (2,true)),
(.last 16 (2,true)),
(.side 7 15 false (1)),
(.side 8 8 false (0)),
(.side 9 7 false (0)),
(.side 7 9 false (1)),
(.side 15 1 false (-3)),
(.side 17 1 false (-3)),
(.side 15 1 false (-3)),
(.side 14 3 false (-2)),
(.side 16 1 false (-4)),
(.side 14 2 true (-3)),
(.side 16 1 false (-4)),
(.side 18 1 false (-4))])
theorem checked_20_18 : check 151 p_20_18 cert_20_18 = true := by decide +kernel
theorem safe_20_18 : ∀ m, compatible p_20_18 m → WeightedBound 151 m := sound 151 _ cert_20_18 (by decide) checked_20_18
def p_20_19 := refine p_20 (5,true) (some ⟨true,true,4⟩)
def cert_20_19 : Tree := (split 15 (4,false) 6 #[
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,4),(true,1)],[(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch .empty (.branch (.branch .leaf .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))))]⟩),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,4),(true,1)],[(false,2),(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))),(.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)))]⟩),
(.side 7 16 false (1)),
(.last 17 (2,true)),
(.side 18 1 false (-2)),
(.last 17 (2,true)),
(.last 16 (2,true)),
(.last 19 (2,true)),
(.last 16 (2,true)),
(.side 2 14 false (2)),
(.side 8 8 false (0)),
(.side 29 4 true (1)),
(.side 8 8 false (0)),
(.side 4 12 false (2)),
(.side 17 1 false (-3)),
(.side 29 1 true (-1)),
(.side 17 1 false (-3)),
(.side 22 1 true (2)),
(.side 14 2 true (-2)),
(.side 13 4 true (-2)),
(.side 14 4 true (-2)),
(.side 21 3 true (1))])
theorem checked_20_19 : check 151 p_20_19 cert_20_19 = true := by decide +kernel
theorem safe_20_19 : ∀ m, compatible p_20_19 m → WeightedBound 151 m := sound 151 _ cert_20_19 (by decide) checked_20_19
def p_20_20 := refine p_20 (5,true) (some ⟨false,false,5⟩)
def cert_20_20 : Tree := (.side 15 1 false (-3))
theorem checked_20_20 : check 151 p_20_20 cert_20_20 = true := by decide +kernel
theorem safe_20_20 : ∀ m, compatible p_20_20 m → WeightedBound 151 m := sound 151 _ cert_20_20 (by decide) checked_20_20
def p_20_21 := refine p_20 (5,true) (some ⟨false,true,5⟩)
def cert_20_21 : Tree := (.side 15 1 false (-1))
theorem checked_20_21 : check 151 p_20_21 cert_20_21 = true := by decide +kernel
theorem safe_20_21 : ∀ m, compatible p_20_21 m → WeightedBound 151 m := sound 151 _ cert_20_21 (by decide) checked_20_21
def p_20_22 := refine p_20 (5,true) (some ⟨true,false,5⟩)
def cert_20_22 : Tree := (.side 15 1 false (-3))
theorem checked_20_22 : check 151 p_20_22 cert_20_22 = true := by decide +kernel
theorem safe_20_22 : ∀ m, compatible p_20_22 m → WeightedBound 151 m := sound 151 _ cert_20_22 (by decide) checked_20_22
def p_20_23 := refine p_20 (5,true) (some ⟨true,true,5⟩)
def cert_20_23 : Tree := (.side 13 2 true (-2))
theorem checked_20_23 : check 151 p_20_23 cert_20_23 = true := by decide +kernel
theorem safe_20_23 : ∀ m, compatible p_20_23 m → WeightedBound 151 m := sound 151 _ cert_20_23 (by decide) checked_20_23
theorem safe_20 : ∀ m, compatible p_20 m → WeightedBound 151 m := by
  apply split_safe 151 p_20 14 (5,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_20_0 | exact safe_20_1 | exact safe_20_2 | exact safe_20_3 | exact safe_20_4 | exact safe_20_5 | exact safe_20_6 | exact safe_20_7 | exact safe_20_8 | exact safe_20_9 | exact safe_20_10 | exact safe_20_11 | exact safe_20_12 | exact safe_20_13 | exact safe_20_14 | exact safe_20_15 | exact safe_20_16 | exact safe_20_17 | exact safe_20_18 | exact safe_20_19 | exact safe_20_20 | exact safe_20_21 | exact safe_20_22 | exact safe_20_23
def p_21 := refine parent (5,false) (some ⟨false,true,5⟩)
def p_21_0 := refine p_21 (5,true) (some ⟨false,false,0⟩)
def cert_21_0 : Tree := (split 18 (2,true) 6 #[
(.side 7 20 false (2)),
(.side 26 22 false (4)),
(.side 7 18 false (2)),
(.side 26 20 false (4)),
(.last 20 (4,false)),
(.side 77 1 true (5)),
(.side 21 1 true (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3),(true,4)],[(false,2),(false,5)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,2)],[(true,2)],[],[],[(false,4)],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,2),(3,8),(3,9),(10,6),(3,11),(7,6),(7,8),(7,8)]⟩,#[(.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .leaf) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty)]⟩),
(.side 7 38 false (2)),
(.side 0 50 true (-4)),
(.side 7 18 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 7 16 false (2)),
(.last 22 (4,false)),
(.side 7 16 false (2)),
(.side 21 18 false (3)),
(.side 6 22 false (2)),
(.last 19 (4,false)),
(.side 6 22 false (2)),
(.last 19 (4,false)),
(.side 7 20 false (2)),
(.side 19 1 true (3)),
(.side 7 20 false (2)),
(.side 19 1 true (3))])
theorem checked_21_0 : check 151 p_21_0 cert_21_0 = true := by decide +kernel
theorem safe_21_0 : ∀ m, compatible p_21_0 m → WeightedBound 151 m := sound 151 _ cert_21_0 (by decide) checked_21_0
def p_21_1 := refine p_21 (5,true) (some ⟨false,true,0⟩)
def cert_21_1 : Tree := (.side 0 28 true (-2))
theorem checked_21_1 : check 151 p_21_1 cert_21_1 = true := by decide +kernel
theorem safe_21_1 : ∀ m, compatible p_21_1 m → WeightedBound 151 m := sound 151 _ cert_21_1 (by decide) checked_21_1
def p_21_2 := refine p_21 (5,true) (some ⟨true,false,0⟩)
def cert_21_2 : Tree := (.side 19 1 true (1))
theorem checked_21_2 : check 151 p_21_2 cert_21_2 = true := by decide +kernel
theorem safe_21_2 : ∀ m, compatible p_21_2 m → WeightedBound 151 m := sound 151 _ cert_21_2 (by decide) checked_21_2
def p_21_3 := refine p_21 (5,true) (some ⟨true,true,0⟩)
def cert_21_3 : Tree := (.side 3 13 true (-2))
theorem checked_21_3 : check 151 p_21_3 cert_21_3 = true := by decide +kernel
theorem safe_21_3 : ∀ m, compatible p_21_3 m → WeightedBound 151 m := sound 151 _ cert_21_3 (by decide) checked_21_3
def p_21_4 := refine p_21 (5,true) (some ⟨false,false,1⟩)
def cert_21_4 : Tree := (.side 7 18 false (1))
theorem checked_21_4 : check 151 p_21_4 cert_21_4 = true := by decide +kernel
theorem safe_21_4 : ∀ m, compatible p_21_4 m → WeightedBound 151 m := sound 151 _ cert_21_4 (by decide) checked_21_4
def p_21_5 := refine p_21 (5,true) (some ⟨false,true,1⟩)
def cert_21_5 : Tree := (split 17 (4,false) 6 #[
(.side 0 18 true (-2)),
(.side 0 18 true (-2)),
(.side 16 3 true (2)),
(.side 37 1 true (5)),
(.side 18 14 true (0)),
(.side 18 14 true (2)),
(.last 19 (2,true)),
(.side 1 17 true (-2)),
(.side 0 19 true (-2)),
(.side 0 19 true (-2)),
(.last 21 (2,true)),
(.side 18 14 true (1)),
(.side 22 14 true (-1)),
(.side 16 4 true (2)),
(.side 22 1 true (2)),
(.side 18 14 true (1)),
(.side 23 1 true (-3)),
(.side 17 1 true (3)),
(.side 32 1 false (4)),
(.side 17 1 true (3)),
(.side 18 1 true (2)),
(.side 18 1 true (4)),
(.side 18 14 true (2)),
(.side 18 1 true (4))])
theorem checked_21_5 : check 151 p_21_5 cert_21_5 = true := by decide +kernel
theorem safe_21_5 : ∀ m, compatible p_21_5 m → WeightedBound 151 m := sound 151 _ cert_21_5 (by decide) checked_21_5
def p_21_6 := refine p_21 (5,true) (some ⟨true,false,1⟩)
def cert_21_6 : Tree := (split 17 (2,true) 6 #[
(.side 7 18 false (1)),
(.side 20 20 false (3)),
(.side 7 16 false (1)),
(.side 20 18 false (3)),
(.last 19 (4,false)),
(.last 19 (4,false)),
(.side 27 1 true (1)),
(.last 19 (4,false)),
(.side 7 16 false (1)),
(.side 0 52 true (-4)),
(.side 7 16 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 7 14 false (1)),
(.side 7 18 false (2)),
(.side 7 14 false (1)),
(.side 7 16 false (2)),
(.side 26 1 true (0)),
(.side 19 1 true (1)),
(.side 12 6 true (-1)),
(.side 22 1 true (0)),
(.side 28 3 false (2)),
(.side 21 1 true (3)),
(.side 26 3 false (0)),
(.side 21 1 true (1))])
theorem checked_21_6 : check 151 p_21_6 cert_21_6 = true := by decide +kernel
theorem safe_21_6 : ∀ m, compatible p_21_6 m → WeightedBound 151 m := sound 151 _ cert_21_6 (by decide) checked_21_6
def p_21_7 := refine p_21 (5,true) (some ⟨true,true,1⟩)
def cert_21_7 : Tree := (split 17 (4,false) 6 #[
(.side 37 1 true (3)),
(.side 0 18 true (-2)),
(.side 16 3 true (2)),
(.side 11 28 true (-1)),
(.side 1 17 true (-2)),
(.side 1 31 true (-2)),
(.last 19 (2,true)),
(.side 1 41 true (-2)),
(.side 1 30 true (-2)),
(.side 1 43 true (-2)),
(.side 7 15 true (-2)),
(.side 37 1 true (3)),
(.side 1 28 true (-2)),
(.side 16 4 true (2)),
(.side 7 13 true (-2)),
(.side 35 1 true (3)),
(.side 20 1 true (0)),
(.side 17 1 true (3)),
(.side 12 7 true (-1)),
(.side 17 1 true (3)),
(.side 18 1 true (2)),
(.side 18 1 true (4)),
(.side 1 43 true (-2)),
(.side 18 1 true (4))])
theorem checked_21_7 : check 151 p_21_7 cert_21_7 = true := by decide +kernel
theorem safe_21_7 : ∀ m, compatible p_21_7 m → WeightedBound 151 m := sound 151 _ cert_21_7 (by decide) checked_21_7
def p_21_8 := refine p_21 (5,true) (some ⟨false,false,2⟩)
def cert_21_8 : Tree := (.side 6 18 false (2))
theorem checked_21_8 : check 151 p_21_8 cert_21_8 = true := by decide +kernel
theorem safe_21_8 : ∀ m, compatible p_21_8 m → WeightedBound 151 m := sound 151 _ cert_21_8 (by decide) checked_21_8
def p_21_9 := refine p_21 (5,true) (some ⟨false,true,2⟩)
def cert_21_9 : Tree := (split 16 (2,true) 6 #[
(.side 0 17 true (-2)),
(.side 0 17 true (-2)),
(.last 19 (4,false)),
(.side 3 32 true (-2)),
(.side 0 32 true (-2)),
(.side 0 32 true (-2)),
(.side 21 1 true (1)),
(.side 1 16 true (-2)),
(.side 7 22 false (2)),
(.side 0 18 true (-2)),
(.side 7 20 false (2)),
(.side 0 31 true (-2)),
(.last 20 (4,false)),
(.last 20 (4,false)),
(.side 21 1 true (1)),
(.side 0 29 true (-2)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.side 17 1 true (1)),
(.side 17 1 true (3)),
(.side 0 20 true (-2)),
(.side 17 1 true (3))])
theorem checked_21_9 : check 151 p_21_9 cert_21_9 = true := by decide +kernel
theorem safe_21_9 : ∀ m, compatible p_21_9 m → WeightedBound 151 m := sound 151 _ cert_21_9 (by decide) checked_21_9
def p_21_10 := refine p_21 (5,true) (some ⟨true,false,2⟩)
def cert_21_10 : Tree := (split 19 (2,true) 6 #[
(.side 6 18 false (2)),
(.side 22 20 false (3)),
(.side 6 16 false (2)),
(.side 22 18 false (3)),
(.last 21 (4,false)),
(.last 21 (4,false)),
(.side 31 1 true (1)),
(.last 21 (4,false)),
(.side 0 24 false (2)),
(.side 0 54 true (-4)),
(.side 20 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch .leaf (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))]⟩),
(.side 6 14 false (2)),
(.side 6 18 false (2)),
(.side 6 14 false (2)),
(.side 6 16 false (2)),
(.last 23 (4,false)),
(.side 21 1 true (1)),
(.last 23 (4,false)),
(.last 35 (4,false)),
(.side 22 9 false (-2)),
(.side 6 20 false (2)),
(.side 22 8 false (-2)),
(.side 19 2 true (1))])
theorem checked_21_10 : check 151 p_21_10 cert_21_10 = true := by decide +kernel
theorem safe_21_10 : ∀ m, compatible p_21_10 m → WeightedBound 151 m := sound 151 _ cert_21_10 (by decide) checked_21_10
def p_21_11 := refine p_21 (5,true) (some ⟨true,true,2⟩)
def cert_21_11 : Tree := (split 16 (2,true) 6 #[
(.side 17 13 true (-1)),
(.side 38 17 true (0)),
(.side 17 13 true (-1)),
(.side 36 15 true (0)),
(.last 18 (4,false)),
(.last 37 (4,false)),
(.side 19 1 true (1)),
(.last 35 (4,false)),
(.side 6 20 false (2)),
(.side 0 62 true (-2)),
(.side 22 6 false (0)),
(.side 2 15 true (-2)),
(.side 22 1 true (0)),
(.last 20 (4,false)),
(.side 17 13 true (-1)),
(.side 4 13 true (-2)),
(.side 18 1 true (0)),
(.last 17 (4,false)),
(.side 17 13 true (0)),
(.last 17 (4,false)),
(.side 17 13 true (-1)),
(.side 17 1 true (3)),
(.side 15 2 true (1)),
(.side 17 1 true (3))])
theorem checked_21_11 : check 151 p_21_11 cert_21_11 = true := by decide +kernel
theorem safe_21_11 : ∀ m, compatible p_21_11 m → WeightedBound 151 m := sound 151 _ cert_21_11 (by decide) checked_21_11
def p_21_12 := refine p_21 (5,true) (some ⟨false,false,3⟩)
def cert_21_12 : Tree := (split 19 (4,false) 6 #[
(.last 22 (2,true)),
(.side 0 36 true (-2)),
(.side 23 1 true (1)),
(.side 22 20 false (3)),
(.side 6 20 false (2)),
(.side 20 18 true (2)),
(.last 21 (2,true)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4),(true,3),(true,5)],[(false,2),(false,4),(false,5)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2),(true,6)],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))]⟩),
(.side 2 18 false (2)),
(.last 20 (2,true)),
(.side 2 18 false (2)),
(.last 20 (2,true)),
(.side 4 16 false (2)),
(.side 25 1 true (1)),
(.side 4 16 false (2)),
(.side 4 18 false (2)),
(.side 43 1 true (-1)),
(.side 21 1 true (1)),
(.side 22 9 false (-2)),
(.side 4 18 false (2)),
(.side 27 1 true (1)),
(.side 25 1 true (3)),
(.side 4 18 false (2)),
(.side 4 18 false (2))])
theorem checked_21_12 : check 151 p_21_12 cert_21_12 = true := by decide +kernel
theorem safe_21_12 : ∀ m, compatible p_21_12 m → WeightedBound 151 m := sound 151 _ cert_21_12 (by decide) checked_21_12
def p_21_13 := refine p_21 (5,true) (some ⟨false,true,3⟩)
def cert_21_13 : Tree := (.side 21 1 true (1))
theorem checked_21_13 : check 151 p_21_13 cert_21_13 = true := by decide +kernel
theorem safe_21_13 : ∀ m, compatible p_21_13 m → WeightedBound 151 m := sound 151 _ cert_21_13 (by decide) checked_21_13
def p_21_14 := refine p_21 (5,true) (some ⟨true,false,3⟩)
def cert_21_14 : Tree := (.side 27 1 true (1))
theorem checked_21_14 : check 151 p_21_14 cert_21_14 = true := by decide +kernel
theorem safe_21_14 : ∀ m, compatible p_21_14 m → WeightedBound 151 m := sound 151 _ cert_21_14 (by decide) checked_21_14
def p_21_15 := refine p_21 (5,true) (some ⟨true,true,3⟩)
def cert_21_15 : Tree := (.side 16 11 true (-1))
theorem checked_21_15 : check 151 p_21_15 cert_21_15 = true := by decide +kernel
theorem safe_21_15 : ∀ m, compatible p_21_15 m → WeightedBound 151 m := sound 151 _ cert_21_15 (by decide) checked_21_15
def p_21_16 := refine p_21 (5,true) (some ⟨false,false,4⟩)
def cert_21_16 : Tree := (split 16 (4,false) 6 #[
(.side 6 18 false (2)),
(.side 0 20 true (-2)),
(.side 23 1 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))]⟩),
(.side 1 16 false (2)),
(.last 18 (2,true)),
(.last 18 (2,true)),
(.last 18 (2,true)),
(.side 7 14 false (1)),
(.last 20 (2,true)),
(.side 7 14 false (1)),
(.side 7 18 false (1)),
(.side 7 12 false (1)),
(.side 21 1 true (1)),
(.side 7 12 false (1)),
(.side 7 16 false (1)),
(.side 25 1 false (1)),
(.side 19 1 true (1)),
(.side 22 1 false (-2)),
(.side 21 1 true (-1)),
(.side 22 1 true (0)),
(.side 20 1 true (2)),
(.side 20 3 false (-2)),
(.side 20 1 true (2))])
theorem checked_21_16 : check 151 p_21_16 cert_21_16 = true := by decide +kernel
theorem safe_21_16 : ∀ m, compatible p_21_16 m → WeightedBound 151 m := sound 151 _ cert_21_16 (by decide) checked_21_16
def p_21_17 := refine p_21 (5,true) (some ⟨false,true,4⟩)
def cert_21_17 : Tree := (.side 17 1 true (1))
theorem checked_21_17 : check 151 p_21_17 cert_21_17 = true := by decide +kernel
theorem safe_21_17 : ∀ m, compatible p_21_17 m → WeightedBound 151 m := sound 151 _ cert_21_17 (by decide) checked_21_17
def p_21_18 := refine p_21 (5,true) (some ⟨true,false,4⟩)
def cert_21_18 : Tree := (split 16 (4,false) 6 #[
(.last 19 (2,true)),
(.side 17 13 true (-1)),
(.side 27 1 true (1)),
(.side 7 16 false (2)),
(.side 1 16 false (2)),
(.side 19 1 true (1)),
(.last 18 (2,true)),
(.side 19 1 true (1)),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.side 7 12 false (1)),
(.side 31 1 true (1)),
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 24 1 false (0)),
(.side 23 1 true (1)),
(.side 22 1 false (-2)),
(.side 25 3 false (-1)),
(.side 13 4 true (-1)),
(.side 15 2 true (0)),
(.side 20 3 false (-2)),
(.side 12 6 true (-1))])
theorem checked_21_18 : check 151 p_21_18 cert_21_18 = true := by decide +kernel
theorem safe_21_18 : ∀ m, compatible p_21_18 m → WeightedBound 151 m := sound 151 _ cert_21_18 (by decide) checked_21_18
def p_21_19 := refine p_21 (5,true) (some ⟨true,true,4⟩)
def cert_21_19 : Tree := (split 18 (4,false) 6 #[
(.side 17 13 true (-1)),
(.side 42 19 true (0)),
(.side 17 11 true (-1)),
(.side 40 17 true (0)),
(.side 17 17 true (-1)),
(.side 17 38 true (-1)),
(.side 21 1 true (1)),
(.side 17 50 true (-1)),
(.last 19 (2,true)),
(.last 40 (2,true)),
(.last 19 (2,true)),
(.side 2 17 true (-2)),
(.side 24 1 true (0)),
(.side 18 4 true (2)),
(.side 17 9 true (-1)),
(.side 4 15 true (-2)),
(.side 20 1 true (0)),
(.side 18 1 true (2)),
(.side 17 5 true (0)),
(.side 18 1 true (2)),
(.side 17 2 true (1)),
(.side 19 1 true (3)),
(.side 15 4 true (1)),
(.side 19 1 true (3))])
theorem checked_21_19 : check 151 p_21_19 cert_21_19 = true := by decide +kernel
theorem safe_21_19 : ∀ m, compatible p_21_19 m → WeightedBound 151 m := sound 151 _ cert_21_19 (by decide) checked_21_19
def p_21_20 := refine p_21 (5,true) (some ⟨false,false,5⟩)
def cert_21_20 : Tree := (.side 19 1 true (1))
theorem checked_21_20 : check 151 p_21_20 cert_21_20 = true := by decide +kernel
theorem safe_21_20 : ∀ m, compatible p_21_20 m → WeightedBound 151 m := sound 151 _ cert_21_20 (by decide) checked_21_20
def p_21_21 := refine p_21 (5,true) (some ⟨false,true,5⟩)
def cert_21_21 : Tree := (.side 17 1 true (3))
theorem checked_21_21 : check 151 p_21_21 cert_21_21 = true := by decide +kernel
theorem safe_21_21 : ∀ m, compatible p_21_21 m → WeightedBound 151 m := sound 151 _ cert_21_21 (by decide) checked_21_21
def p_21_22 := refine p_21 (5,true) (some ⟨true,false,5⟩)
def cert_21_22 : Tree := (.side 14 2 true (0))
theorem checked_21_22 : check 151 p_21_22 cert_21_22 = true := by decide +kernel
theorem safe_21_22 : ∀ m, compatible p_21_22 m → WeightedBound 151 m := sound 151 _ cert_21_22 (by decide) checked_21_22
def p_21_23 := refine p_21 (5,true) (some ⟨true,true,5⟩)
def cert_21_23 : Tree := (.side 17 1 true (3))
theorem checked_21_23 : check 151 p_21_23 cert_21_23 = true := by decide +kernel
theorem safe_21_23 : ∀ m, compatible p_21_23 m → WeightedBound 151 m := sound 151 _ cert_21_23 (by decide) checked_21_23
theorem safe_21 : ∀ m, compatible p_21 m → WeightedBound 151 m := by
  apply split_safe 151 p_21 15 (5,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_21_0 | exact safe_21_1 | exact safe_21_2 | exact safe_21_3 | exact safe_21_4 | exact safe_21_5 | exact safe_21_6 | exact safe_21_7 | exact safe_21_8 | exact safe_21_9 | exact safe_21_10 | exact safe_21_11 | exact safe_21_12 | exact safe_21_13 | exact safe_21_14 | exact safe_21_15 | exact safe_21_16 | exact safe_21_17 | exact safe_21_18 | exact safe_21_19 | exact safe_21_20 | exact safe_21_21 | exact safe_21_22 | exact safe_21_23
def p_22 := refine parent (5,false) (some ⟨true,false,5⟩)
def p_22_0 := refine p_22 (5,true) (some ⟨false,false,0⟩)
def cert_22_0 : Tree := (split 17 (2,true) 6 #[
(.side 3 15 false (2)),
(.last 77 (4,false)),
(.side 5 13 false (2)),
(.side 6 21 false (2)),
(.last 19 (4,false)),
(.last 21 (4,false)),
(.side 11 7 false (0)),
(.last 21 (4,false)),
(.side 0 21 false (2)),
(.side 0 60 true (-6)),
(.side 15 6 false (-1)),
(.side 6 17 false (2)),
(.side 7 11 false (1)),
(.side 3 21 false (2)),
(.side 7 11 false (1)),
(.side 6 15 false (2)),
(.side 0 20 false (2)),
(.last 18 (4,false)),
(.side 0 20 false (2)),
(.last 18 (4,false)),
(.side 7 15 false (1)),
(.side 7 17 false (1)),
(.side 7 15 false (1)),
(.side 3 17 false (2))])
theorem checked_22_0 : check 151 p_22_0 cert_22_0 = true := by decide +kernel
theorem safe_22_0 : ∀ m, compatible p_22_0 m → WeightedBound 151 m := sound 151 _ cert_22_0 (by decide) checked_22_0
def p_22_1 := refine p_22 (5,true) (some ⟨false,true,0⟩)
def cert_22_1 : Tree := (.side 7 11 false (1))
theorem checked_22_1 : check 151 p_22_1 cert_22_1 = true := by decide +kernel
theorem safe_22_1 : ∀ m, compatible p_22_1 m → WeightedBound 151 m := sound 151 _ cert_22_1 (by decide) checked_22_1
def p_22_2 := refine p_22 (5,true) (some ⟨true,false,0⟩)
def cert_22_2 : Tree := (.side 10 5 false (0))
theorem checked_22_2 : check 151 p_22_2 cert_22_2 = true := by decide +kernel
theorem safe_22_2 : ∀ m, compatible p_22_2 m → WeightedBound 151 m := sound 151 _ cert_22_2 (by decide) checked_22_2
def p_22_3 := refine p_22 (5,true) (some ⟨true,true,0⟩)
def cert_22_3 : Tree := (.side 3 12 false (2))
theorem checked_22_3 : check 151 p_22_3 cert_22_3 = true := by decide +kernel
theorem safe_22_3 : ∀ m, compatible p_22_3 m → WeightedBound 151 m := sound 151 _ cert_22_3 (by decide) checked_22_3
def p_22_4 := refine p_22 (5,true) (some ⟨false,false,1⟩)
def cert_22_4 : Tree := (.side 7 13 false (1))
theorem checked_22_4 : check 151 p_22_4 cert_22_4 = true := by decide +kernel
theorem safe_22_4 : ∀ m, compatible p_22_4 m → WeightedBound 151 m := sound 151 _ cert_22_4 (by decide) checked_22_4
def p_22_5 := refine p_22 (5,true) (some ⟨false,true,1⟩)
def cert_22_5 : Tree := (split 16 (4,false) 6 #[
(.last 19 (2,true)),
(.side 17 13 true (-1)),
(.side 29 3 true (1)),
(.side 5 12 true (-2)),
(.side 7 15 false (1)),
(.side 19 1 false (1)),
(.last 18 (2,true)),
(.side 1 22 true (-2)),
(.side 0 18 false (2)),
(.last 17 (2,true)),
(.last 20 (2,true)),
(.last 17 (2,true)),
(.side 7 16 false (1)),
(.side 33 4 true (1)),
(.side 9 8 true (-2)),
(.side 7 10 true (-2)),
(.side 16 1 false (0)),
(.side 18 1 false (0)),
(.side 16 1 false (0)),
(.last 20 (2,true)),
(.side 17 1 false (-1)),
(.side 20 1 false (4)),
(.side 17 1 false (-1)),
(.side 17 4 true (1))])
theorem checked_22_5 : check 151 p_22_5 cert_22_5 = true := by decide +kernel
theorem safe_22_5 : ∀ m, compatible p_22_5 m → WeightedBound 151 m := sound 151 _ cert_22_5 (by decide) checked_22_5
def p_22_6 := refine p_22 (5,true) (some ⟨true,false,1⟩)
def cert_22_6 : Tree := (split 16 (2,true) 6 #[
(.side 7 13 false (1)),
(.side 7 17 false (1)),
(.side 7 11 false (1)),
(.side 6 15 false (2)),
(.last 18 (4,false)),
(.last 18 (4,false)),
(.side 19 1 false (-3)),
(.last 18 (4,false)),
(.side 0 19 false (2)),
(.side 0 62 true (-6)),
(.side 16 6 false (-2)),
(.side 6 17 false (2)),
(.side 8 9 false (0)),
(.side 7 13 false (1)),
(.side 8 9 false (0)),
(.side 6 11 false (2)),
(.side 18 1 false (-4)),
(.side 12 5 false (0)),
(.side 18 1 false (-4)),
(.side 21 1 false (-3)),
(.side 14 3 false (-2)),
(.side 25 1 false (-3)),
(.side 14 3 false (-2)),
(.side 11 7 false (0))])
theorem checked_22_6 : check 151 p_22_6 cert_22_6 = true := by decide +kernel
theorem safe_22_6 : ∀ m, compatible p_22_6 m → WeightedBound 151 m := sound 151 _ cert_22_6 (by decide) checked_22_6
def p_22_7 := refine p_22 (5,true) (some ⟨true,true,1⟩)
def cert_22_7 : Tree := (split 16 (4,false) 6 #[
(.last 19 (2,true)),
(.side 17 13 true (-1)),
(.side 29 3 true (1)),
(.side 7 16 false (2)),
(.side 1 16 false (2)),
(.side 23 17 true (-2)),
(.last 18 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2),(true,6)],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty))]⟩),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.side 7 12 false (1)),
(.side 33 4 true (1)),
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 19 1 false (-3)),
(.side 48 1 true (0)),
(.side 19 1 false (-3)),
(.last 20 (2,true)),
(.side 13 4 true (-2)),
(.side 1 30 true (-2)),
(.side 11 8 true (-2)),
(.side 17 4 true (1))])
theorem checked_22_7 : check 151 p_22_7 cert_22_7 = true := by decide +kernel
theorem safe_22_7 : ∀ m, compatible p_22_7 m → WeightedBound 151 m := sound 151 _ cert_22_7 (by decide) checked_22_7
def p_22_8 := refine p_22 (5,true) (some ⟨false,false,2⟩)
def cert_22_8 : Tree := (.side 0 16 false (2))
theorem checked_22_8 : check 151 p_22_8 cert_22_8 = true := by decide +kernel
theorem safe_22_8 : ∀ m, compatible p_22_8 m → WeightedBound 151 m := sound 151 _ cert_22_8 (by decide) checked_22_8
def p_22_9 := refine p_22 (5,true) (some ⟨false,true,2⟩)
def cert_22_9 : Tree := (split 15 (2,true) 6 #[
(.side 0 16 false (2)),
(.side 0 22 true (-2)),
(.last 18 (4,false)),
(.last 57 (4,false)),
(.side 7 14 false (1)),
(.last 19 (4,false)),
(.side 20 1 false (-2)),
(.last 19 (4,false)),
(.side 0 17 false (2)),
(.side 0 52 true (-3)),
(.side 15 6 false (-1)),
(.side 7 13 false (1)),
(.last 19 (4,false)),
(.last 33 (4,false)),
(.side 9 7 false (0)),
(.side 7 11 false (1)),
(.last 16 (4,false)),
(.last 16 (4,false)),
(.last 16 (4,false)),
(.last 16 (4,false)),
(.side 16 1 false (-2)),
(.side 16 1 false (0)),
(.side 16 1 false (-2)),
(.side 19 3 true (1))])
theorem checked_22_9 : check 151 p_22_9 cert_22_9 = true := by decide +kernel
theorem safe_22_9 : ∀ m, compatible p_22_9 m → WeightedBound 151 m := sound 151 _ cert_22_9 (by decide) checked_22_9
def p_22_10 := refine p_22 (5,true) (some ⟨true,false,2⟩)
def cert_22_10 : Tree := (split 18 (2,true) 6 #[
(.side 3 16 false (2)),
(.side 4 20 false (2)),
(.side 5 14 false (2)),
(.side 6 18 false (2)),
(.last 20 (4,false)),
(.last 20 (4,false)),
(.side 11 8 false (0)),
(.last 20 (4,false)),
(.side 0 22 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6),(false,4)],[(true,2),(true,6),(true,4)],[(false,3),(false,7),(false,5)],[(true,3),(true,7),(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),.empty,(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch .empty (.branch (.branch .empty .leaf) .leaf)))),(.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))))]⟩),
(.side 15 6 false (-2)),
(.side 6 20 false (2)),
(.side 7 12 false (1)),
(.side 4 16 false (2)),
(.side 7 12 false (1)),
(.side 6 14 false (2)),
(.side 14 6 false (-2)),
(.side 24 1 false (-4)),
(.side 14 6 false (-2)),
(.last 31 (4,false)),
(.side 21 1 false (-5)),
(.side 2 18 false (2)),
(.side 21 1 false (-5)),
(.side 18 2 true (-2))])
theorem checked_22_10 : check 151 p_22_10 cert_22_10 = true := by decide +kernel
theorem safe_22_10 : ∀ m, compatible p_22_10 m → WeightedBound 151 m := sound 151 _ cert_22_10 (by decide) checked_22_10
def p_22_11 := refine p_22 (5,true) (some ⟨true,true,2⟩)
def cert_22_11 : Tree := (split 15 (2,true) 6 #[
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[],[(true,2),(true,8)],[],[(true,7)],[(false,4)],[(true,4)],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,4),(5,14),(3,15),(7,16),(17,10),(18,6),(3,19),(7,20),(13,11),(12,14),(21,10),(7,22),(13,15),(18,14),(13,19)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),.empty,(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)),(.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))))]⟩),
(.side 7 10 false (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0),(false,1)],[(true,0),(true,1)],[],[(true,2),(true,8)],[],[(true,7)],[(false,4)],[(true,4)],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,4),(5,14),(3,15),(7,16),(17,10),(18,6),(3,19),(7,20),(13,11),(12,14),(21,10),(7,22),(13,15),(18,14),(13,19)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty),(.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),(.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)),.empty,(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)),(.branch .empty (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch .empty (.branch (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty) (.branch .leaf (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .empty)]⟩),
(.last 17 (4,false)),
(.last 19 (4,false)),
(.side 18 1 false (-2)),
(.last 19 (4,false)),
(.side 0 18 false (2)),
(.side 0 54 true (-4)),
(.side 15 6 false (-1)),
(.side 2 14 false (2)),
(.side 8 8 false (0)),
(.last 33 (4,false)),
(.side 8 8 false (0)),
(.side 4 12 false (2)),
(.side 17 1 false (-3)),
(.last 16 (4,false)),
(.side 17 1 false (-3)),
(.last 16 (4,false)),
(.side 7 14 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2),(true,6)],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),.empty,(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))))]⟩),
(.side 14 2 true (-2)),
(.side 19 3 true (1))])
theorem checked_22_11 : check 151 p_22_11 cert_22_11 = true := by decide +kernel
theorem safe_22_11 : ∀ m, compatible p_22_11 m → WeightedBound 151 m := sound 151 _ cert_22_11 (by decide) checked_22_11
def p_22_12 := refine p_22 (5,true) (some ⟨false,false,3⟩)
def cert_22_12 : Tree := (split 18 (4,false) 6 #[
(.last 21 (2,true)),
(.side 8 22 false (0)),
(.side 8 16 false (0)),
(.side 7 20 false (1)),
(.side 1 18 false (2)),
(.side 25 10 false (-1)),
(.last 20 (2,true)),
(.side 7 24 false (2)),
(.side 7 16 false (1)),
(.last 19 (2,true)),
(.side 7 16 false (1)),
(.last 19 (2,true)),
(.side 7 14 false (1)),
(.side 8 18 false (0)),
(.side 7 14 false (1)),
(.side 7 16 false (1)),
(.side 21 1 false (-5)),
(.side 13 8 false (-1)),
(.side 21 1 false (-5)),
(.side 7 16 false (1)),
(.side 13 6 false (-1)),
(.side 8 20 false (0)),
(.side 13 6 false (-1)),
(.side 7 16 false (1))])
theorem checked_22_12 : check 151 p_22_12 cert_22_12 = true := by decide +kernel
theorem safe_22_12 : ∀ m, compatible p_22_12 m → WeightedBound 151 m := sound 151 _ cert_22_12 (by decide) checked_22_12
def p_22_13 := refine p_22 (5,true) (some ⟨false,true,3⟩)
def cert_22_13 : Tree := (.side 8 7 false (0))
theorem checked_22_13 : check 151 p_22_13 cert_22_13 = true := by decide +kernel
theorem safe_22_13 : ∀ m, compatible p_22_13 m → WeightedBound 151 m := sound 151 _ cert_22_13 (by decide) checked_22_13
def p_22_14 := refine p_22 (5,true) (some ⟨true,false,3⟩)
def cert_22_14 : Tree := (.side 9 6 false (0))
theorem checked_22_14 : check 151 p_22_14 cert_22_14 = true := by decide +kernel
theorem safe_22_14 : ∀ m, compatible p_22_14 m → WeightedBound 151 m := sound 151 _ cert_22_14 (by decide) checked_22_14
def p_22_15 := refine p_22 (5,true) (some ⟨true,true,3⟩)
def cert_22_15 : Tree := (.side 7 8 false (1))
theorem checked_22_15 : check 151 p_22_15 cert_22_15 = true := by decide +kernel
theorem safe_22_15 : ∀ m, compatible p_22_15 m → WeightedBound 151 m := sound 151 _ cert_22_15 (by decide) checked_22_15
def p_22_16 := refine p_22 (5,true) (some ⟨false,false,4⟩)
def cert_22_16 : Tree := (split 15 (4,false) 6 #[
(.side 0 16 false (2)),
(.side 29 1 false (-3)),
(.side 25 1 false (-5)),
(.side 4 19 false (2)),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.last 17 (2,true)),
(.last 17 (2,true)),
(.side 0 17 false (2)),
(.last 19 (2,true)),
(.last 19 (2,true)),
(.side 7 13 false (1)),
(.side 7 15 false (1)),
(.side 9 7 false (0)),
(.side 9 7 false (0)),
(.side 7 11 false (1)),
(.side 15 1 false (-3)),
(.side 18 1 false (-2)),
(.side 15 1 false (-3)),
(.side 20 1 false (-4)),
(.side 16 1 false (-4)),
(.side 16 1 false (-2)),
(.side 16 1 false (-4)),
(.side 13 3 false (-1))])
theorem checked_22_16 : check 151 p_22_16 cert_22_16 = true := by decide +kernel
theorem safe_22_16 : ∀ m, compatible p_22_16 m → WeightedBound 151 m := sound 151 _ cert_22_16 (by decide) checked_22_16
def p_22_17 := refine p_22 (5,true) (some ⟨false,true,4⟩)
def cert_22_17 : Tree := (.side 16 1 false (-2))
theorem checked_22_17 : check 151 p_22_17 cert_22_17 = true := by decide +kernel
theorem safe_22_17 : ∀ m, compatible p_22_17 m → WeightedBound 151 m := sound 151 _ cert_22_17 (by decide) checked_22_17
def p_22_18 := refine p_22 (5,true) (some ⟨true,false,4⟩)
def cert_22_18 : Tree := (split 15 (4,false) 6 #[
(.last 18 (2,true)),
(.side 7 10 false (1)),
(.side 10 6 false (0)),
(.side 5 11 false (2)),
(.side 7 14 false (1)),
(.side 18 1 false (-2)),
(.last 17 (2,true)),
(.side 11 5 false (0)),
(.side 0 17 false (2)),
(.last 16 (2,true)),
(.last 19 (2,true)),
(.last 16 (2,true)),
(.side 7 15 false (1)),
(.side 8 8 false (0)),
(.side 9 7 false (0)),
(.side 7 9 false (1)),
(.side 15 1 false (-3)),
(.side 17 1 false (-3)),
(.side 15 1 false (-3)),
(.side 14 3 false (-2)),
(.side 16 1 false (-4)),
(.side 14 2 true (-3)),
(.side 16 1 false (-4)),
(.side 18 1 false (-4))])
theorem checked_22_18 : check 151 p_22_18 cert_22_18 = true := by decide +kernel
theorem safe_22_18 : ∀ m, compatible p_22_18 m → WeightedBound 151 m := sound 151 _ cert_22_18 (by decide) checked_22_18
def p_22_19 := refine p_22 (5,true) (some ⟨true,true,4⟩)
def cert_22_19 : Tree := (split 17 (4,false) 6 #[
(.side 7 14 false (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3),(true,5),(true,4)],[(false,2),(false,4)],[(true,2)],[(false,3)]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[(true,2),(true,6)],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) .empty),.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))) .empty) (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))) .empty))]⟩),
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[(true,2),(true,6)],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty))]⟩),
(.side 7 18 false (1)),
(.last 19 (2,true)),
(.side 20 1 false (-2)),
(.last 19 (2,true)),
(.last 18 (2,true)),
(.last 21 (2,true)),
(.last 18 (2,true)),
(.side 2 16 false (2)),
(.side 8 10 false (0)),
(.side 35 4 true (1)),
(.side 8 10 false (0)),
(.side 4 14 false (2)),
(.side 19 1 false (-3)),
(.side 61 1 true (-1)),
(.side 19 1 false (-3)),
(.side 24 1 true (2)),
(.side 16 2 true (-2)),
(.side 24 8 true (0)),
(.side 14 4 true (-2)),
(.side 23 5 true (1))])
theorem checked_22_19 : check 151 p_22_19 cert_22_19 = true := by decide +kernel
theorem safe_22_19 : ∀ m, compatible p_22_19 m → WeightedBound 151 m := sound 151 _ cert_22_19 (by decide) checked_22_19
def p_22_20 := refine p_22 (5,true) (some ⟨false,false,5⟩)
def cert_22_20 : Tree := (.side 15 1 false (-3))
theorem checked_22_20 : check 151 p_22_20 cert_22_20 = true := by decide +kernel
theorem safe_22_20 : ∀ m, compatible p_22_20 m → WeightedBound 151 m := sound 151 _ cert_22_20 (by decide) checked_22_20
def p_22_21 := refine p_22 (5,true) (some ⟨false,true,5⟩)
def cert_22_21 : Tree := (.side 16 1 false (0))
theorem checked_22_21 : check 151 p_22_21 cert_22_21 = true := by decide +kernel
theorem safe_22_21 : ∀ m, compatible p_22_21 m → WeightedBound 151 m := sound 151 _ cert_22_21 (by decide) checked_22_21
def p_22_22 := refine p_22 (5,true) (some ⟨true,false,5⟩)
def cert_22_22 : Tree := (.side 15 1 false (-3))
theorem checked_22_22 : check 151 p_22_22 cert_22_22 = true := by decide +kernel
theorem safe_22_22 : ∀ m, compatible p_22_22 m → WeightedBound 151 m := sound 151 _ cert_22_22 (by decide) checked_22_22
def p_22_23 := refine p_22 (5,true) (some ⟨true,true,5⟩)
def cert_22_23 : Tree := (.side 19 3 true (1))
theorem checked_22_23 : check 151 p_22_23 cert_22_23 = true := by decide +kernel
theorem safe_22_23 : ∀ m, compatible p_22_23 m → WeightedBound 151 m := sound 151 _ cert_22_23 (by decide) checked_22_23
theorem safe_22 : ∀ m, compatible p_22 m → WeightedBound 151 m := by
  apply split_safe 151 p_22 14 (5,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_22_0 | exact safe_22_1 | exact safe_22_2 | exact safe_22_3 | exact safe_22_4 | exact safe_22_5 | exact safe_22_6 | exact safe_22_7 | exact safe_22_8 | exact safe_22_9 | exact safe_22_10 | exact safe_22_11 | exact safe_22_12 | exact safe_22_13 | exact safe_22_14 | exact safe_22_15 | exact safe_22_16 | exact safe_22_17 | exact safe_22_18 | exact safe_22_19 | exact safe_22_20 | exact safe_22_21 | exact safe_22_22 | exact safe_22_23
def p_23 := refine parent (5,false) (some ⟨true,true,5⟩)
def p_23_0 := refine p_23 (5,true) (some ⟨false,false,0⟩)
def cert_23_0 : Tree := (.side 6 14 false (2))
theorem checked_23_0 : check 151 p_23_0 cert_23_0 = true := by decide +kernel
theorem safe_23_0 : ∀ m, compatible p_23_0 m → WeightedBound 151 m := sound 151 _ cert_23_0 (by decide) checked_23_0
def p_23_1 := refine p_23 (5,true) (some ⟨false,true,0⟩)
def cert_23_1 : Tree := (.side 18 16 false (3))
theorem checked_23_1 : check 151 p_23_1 cert_23_1 = true := by decide +kernel
theorem safe_23_1 : ∀ m, compatible p_23_1 m → WeightedBound 151 m := sound 151 _ cert_23_1 (by decide) checked_23_1
def p_23_2 := refine p_23 (5,true) (some ⟨true,false,0⟩)
def cert_23_2 : Tree := (.side 6 12 false (2))
theorem checked_23_2 : check 151 p_23_2 cert_23_2 = true := by decide +kernel
theorem safe_23_2 : ∀ m, compatible p_23_2 m → WeightedBound 151 m := sound 151 _ cert_23_2 (by decide) checked_23_2
def p_23_3 := refine p_23 (5,true) (some ⟨true,true,0⟩)
def cert_23_3 : Tree := (.side 18 14 false (3))
theorem checked_23_3 : check 151 p_23_3 cert_23_3 = true := by decide +kernel
theorem safe_23_3 : ∀ m, compatible p_23_3 m → WeightedBound 151 m := sound 151 _ cert_23_3 (by decide) checked_23_3
def p_23_4 := refine p_23 (5,true) (some ⟨false,false,1⟩)
def cert_23_4 : Tree := (split 17 (4,false) 6 #[
(.last 20 (2,true)),
(.side 0 32 true (-2)),
(.side 21 1 true (1)),
(.side 20 18 false (3)),
(.side 6 18 false (2)),
(.side 18 16 true (2)),
(.last 19 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 2 16 false (2)),
(.last 18 (2,true)),
(.side 2 16 false (2)),
(.last 18 (2,true)),
(.side 4 14 false (2)),
(.side 23 1 true (1)),
(.side 4 14 false (2)),
(.side 4 16 false (2)),
(.side 7 19 false (1)),
(.side 19 1 true (1)),
(.side 7 19 false (1)),
(.side 6 20 false (2)),
(.side 23 1 true (1)),
(.side 4 22 false (2)),
(.side 14 4 true (0)),
(.side 21 1 true (3))])
theorem checked_23_4 : check 151 p_23_4 cert_23_4 = true := by decide +kernel
theorem safe_23_4 : ∀ m, compatible p_23_4 m → WeightedBound 151 m := sound 151 _ cert_23_4 (by decide) checked_23_4
def p_23_5 := refine p_23 (5,true) (some ⟨false,true,1⟩)
def cert_23_5 : Tree := (split 17 (4,false) 6 #[
(.side 47 1 true (3)),
(.side 0 18 true (-2)),
(.side 16 3 true (2)),
(.side 37 1 true (5)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 70 1 true (6)),
(.last 19 (2,true)),
(.side 1 17 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 0 19 true (-2)),
(.last 21 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 16 4 true (2)),
(.side 22 1 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 42 1 true (0)),
(.side 17 1 true (3)),
(.last 23 (2,true)),
(.side 17 1 true (3)),
(.side 18 1 true (2)),
(.side 18 1 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 18 1 true (4))])
theorem checked_23_5 : check 151 p_23_5 cert_23_5 = true := by decide +kernel
theorem safe_23_5 : ∀ m, compatible p_23_5 m → WeightedBound 151 m := sound 151 _ cert_23_5 (by decide) checked_23_5
def p_23_6 := refine p_23 (5,true) (some ⟨true,false,1⟩)
def cert_23_6 : Tree := (.side 23 1 true (1))
theorem checked_23_6 : check 151 p_23_6 cert_23_6 = true := by decide +kernel
theorem safe_23_6 : ∀ m, compatible p_23_6 m → WeightedBound 151 m := sound 151 _ cert_23_6 (by decide) checked_23_6
def p_23_7 := refine p_23 (5,true) (some ⟨true,true,1⟩)
def cert_23_7 : Tree := (split 17 (4,false) 6 #[
(.side 45 1 true (3)),
(.side 0 18 true (-2)),
(.side 16 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 66 1 true (6)),
(.last 19 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 45 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 16 4 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 43 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 17 1 true (3)),
(.last 22 (2,true)),
(.side 17 1 true (3)),
(.side 18 1 true (2)),
(.side 18 1 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 18 1 true (4))])
theorem checked_23_7 : check 151 p_23_7 cert_23_7 = true := by decide +kernel
theorem safe_23_7 : ∀ m, compatible p_23_7 m → WeightedBound 151 m := sound 151 _ cert_23_7 (by decide) checked_23_7
def p_23_8 := refine p_23 (5,true) (some ⟨false,false,2⟩)
def cert_23_8 : Tree := (split 16 (2,true) 6 #[
(.side 3 14 false (2)),
(.last 19 (4,false)),
(.side 5 12 false (2)),
(.last 19 (4,false)),
(.last 18 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[(false,3)],[(true,3)],[],[],[(false,13)],[(true,13)],[(false,10)],[(true,6),(true,10)],[],[(true,7),(true,15),(true,11)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,2)],[(true,2)],[],[],[(false,4)],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,2),(3,8),(3,9),(10,6),(3,11),(7,6),(7,8),(7,8)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty .leaf)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) .empty)) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty .leaf))) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .leaf) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch .empty .leaf))) .empty),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty .leaf))) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))))),(.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) .empty))) .empty)]⟩),
(.side 26 1 true (0)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,2)],[(true,2)],[],[],[(false,4)],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,2),(3,8),(3,9),(10,6),(3,11),(7,6),(7,8),(7,8)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .leaf) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .leaf (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty)]⟩),
(.side 0 20 false (2)),
(.side 0 52 true (-4)),
(.side 16 6 false (0)),
(.side 6 16 false (2)),
(.side 7 10 false (1)),
(.side 21 1 true (1)),
(.side 7 10 false (1)),
(.side 6 14 false (2)),
(.side 0 20 false (2)),
(.last 17 (4,false)),
(.side 0 20 false (2)),
(.last 17 (4,false)),
(.side 30 1 true (-4)),
(.side 20 1 true (2)),
(.side 17 3 false (-1)),
(.side 20 1 true (2))])
theorem checked_23_8 : check 151 p_23_8 cert_23_8 = true := by decide +kernel
theorem safe_23_8 : ∀ m, compatible p_23_8 m → WeightedBound 151 m := sound 151 _ cert_23_8 (by decide) checked_23_8
def p_23_9 := refine p_23 (5,true) (some ⟨false,true,2⟩)
def cert_23_9 : Tree := (split 16 (2,true) 6 #[
(.side 20 20 false (3)),
(.side 0 17 true (-2)),
(.last 19 (4,false)),
(.side 24 18 false (4)),
(.side 6 18 false (2)),
(.side 63 1 true (5)),
(.side 21 1 true (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4),(true,3)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,4)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)]⟩),
(.side 6 16 false (2)),
(.side 0 46 true (-4)),
(.side 6 16 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .empty .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 6 14 false (2)),
(.last 20 (4,false)),
(.side 6 14 false (2)),
(.side 19 16 false (3)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.last 17 (4,false)),
(.side 17 1 true (1)),
(.side 17 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 17 1 true (3))])
theorem checked_23_9 : check 151 p_23_9 cert_23_9 = true := by decide +kernel
theorem safe_23_9 : ∀ m, compatible p_23_9 m → WeightedBound 151 m := sound 151 _ cert_23_9 (by decide) checked_23_9
def p_23_10 := refine p_23 (5,true) (some ⟨true,false,2⟩)
def cert_23_10 : Tree := (split 16 (2,true) 6 #[
(.side 3 14 false (2)),
(.side 4 16 false (2)),
(.side 5 12 false (2)),
(.side 6 14 false (2)),
(.last 18 (4,false)),
(.side 19 1 true (1)),
(.side 11 6 true (-1)),
(.side 19 1 true (1)),
(.side 0 20 false (2)),
(.side 0 20 true (-2)),
(.side 16 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 7 10 false (1)),
(.side 4 14 false (2)),
(.side 7 10 false (1)),
(.side 6 12 false (2)),
(.side 16 6 false (0)),
(.side 23 1 true (1)),
(.side 16 6 false (0)),
(.last 29 (4,false)),
(.side 16 11 false (0)),
(.side 2 16 false (2)),
(.side 17 3 false (-1)),
(.side 15 2 true (0))])
theorem checked_23_10 : check 151 p_23_10 cert_23_10 = true := by decide +kernel
theorem safe_23_10 : ∀ m, compatible p_23_10 m → WeightedBound 151 m := sound 151 _ cert_23_10 (by decide) checked_23_10
def p_23_11 := refine p_23 (5,true) (some ⟨true,true,2⟩)
def cert_23_11 : Tree := (split 16 (2,true) 6 #[
(.side 6 16 false (2)),
(.side 24 18 false (4)),
(.side 6 14 false (2)),
(.side 24 16 false (4)),
(.last 18 (4,false)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0)],[(false,2)],[(true,2),(true,8)],[],[(true,7),(true,13)],[(false,4)],[(true,4)],[],[],[(true,6),(true,16)],[(false,7)],[(false,16)],[],[],[(true,11)],[],[(false,13)],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,4),(5,14),(3,15),(7,16),(17,10),(18,6),(3,19),(7,20),(13,11),(12,14),(21,10),(7,22),(13,15),(18,14),(13,19)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,4)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))),(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf))) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch .empty .leaf))) .leaf) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty .leaf))) .empty),.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .empty) .empty))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) .empty)]⟩),
(.side 19 1 true (1)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,4)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[(false,4)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .empty) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .leaf) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf)))),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)]⟩),
(.side 0 22 false (2)),
(.side 0 44 true (-4)),
(.side 18 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 6 12 false (2)),
(.last 20 (4,false)),
(.side 6 12 false (2)),
(.side 19 14 false (3)),
(.side 6 18 false (2)),
(.last 17 (4,false)),
(.side 6 18 false (2)),
(.last 17 (4,false)),
(.side 6 18 false (2)),
(.side 17 1 true (3)),
(.side 15 2 true (1)),
(.side 17 1 true (3))])
theorem checked_23_11 : check 151 p_23_11 cert_23_11 = true := by decide +kernel
theorem safe_23_11 : ∀ m, compatible p_23_11 m → WeightedBound 151 m := sound 151 _ cert_23_11 (by decide) checked_23_11
def p_23_12 := refine p_23 (5,true) (some ⟨false,false,3⟩)
def cert_23_12 : Tree := (.side 6 10 false (2))
theorem checked_23_12 : check 151 p_23_12 cert_23_12 = true := by decide +kernel
theorem safe_23_12 : ∀ m, compatible p_23_12 m → WeightedBound 151 m := sound 151 _ cert_23_12 (by decide) checked_23_12
def p_23_13 := refine p_23 (5,true) (some ⟨false,true,3⟩)
def cert_23_13 : Tree := (.side 6 14 false (2))
theorem checked_23_13 : check 151 p_23_13 cert_23_13 = true := by decide +kernel
theorem safe_23_13 : ∀ m, compatible p_23_13 m → WeightedBound 151 m := sound 151 _ cert_23_13 (by decide) checked_23_13
def p_23_14 := refine p_23 (5,true) (some ⟨true,false,3⟩)
def cert_23_14 : Tree := (.side 6 10 false (2))
theorem checked_23_14 : check 151 p_23_14 cert_23_14 = true := by decide +kernel
theorem safe_23_14 : ∀ m, compatible p_23_14 m → WeightedBound 151 m := sound 151 _ cert_23_14 (by decide) checked_23_14
def p_23_15 := refine p_23 (5,true) (some ⟨true,true,3⟩)
def cert_23_15 : Tree := (.side 6 12 false (2))
theorem checked_23_15 : check 151 p_23_15 cert_23_15 = true := by decide +kernel
theorem safe_23_15 : ∀ m, compatible p_23_15 m → WeightedBound 151 m := sound 151 _ cert_23_15 (by decide) checked_23_15
def p_23_16 := refine p_23 (5,true) (some ⟨false,false,4⟩)
def cert_23_16 : Tree := (.side 30 1 true (-4))
theorem checked_23_16 : check 151 p_23_16 cert_23_16 = true := by decide +kernel
theorem safe_23_16 : ∀ m, compatible p_23_16 m → WeightedBound 151 m := sound 151 _ cert_23_16 (by decide) checked_23_16
def p_23_17 := refine p_23 (5,true) (some ⟨false,true,4⟩)
def cert_23_17 : Tree := (.side 17 1 true (1))
theorem checked_23_17 : check 151 p_23_17 cert_23_17 = true := by decide +kernel
theorem safe_23_17 : ∀ m, compatible p_23_17 m → WeightedBound 151 m := sound 151 _ cert_23_17 (by decide) checked_23_17
def p_23_18 := refine p_23 (5,true) (some ⟨true,false,4⟩)
def cert_23_18 : Tree := (split 24 (4,false) 6 #[
(.last 27 (2,true)),
(.side 7 21 false (1)),
(.side 21 12 false (-1)),
(.side 3 22 false (2)),
(.side 7 23 false (1)),
(.side 31 1 true (1)),
(.last 26 (2,true)),
(.side 31 1 true (1)),
(.side 0 26 false (2)),
(.last 25 (2,true)),
(.last 28 (2,true)),
(.last 25 (2,true)),
(.side 7 24 false (1)),
(.side 21 14 false (-1)),
(.side 9 16 false (1)),
(.side 7 18 false (1)),
(.side 24 1 false (-4)),
(.side 13 14 false (1)),
(.side 24 1 false (-4)),
(.side 22 3 false (-2)),
(.side 19 6 false (-1)),
(.side 23 2 true (-4)),
(.side 17 9 false (-1)),
(.side 17 8 false (-1))])
theorem checked_23_18 : check 151 p_23_18 cert_23_18 = true := by decide +kernel
theorem safe_23_18 : ∀ m, compatible p_23_18 m → WeightedBound 151 m := sound 151 _ cert_23_18 (by decide) checked_23_18
def p_23_19 := refine p_23 (5,true) (some ⟨true,true,4⟩)
def cert_23_19 : Tree := (split 18 (4,false) 6 #[
(.side 6 18 false (2)),
(.side 26 20 false (4)),
(.side 6 16 false (2)),
(.side 26 18 false (4)),
(.side 6 22 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.side 21 1 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf .leaf),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf))]⟩),
(.last 19 (2,true)),
(.last 43 (2,true)),
(.last 19 (2,true)),
(.last 39 (2,true)),
(.side 6 14 false (2)),
(.side 18 4 true (2)),
(.side 6 14 false (2)),
(.side 21 16 false (3)),
(.side 29 1 true (-3)),
(.side 18 1 true (2)),
(.side 19 13 false (1)),
(.side 18 1 true (2)),
(.side 17 2 true (1)),
(.side 19 1 true (3)),
(.side 15 4 true (1)),
(.side 19 1 true (3))])
theorem checked_23_19 : check 151 p_23_19 cert_23_19 = true := by decide +kernel
theorem safe_23_19 : ∀ m, compatible p_23_19 m → WeightedBound 151 m := sound 151 _ cert_23_19 (by decide) checked_23_19
def p_23_20 := refine p_23 (5,true) (some ⟨false,false,5⟩)
def cert_23_20 : Tree := (.side 30 1 true (-4))
theorem checked_23_20 : check 151 p_23_20 cert_23_20 = true := by decide +kernel
theorem safe_23_20 : ∀ m, compatible p_23_20 m → WeightedBound 151 m := sound 151 _ cert_23_20 (by decide) checked_23_20
def p_23_21 := refine p_23 (5,true) (some ⟨false,true,5⟩)
def cert_23_21 : Tree := (.side 17 1 true (3))
theorem checked_23_21 : check 151 p_23_21 cert_23_21 = true := by decide +kernel
theorem safe_23_21 : ∀ m, compatible p_23_21 m → WeightedBound 151 m := sound 151 _ cert_23_21 (by decide) checked_23_21
def p_23_22 := refine p_23 (5,true) (some ⟨true,false,5⟩)
def cert_23_22 : Tree := (.side 17 3 false (-1))
theorem checked_23_22 : check 151 p_23_22 cert_23_22 = true := by decide +kernel
theorem safe_23_22 : ∀ m, compatible p_23_22 m → WeightedBound 151 m := sound 151 _ cert_23_22 (by decide) checked_23_22
def p_23_23 := refine p_23 (5,true) (some ⟨true,true,5⟩)
def cert_23_23 : Tree := (.side 17 1 true (3))
theorem checked_23_23 : check 151 p_23_23 cert_23_23 = true := by decide +kernel
theorem safe_23_23 : ∀ m, compatible p_23_23 m → WeightedBound 151 m := sound 151 _ cert_23_23 (by decide) checked_23_23
theorem safe_23 : ∀ m, compatible p_23 m → WeightedBound 151 m := by
  apply split_safe 151 p_23 15 (5,true) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_23_0 | exact safe_23_1 | exact safe_23_2 | exact safe_23_3 | exact safe_23_4 | exact safe_23_5 | exact safe_23_6 | exact safe_23_7 | exact safe_23_8 | exact safe_23_9 | exact safe_23_10 | exact safe_23_11 | exact safe_23_12 | exact safe_23_13 | exact safe_23_14 | exact safe_23_15 | exact safe_23_16 | exact safe_23_17 | exact safe_23_18 | exact safe_23_19 | exact safe_23_20 | exact safe_23_21 | exact safe_23_22 | exact safe_23_23
theorem safe : ∀ m, compatible parent m → WeightedBound 151 m := by
  apply split_safe 151 parent 13 (5,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_0 | exact safe_1 | exact safe_2 | exact safe_3 | exact safe_4 | exact safe_5 | exact safe_6 | exact safe_7 | exact safe_8 | exact safe_9 | exact safe_10 | exact safe_11 | exact safe_12 | exact safe_13 | exact safe_14 | exact safe_15 | exact safe_16 | exact safe_17 | exact safe_18 | exact safe_19 | exact safe_20 | exact safe_21 | exact safe_22 | exact safe_23
theorem cover : Cover (WeightedBound 151) parent := .leaf _ safe
#print axioms safe
#print axioms cover
end BB6.Agent47Root48
