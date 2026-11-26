import Root51LeanBase
set_option maxHeartbeats 0
set_option maxRecDepth 100000
namespace BB6.Agent47Root51
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def p_0 := refine parent (5,true) (some ⟨false,false,0⟩)
def cert_0 : Tree := (.side 7 14 false (1))
theorem checked_0 : check 208 p_0 cert_0 = true := by decide +kernel
theorem safe_0 : ∀ m, compatible p_0 m → WeightedBound 208 m := sound 208 _ cert_0 (by decide) checked_0
def p_1 := refine parent (5,true) (some ⟨false,true,0⟩)
def cert_1 : Tree := (.side 16 16 false (3))
theorem checked_1 : check 208 p_1 cert_1 = true := by decide +kernel
theorem safe_1 : ∀ m, compatible p_1 m → WeightedBound 208 m := sound 208 _ cert_1 (by decide) checked_1
def p_2 := refine parent (5,true) (some ⟨true,false,0⟩)
def cert_2 : Tree := (.side 7 12 false (1))
theorem checked_2 : check 208 p_2 cert_2 = true := by decide +kernel
theorem safe_2 : ∀ m, compatible p_2 m → WeightedBound 208 m := sound 208 _ cert_2 (by decide) checked_2
def p_3 := refine parent (5,true) (some ⟨true,true,0⟩)
def cert_3 : Tree := (.side 16 14 false (3))
theorem checked_3 : check 208 p_3 cert_3 = true := by decide +kernel
theorem safe_3 : ∀ m, compatible p_3 m → WeightedBound 208 m := sound 208 _ cert_3 (by decide) checked_3
def p_4 := refine parent (5,true) (some ⟨false,false,1⟩)
def p_4_0 := refine p_4 (4,false) (some ⟨false,false,0⟩)
def cert_4_0 : Tree := (split 18 (2,true) 6 #[
(.side 7 20 false (2)),
(.side 26 22 false (4)),
(.side 7 18 false (2)),
(.side 26 20 false (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)))),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))))]⟩),
(.last 77 (5,false)),
(.last 21 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[],[],[],[],[],[(true,5)],[],[],[],[],[],[],[],[],[],[],[],[(true,11),(true,27)],[],[],[],[(true,29)],[(false,30)],[(true,30)],[(false,23)],[(true,23)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31),(16,17),(18,19),(20,21),(22,23),(24,25),(26,27),(28,29),(30,31)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,8)],[(false,2)],[(true,2)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .leaf .leaf)) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf))) .empty) .empty)) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)))),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty .leaf)) .empty)) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty))))),(.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty .leaf)))) .empty),(.branch (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) .empty)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .empty .leaf)) (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))) (.branch .empty .leaf))) (.branch (.branch .leaf (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .leaf .leaf))) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty .leaf)) .empty) .empty) .empty),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch .empty .leaf)) .empty)) .empty) .empty)]⟩),
(.side 7 38 false (2)),
(.side 0 50 true (-4)),
(.side 7 18 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)))),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))))]⟩),
(.side 7 16 false (2)),
(.side 32 20 false (2)),
(.side 7 16 false (2)),
(.side 21 18 false (3)),
(.last 20 (5,false)),
(.last 53 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)))),(.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))))]⟩),
(.automata ⟨⟨#[[(false,0)],[],[(true,0)],[(false,2)],[(true,2)],[(false,3)],[(true,3),(true,16)],[],[],[],[],[(true,6)],[],[(false,16)],[],[],[(true,11)],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,2),(3,14),(3,15),(7,16),(17,10),(18,6),(3,19),(7,20),(13,6),(7,14),(21,10),(7,22),(13,10),(13,14),(13,14)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,8)],[(true,2),(true,8)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,4),(5,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .leaf) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf))) (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf))) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf))) .empty)) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty)]⟩),
(.side 7 26 false (2)),
(.last 19 (5,false)),
(.side 13 6 true (0)),
(.last 19 (5,false))])
theorem checked_4_0 : check 208 p_4_0 cert_4_0 = true := by decide +kernel
theorem safe_4_0 : ∀ m, compatible p_4_0 m → WeightedBound 208 m := sound 208 _ cert_4_0 (by decide) checked_4_0
def p_4_1 := refine p_4 (4,false) (some ⟨false,true,0⟩)
def cert_4_1 : Tree := (.side 0 28 true (-2))
theorem checked_4_1 : check 208 p_4_1 cert_4_1 = true := by decide +kernel
theorem safe_4_1 : ∀ m, compatible p_4_1 m → WeightedBound 208 m := sound 208 _ cert_4_1 (by decide) checked_4_1
def p_4_2 := refine p_4 (4,false) (some ⟨true,false,0⟩)
def cert_4_2 : Tree := (split 19 (5,false) 6 #[
(.side 50 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 48 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 20 3 true (2)),
(.side 62 3 true (4)),
(.side 17 3 true (1)),
(.side 60 3 true (4)),
(.last 20 (2,true)),
(.side 62 3 true (4)),
(.last 20 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 21 3 true (3)),
(.side 46 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 18 2 true (2)),
(.side 20 3 true (3)),
(.side 22 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf))]⟩),
(.side 19 1 true (3)),
(.side 50 3 true (2)),
(.side 19 1 true (3))])
theorem checked_4_2 : check 208 p_4_2 cert_4_2 = true := by decide +kernel
theorem safe_4_2 : ∀ m, compatible p_4_2 m → WeightedBound 208 m := sound 208 _ cert_4_2 (by decide) checked_4_2
def p_4_3 := refine p_4 (4,false) (some ⟨true,true,0⟩)
def cert_4_3 : Tree := (.side 3 13 true (-2))
theorem checked_4_3 : check 208 p_4_3 cert_4_3 = true := by decide +kernel
theorem safe_4_3 : ∀ m, compatible p_4_3 m → WeightedBound 208 m := sound 208 _ cert_4_3 (by decide) checked_4_3
def p_4_4 := refine p_4 (4,false) (some ⟨false,false,1⟩)
def cert_4_4 : Tree := (.side 7 18 false (1))
theorem checked_4_4 : check 208 p_4_4 cert_4_4 = true := by decide +kernel
theorem safe_4_4 : ∀ m, compatible p_4_4 m → WeightedBound 208 m := sound 208 _ cert_4_4 (by decide) checked_4_4
def p_4_5 := refine p_4 (4,false) (some ⟨false,true,1⟩)
def cert_4_5 : Tree := (.side 16 14 true (2))
theorem checked_4_5 : check 208 p_4_5 cert_4_5 = true := by decide +kernel
theorem safe_4_5 : ∀ m, compatible p_4_5 m → WeightedBound 208 m := sound 208 _ cert_4_5 (by decide) checked_4_5
def p_4_6 := refine p_4 (4,false) (some ⟨true,false,1⟩)
def cert_4_6 : Tree := (split 17 (2,true) 6 #[
(.side 7 18 false (1)),
(.side 20 20 false (3)),
(.side 7 16 false (1)),
(.side 20 18 false (3)),
(.side 14 4 true (0)),
(.last 86 (5,false)),
(.last 27 (5,false)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0)],[(false,2)],[(true,2)],[(false,3)],[(true,3),(true,16),(true,7)],[(false,11)],[],[],[],[(true,6)],[(false,7)],[(false,16)],[],[],[(true,11)],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,2),(3,14),(3,15),(7,16),(17,10),(18,6),(3,19),(7,20),(13,6),(7,14),(21,10),(7,22),(13,10),(13,14),(13,14)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0)],[(false,2),(false,8),(false,6)],[(true,2),(true,8)],[],[(true,4)],[],[(true,6)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,8),(9,2),(3,4),(5,2)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .empty .leaf)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .leaf) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty)) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))))) (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty .leaf)) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) .empty) .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .leaf (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf))))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) .empty),.empty,(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty)]⟩),
(.side 7 16 false (1)),
(.side 0 52 true (-4)),
(.side 7 16 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch .leaf (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)))),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))))]⟩),
(.side 7 14 false (1)),
(.side 7 18 false (2)),
(.side 7 14 false (1)),
(.side 7 16 false (2)),
(.last 19 (5,false)),
(.last 19 (5,false)),
(.side 12 6 true (0)),
(.last 19 (5,false)),
(.side 1 18 false (2)),
(.side 7 22 false (2)),
(.side 1 18 false (2)),
(.last 23 (5,false))])
theorem checked_4_6 : check 208 p_4_6 cert_4_6 = true := by decide +kernel
theorem safe_4_6 : ∀ m, compatible p_4_6 m → WeightedBound 208 m := sound 208 _ cert_4_6 (by decide) checked_4_6
def p_4_7 := refine p_4 (4,false) (some ⟨true,true,1⟩)
def cert_4_7 : Tree := (.side 1 41 true (-2))
theorem checked_4_7 : check 208 p_4_7 cert_4_7 = true := by decide +kernel
theorem safe_4_7 : ∀ m, compatible p_4_7 m → WeightedBound 208 m := sound 208 _ cert_4_7 (by decide) checked_4_7
def p_4_8 := refine p_4 (4,false) (some ⟨false,false,2⟩)
def cert_4_8 : Tree := (.side 6 18 false (2))
theorem checked_4_8 : check 208 p_4_8 cert_4_8 = true := by decide +kernel
theorem safe_4_8 : ∀ m, compatible p_4_8 m → WeightedBound 208 m := sound 208 _ cert_4_8 (by decide) checked_4_8
def p_4_9 := refine p_4 (4,false) (some ⟨false,true,2⟩)
def cert_4_9 : Tree := (split 16 (2,true) 6 #[
(.side 0 17 true (-2)),
(.side 0 17 true (-2)),
(.side 0 49 true (-2)),
(.side 3 32 true (-2)),
(.side 0 32 true (-2)),
(.side 0 32 true (-2)),
(.last 21 (5,false)),
(.side 1 16 true (-2)),
(.side 7 22 false (2)),
(.side 0 18 true (-2)),
(.side 7 20 false (2)),
(.side 0 31 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,4),(false,6)],[(true,2),(true,4),(true,6)],[(false,3),(false,5),(false,7)],[(true,5),(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2),(true,6)],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))) (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .leaf .leaf))))) (.branch .empty (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .leaf .leaf))) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty))) (.branch .empty (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)))),(.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) (.branch (.branch .empty (.branch .leaf .leaf)) .empty)))),.empty,(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty)))))]⟩),
(.side 0 52 true (-2)),
(.last 21 (5,false)),
(.side 0 29 true (-2)),
(.side 0 19 true (-2)),
(.side 0 19 true (-2)),
(.side 15 2 true (1)),
(.last 38 (5,false)),
(.last 17 (5,false)),
(.last 17 (5,false)),
(.last 17 (5,false)),
(.last 17 (5,false))])
theorem checked_4_9 : check 208 p_4_9 cert_4_9 = true := by decide +kernel
theorem safe_4_9 : ∀ m, compatible p_4_9 m → WeightedBound 208 m := sound 208 _ cert_4_9 (by decide) checked_4_9
def p_4_10 := refine p_4 (4,false) (some ⟨true,false,2⟩)
def cert_4_10 : Tree := (split 19 (2,true) 6 #[
(.side 6 18 false (2)),
(.side 22 20 false (3)),
(.side 6 16 false (2)),
(.side 22 18 false (3)),
(.side 2 20 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(true,1)],[(false,1)],[(true,3)],[(false,3)],[(true,2)],[(false,6)],[(false,7)],[(true,6)],[(true,9)],[(false,10)],[(true,11),(true,25)],[(true,8)],[(false,8)],[(true,7)],[(true,15)],[(false,16),(false,22)],[(false,17)],[(true,18)],[(false,18)],[(true,17)],[(true,21)],[(true,16),(true,22)],[(true,23)],[(false,24)]],#[(0,1),(3,2),(0,6),(5,4),(0,0),(0,0),(7,9),(8,15),(14,13),(0,10),(11,0),(0,12),(0,0),(0,0),(0,0),(0,16),(17,23),(18,21),(20,19),(0,0),(0,0),(0,22),(17,23),(0,24),(25,0),(0,12)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[(false,3)],[(true,3)],[(false,4),(true,4),(false,5),(true,5),(true,6),(false,8),(true,8),(false,9),(true,9),(false,10),(false,12),(true,12),(false,15),(true,15),(true,16),(false,18),(false,20),(true,20),(false,23),(true,23),(true,24),(false,26)],[(false,6)],[(false,7)],[(true,7)],[(true,10),(true,13)],[(false,11)],[(true,11)],[(false,13),(false,16)],[(false,14)],[(true,14)],[(false,17)],[(true,17)],[(true,18),(true,21),(true,26),(true,28)],[(false,19)],[(true,19),(true,27)],[(false,21),(false,24),(false,28)],[(false,22)],[(true,22)],[(false,25)],[(true,25)],[(false,27)]],#[(0,1),(2,3),(4,5),(6,7),(8,8),(8,8),(9,8),(10,11),(8,8),(8,8),(8,12),(13,14),(8,8),(15,12),(16,17),(8,8),(15,8),(18,19),(8,20),(21,22),(8,8),(23,20),(24,25),(8,8),(23,8),(26,27),(8,20),(28,22),(23,20)]⟩,#[(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) .empty) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .leaf)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .leaf .leaf))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))))) (.branch (.branch (.branch (.branch .empty (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch .leaf (.branch (.branch .leaf (.branch .empty .leaf)) .empty))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch .empty (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .leaf)))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .leaf))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty)) (.branch (.branch .empty (.branch (.branch .empty (.branch .leaf (.branch (.branch .empty .leaf) .empty))) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .leaf .leaf)))) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))))),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty .leaf)) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty (.branch .leaf .leaf)) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch .leaf .leaf))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty))) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty .leaf))))))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))))))) (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf)) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))))))),(.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) .leaf) (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty .leaf)) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))) .leaf))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .leaf) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch .empty (.branch .leaf (.branch .empty (.branch .empty .leaf)))))) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .leaf)) (.branch (.branch .empty .leaf) .empty))))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)) (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch .empty (.branch .empty (.branch (.branch .leaf (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .leaf .leaf)))) (.branch (.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .empty))) .leaf)) (.branch (.branch .empty (.branch .leaf (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .leaf (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch .empty (.branch .empty .leaf)))))))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .leaf .leaf))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty .leaf) .empty)))) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)) (.branch (.branch (.branch (.branch .leaf (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .leaf (.branch .leaf (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty)))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)))) (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty))) .empty))))),(.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty))) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty .leaf) .empty)) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty))) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)))) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)) (.branch (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch .empty (.branch .empty .leaf)) .empty)) (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty))) .empty) (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty))) (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf))))))) (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty .leaf)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch .empty .leaf))))) .empty))),.empty,(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty)))) (.branch (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch .empty (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) (.branch .empty (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)))))]⟩),
(.last 31 (5,false)),
(.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,8)],[(false,2)],[(true,2)],[(false,3)],[(true,3)],[],[(true,4)],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,2),(3,14),(3,15),(7,16),(17,10),(18,6),(3,19),(7,20),(13,6),(7,14),(21,10),(7,22),(13,10),(13,14),(13,14)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,8)],[(false,2)],[(true,2)],[],[],[(false,4)],[(true,4)],[],[],[],[],[],[],[],[],[],[],[],[],[],[]],#[(1,2),(1,2),(3,4),(5,6),(7,8),(9,10),(3,11),(12,6),(13,2),(3,14),(3,15),(7,16),(17,10),(18,6),(3,19),(7,20),(13,6),(7,14),(21,10),(7,22),(13,10),(13,14),(13,14)]⟩,#[(.branch (.branch .leaf .leaf) (.branch (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) .empty)) .empty)),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))))) .empty) (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) (.branch .empty (.branch (.branch .empty .leaf) .empty))))),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty),(.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch .empty (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) .empty)))) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)),(.branch (.branch .empty (.branch (.branch .empty (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty)))) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf (.branch .empty .leaf)) .empty) (.branch .empty (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty))))) .empty) .empty),(.branch .empty (.branch (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))) .empty)) .empty)),(.branch .empty (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty)),.empty,(.branch (.branch (.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) .empty) .empty)]⟩),
(.side 0 24 false (2)),
(.side 0 54 true (-4)),
(.side 20 6 false (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch .leaf (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)))),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))))]⟩),
(.side 6 14 false (2)),
(.side 6 18 false (2)),
(.side 6 14 false (2)),
(.side 6 16 false (2)),
(.last 21 (5,false)),
(.last 21 (5,false)),
(.side 2 22 false (2)),
(.last 21 (5,false)),
(.side 7 20 false (1)),
(.side 6 22 false (2)),
(.side 7 20 false (1)),
(.side 6 22 false (2))])
theorem checked_4_10 : check 208 p_4_10 cert_4_10 = true := by decide +kernel
theorem safe_4_10 : ∀ m, compatible p_4_10 m → WeightedBound 208 m := sound 208 _ cert_4_10 (by decide) checked_4_10
def p_4_11 := refine p_4 (4,false) (some ⟨true,true,2⟩)
def cert_4_11 : Tree := (split 16 (2,true) 6 #[
(.side 17 13 true (-1)),
(.side 38 17 true (0)),
(.side 17 13 true (-1)),
(.side 36 15 true (0)),
(.side 17 13 true (0)),
(.side 36 13 true (3)),
(.last 19 (5,false)),
(.last 57 (5,false)),
(.side 6 20 false (2)),
(.side 0 62 true (-2)),
(.side 22 6 false (0)),
(.side 2 15 true (-2)),
(.last 22 (5,false)),
(.side 7 49 true (-2)),
(.side 17 13 true (-1)),
(.side 4 13 true (-2)),
(.last 18 (5,false)),
(.last 37 (5,false)),
(.side 17 13 true (0)),
(.last 35 (5,false)),
(.side 7 20 false (2)),
(.last 17 (5,false)),
(.side 7 20 false (2)),
(.last 17 (5,false))])
theorem checked_4_11 : check 208 p_4_11 cert_4_11 = true := by decide +kernel
theorem safe_4_11 : ∀ m, compatible p_4_11 m → WeightedBound 208 m := sound 208 _ cert_4_11 (by decide) checked_4_11
def p_4_12 := refine p_4 (4,false) (some ⟨false,false,3⟩)
def cert_4_12 : Tree := (.side 4 16 false (2))
theorem checked_4_12 : check 208 p_4_12 cert_4_12 = true := by decide +kernel
theorem safe_4_12 : ∀ m, compatible p_4_12 m → WeightedBound 208 m := sound 208 _ cert_4_12 (by decide) checked_4_12
def p_4_13 := refine p_4 (4,false) (some ⟨false,true,3⟩)
def cert_4_13 : Tree := (split 21 (5,false) 6 #[
(.side 56 4 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 54 4 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 22 4 true (2)),
(.side 70 4 true (4)),
(.side 19 3 true (1)),
(.side 68 4 true (4)),
(.last 22 (2,true)),
(.side 70 4 true (4)),
(.last 22 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 22 4 true (3)),
(.side 52 4 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 20 2 true (2)),
(.side 22 4 true (4)),
(.side 24 4 true (2)),
(.side 22 4 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf))]⟩),
(.side 21 1 true (3)),
(.side 56 4 true (2)),
(.side 21 1 true (3))])
theorem checked_4_13 : check 208 p_4_13 cert_4_13 = true := by decide +kernel
theorem safe_4_13 : ∀ m, compatible p_4_13 m → WeightedBound 208 m := sound 208 _ cert_4_13 (by decide) checked_4_13
def p_4_14 := refine p_4 (4,false) (some ⟨true,false,3⟩)
def cert_4_14 : Tree := (split 27 (5,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 21 7 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 25 3 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.last 28 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.last 28 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 26 2 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 19 9 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf))]⟩),
(.side 27 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))]⟩),
(.side 27 1 true (3))])
theorem checked_4_14 : check 208 p_4_14 cert_4_14 = true := by decide +kernel
theorem safe_4_14 : ∀ m, compatible p_4_14 m → WeightedBound 208 m := sound 208 _ cert_4_14 (by decide) checked_4_14
def p_4_15 := refine p_4 (4,false) (some ⟨true,true,3⟩)
def cert_4_15 : Tree := (.side 16 11 true (-1))
theorem checked_4_15 : check 208 p_4_15 cert_4_15 = true := by decide +kernel
theorem safe_4_15 : ∀ m, compatible p_4_15 m → WeightedBound 208 m := sound 208 _ cert_4_15 (by decide) checked_4_15
def p_4_16 := refine p_4 (4,false) (some ⟨false,false,4⟩)
def cert_4_16 : Tree := (split 19 (5,false) 6 #[
(.side 7 16 false (1)),
(.last 22 (2,true)),
(.side 7 14 false (1)),
(.last 22 (2,true)),
(.side 21 1 false (-1)),
(.side 7 22 false (1)),
(.side 30 1 false (2)),
(.side 6 20 false (2)),
(.last 20 (2,true)),
(.side 6 22 false (2)),
(.last 20 (2,true)),
(.side 2 18 false (2)),
(.side 7 22 false (1)),
(.side 30 7 true (2)),
(.side 8 12 false (1)),
(.side 4 16 false (2)),
(.side 18 2 true (-2)),
(.side 16 4 true (-2)),
(.side 23 1 false (-1)),
(.side 26 3 true (2)),
(.side 7 19 false (1)),
(.side 40 1 true (0)),
(.side 7 19 false (1)),
(.side 27 1 true (1))])
theorem checked_4_16 : check 208 p_4_16 cert_4_16 = true := by decide +kernel
theorem safe_4_16 : ∀ m, compatible p_4_16 m → WeightedBound 208 m := sound 208 _ cert_4_16 (by decide) checked_4_16
def p_4_17 := refine p_4 (4,false) (some ⟨false,true,4⟩)
def cert_4_17 : Tree := (split 17 (5,false) 6 #[
(.side 29 1 true (3)),
(.side 12 26 true (0)),
(.side 27 1 true (3)),
(.side 12 24 true (0)),
(.side 19 1 true (3)),
(.side 39 1 true (5)),
(.side 16 3 true (2)),
(.side 37 1 true (5)),
(.last 18 (2,true)),
(.side 39 1 true (5)),
(.last 18 (2,true)),
(.side 2 16 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 21 1 true (5)),
(.side 25 1 true (3)),
(.side 4 14 true (-2)),
(.side 16 2 true (2)),
(.side 18 1 true (4)),
(.side 21 1 true (3)),
(.side 18 1 true (4)),
(.side 32 1 true (2)),
(.side 17 1 true (3)),
(.side 7 17 true (-2)),
(.side 17 1 true (3))])
theorem checked_4_17 : check 208 p_4_17 cert_4_17 = true := by decide +kernel
theorem safe_4_17 : ∀ m, compatible p_4_17 m → WeightedBound 208 m := sound 208 _ cert_4_17 (by decide) checked_4_17
def p_4_18 := refine p_4 (4,false) (some ⟨true,false,4⟩)
def cert_4_18 : Tree := (.side 21 1 false (-1))
theorem checked_4_18 : check 208 p_4_18 cert_4_18 = true := by decide +kernel
theorem safe_4_18 : ∀ m, compatible p_4_18 m → WeightedBound 208 m := sound 208 _ cert_4_18 (by decide) checked_4_18
def p_4_19 := refine p_4 (4,false) (some ⟨true,true,4⟩)
def cert_4_19 : Tree := (split 17 (5,false) 6 #[
(.side 3 15 true (-2)),
(.side 46 1 true (6)),
(.side 5 13 true (-2)),
(.side 44 1 true (6)),
(.side 19 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 16 3 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.last 18 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.last 18 (2,true)),
(.side 36 1 true (4)),
(.side 26 1 true (2)),
(.side 21 1 true (5)),
(.side 7 11 true (-2)),
(.side 34 1 true (4)),
(.side 16 2 true (2)),
(.side 18 1 true (4)),
(.side 21 1 true (3)),
(.side 18 1 true (4)),
(.side 20 1 true (2)),
(.side 17 1 true (3)),
(.side 13 5 true (0)),
(.side 17 1 true (3))])
theorem checked_4_19 : check 208 p_4_19 cert_4_19 = true := by decide +kernel
theorem safe_4_19 : ∀ m, compatible p_4_19 m → WeightedBound 208 m := sound 208 _ cert_4_19 (by decide) checked_4_19
def p_4_20 := refine p_4 (4,false) (some ⟨false,false,5⟩)
def cert_4_20 : Tree := (split 16 (5,false) 6 #[
(.side 6 18 false (2)),
(.side 0 49 true (-2)),
(.side 5 16 false (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 1 16 false (2)),
(.last 18 (2,true)),
(.last 18 (2,true)),
(.last 18 (2,true)),
(.side 7 14 false (1)),
(.last 20 (2,true)),
(.side 7 14 false (1)),
(.side 7 18 false (1)),
(.side 7 12 false (1)),
(.side 21 5 true (3)),
(.side 7 12 false (1)),
(.side 7 16 false (1)),
(.side 7 17 false (1)),
(.side 15 2 true (0)),
(.side 7 17 false (1)),
(.side 1 18 false (2)),
(.side 7 17 false (1)),
(.side 33 1 true (1)),
(.side 7 17 false (1)),
(.side 21 1 true (1))])
theorem checked_4_20 : check 208 p_4_20 cert_4_20 = true := by decide +kernel
theorem safe_4_20 : ∀ m, compatible p_4_20 m → WeightedBound 208 m := sound 208 _ cert_4_20 (by decide) checked_4_20
def p_4_21 := refine p_4 (4,false) (some ⟨false,true,5⟩)
def cert_4_21 : Tree := (split 31 (5,false) 6 #[
(.side 0 32 true (-2)),
(.side 0 32 true (-2)),
(.side 29 4 true (1)),
(.side 7 48 true (-2)),
(.side 17 15 true (-1)),
(.side 17 15 true (-1)),
(.last 33 (2,true)),
(.side 1 31 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[],[(false,3),(false,7)],[(true,3),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) .empty),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)))),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))))]⟩),
(.side 0 33 true (-2)),
(.last 35 (2,true)),
(.side 18 14 true (-1)),
(.side 29 5 true (1)),
(.side 29 5 true (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))]⟩),
(.side 20 12 true (-1)),
(.side 30 2 true (2)),
(.side 30 2 true (2)),
(.side 15 17 true (-1)),
(.side 30 2 true (2)),
(.side 38 1 false (0)),
(.side 31 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf)))]⟩),
(.side 31 1 true (3))])
theorem checked_4_21 : check 208 p_4_21 cert_4_21 = true := by decide +kernel
theorem safe_4_21 : ∀ m, compatible p_4_21 m → WeightedBound 208 m := sound 208 _ cert_4_21 (by decide) checked_4_21
def p_4_22 := refine p_4 (4,false) (some ⟨true,false,5⟩)
def cert_4_22 : Tree := (split 16 (5,false) 6 #[
(.last 19 (2,true)),
(.side 17 13 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 7 16 false (2)),
(.side 1 16 false (2)),
(.side 42 3 true (4)),
(.last 18 (2,true)),
(.side 60 3 true (4)),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.side 7 14 false (1)),
(.last 17 (2,true)),
(.side 7 12 false (1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 7 12 false (1)),
(.side 7 14 false (1)),
(.side 7 17 false (1)),
(.side 20 4 true (1)),
(.side 7 17 false (1)),
(.side 13 12 true (0)),
(.side 7 17 false (1)),
(.side 7 20 false (1)),
(.side 7 17 false (1)),
(.side 13 4 true (0))])
theorem checked_4_22 : check 208 p_4_22 cert_4_22 = true := by decide +kernel
theorem safe_4_22 : ∀ m, compatible p_4_22 m → WeightedBound 208 m := sound 208 _ cert_4_22 (by decide) checked_4_22
def p_4_23 := refine p_4 (4,false) (some ⟨true,true,5⟩)
def cert_4_23 : Tree := (split 19 (5,false) 6 #[
(.side 16 13 true (0)),
(.side 13 30 true (0)),
(.side 16 11 true (0)),
(.side 13 28 true (0)),
(.side 17 3 true (1)),
(.side 13 25 true (0)),
(.side 19 3 true (2)),
(.side 13 23 true (0)),
(.last 20 (2,true)),
(.side 13 25 true (0)),
(.last 20 (2,true)),
(.side 2 18 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 17 5 true (1)),
(.side 16 9 true (0)),
(.side 4 16 true (-2)),
(.side 19 2 true (2)),
(.side 18 2 true (2)),
(.side 16 5 true (1)),
(.side 18 2 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf))]⟩),
(.side 19 1 true (3)),
(.side 7 19 true (-2)),
(.side 19 1 true (3))])
theorem checked_4_23 : check 208 p_4_23 cert_4_23 = true := by decide +kernel
theorem safe_4_23 : ∀ m, compatible p_4_23 m → WeightedBound 208 m := sound 208 _ cert_4_23 (by decide) checked_4_23
theorem safe_4 : ∀ m, compatible p_4 m → WeightedBound 208 m := by
  apply split_safe 208 p_4 15 (4,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_4_0 | exact safe_4_1 | exact safe_4_2 | exact safe_4_3 | exact safe_4_4 | exact safe_4_5 | exact safe_4_6 | exact safe_4_7 | exact safe_4_8 | exact safe_4_9 | exact safe_4_10 | exact safe_4_11 | exact safe_4_12 | exact safe_4_13 | exact safe_4_14 | exact safe_4_15 | exact safe_4_16 | exact safe_4_17 | exact safe_4_18 | exact safe_4_19 | exact safe_4_20 | exact safe_4_21 | exact safe_4_22 | exact safe_4_23
def p_5 := refine parent (5,true) (some ⟨false,true,1⟩)
def p_5_0 := refine p_5 (4,false) (some ⟨false,false,0⟩)
def cert_5_0 : Tree := (split 43 (5,false) 6 #[
(.side 31 37 true (-4)),
(.side 38 40 true (0)),
(.side 31 35 true (-4)),
(.side 38 38 true (0)),
(.side 82 74 true (0)),
(.side 38 19 true (0)),
(.side 41 3 true (3)),
(.side 38 17 true (0)),
(.last 44 (2,true)),
(.side 38 19 true (0)),
(.last 44 (2,true)),
(.side 78 70 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 38 42 true (0)),
(.side 31 33 true (-4)),
(.side 76 68 true (0)),
(.side 42 2 true (4)),
(.side 38 19 true (0)),
(.side 38 21 true (0)),
(.side 78 70 true (0)),
(.side 78 70 true (0)),
(.side 43 1 true (5)),
(.side 86 109 true (0)),
(.side 43 1 true (5))])
theorem checked_5_0 : check 208 p_5_0 cert_5_0 = true := by decide +kernel
theorem safe_5_0 : ∀ m, compatible p_5_0 m → WeightedBound 208 m := sound 208 _ cert_5_0 (by decide) checked_5_0
def p_5_1 := refine p_5 (4,false) (some ⟨false,true,0⟩)
def cert_5_1 : Tree := (.side 0 16 true (-2))
theorem checked_5_1 : check 208 p_5_1 cert_5_1 = true := by decide +kernel
theorem safe_5_1 : ∀ m, compatible p_5_1 m → WeightedBound 208 m := sound 208 _ cert_5_1 (by decide) checked_5_1
def p_5_2 := refine p_5 (4,false) (some ⟨true,false,0⟩)
def cert_5_2 : Tree := (.side 14 3 true (2))
theorem checked_5_2 : check 208 p_5_2 cert_5_2 = true := by decide +kernel
theorem safe_5_2 : ∀ m, compatible p_5_2 m → WeightedBound 208 m := sound 208 _ cert_5_2 (by decide) checked_5_2
def p_5_3 := refine p_5 (4,false) (some ⟨true,true,0⟩)
def cert_5_3 : Tree := (split 33 (5,false) 6 #[
(.side 139 37 true (9)),
(.side 24 40 true (1)),
(.side 135 35 true (9)),
(.side 24 38 true (1)),
(.side 14 20 true (1)),
(.side 24 19 true (1)),
(.side 31 3 true (5)),
(.side 17 17 true (1)),
(.last 34 (2,true)),
(.side 16 19 true (1)),
(.last 34 (2,true)),
(.side 2 32 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 28 30 true (2)),
(.side 131 33 true (9)),
(.side 4 30 true (-2)),
(.side 32 2 true (6)),
(.side 11 43 true (-1)),
(.side 24 21 true (1)),
(.side 11 41 true (-1)),
(.side 126 70 true (6)),
(.side 33 1 true (7)),
(.side 13 21 true (1)),
(.side 33 1 true (7))])
theorem checked_5_3 : check 208 p_5_3 cert_5_3 = true := by decide +kernel
theorem safe_5_3 : ∀ m, compatible p_5_3 m → WeightedBound 208 m := sound 208 _ cert_5_3 (by decide) checked_5_3
def p_5_4 := refine p_5 (4,false) (some ⟨false,false,1⟩)
def cert_5_4 : Tree := (split 59 (5,false) 6 #[
(.side 166 37 true (4)),
(.side 41 40 true (-1)),
(.side 162 35 true (4)),
(.side 41 38 true (-1)),
(.side 174 41 true (4)),
(.side 41 19 true (-1)),
(.side 57 3 true (3)),
(.side 50 17 true (-1)),
(.last 60 (2,true)),
(.side 50 19 true (-1)),
(.last 60 (2,true)),
(.side 174 41 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 50 21 true (-1)),
(.side 158 33 true (4)),
(.side 170 39 true (4)),
(.side 58 2 true (4)),
(.side 178 43 true (4)),
(.side 41 21 true (-1)),
(.side 182 45 true (4)),
(.side 152 70 true (4)),
(.side 59 1 true (5)),
(.side 156 72 true (4)),
(.side 59 1 true (5))])
theorem checked_5_4 : check 208 p_5_4 cert_5_4 = true := by decide +kernel
theorem safe_5_4 : ∀ m, compatible p_5_4 m → WeightedBound 208 m := sound 208 _ cert_5_4 (by decide) checked_5_4
def p_5_5 := refine p_5 (4,false) (some ⟨false,true,1⟩)
def cert_5_5 : Tree := (split 64 (5,false) 6 #[
(.side 56 37 true (0)),
(.side 59 40 true (3)),
(.side 56 35 true (0)),
(.side 59 38 true (3)),
(.side 59 100 true (3)),
(.side 59 19 true (3)),
(.side 62 3 true (6)),
(.side 59 17 true (3)),
(.last 65 (2,true)),
(.side 59 19 true (3)),
(.last 65 (2,true)),
(.side 117 91 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 59 63 true (3)),
(.side 56 33 true (0)),
(.side 115 89 true (3)),
(.side 63 2 true (7)),
(.side 56 40 true (0)),
(.side 59 21 true (3)),
(.side 59 40 true (3)),
(.side 99 70 true (3)),
(.side 64 1 true (8)),
(.side 59 101 true (3)),
(.side 64 1 true (8))])
theorem checked_5_5 : check 208 p_5_5 cert_5_5 = true := by decide +kernel
theorem safe_5_5 : ∀ m, compatible p_5_5 m → WeightedBound 208 m := sound 208 _ cert_5_5 (by decide) checked_5_5
def p_5_6 := refine p_5 (4,false) (some ⟨true,false,1⟩)
def cert_5_6 : Tree := (split 17 (2,true) 6 #[
(.last 59 (5,false)),
(.last 81 (5,false)),
(.last 55 (5,false)),
(.last 77 (5,false)),
(.side 14 4 true (2)),
(.last 66 (5,false)),
(.last 20 (5,false)),
(.last 64 (5,false)),
(.last 36 (5,false)),
(.last 66 (5,false)),
(.last 55 (5,false)),
(.last 43 (5,false)),
(.last 53 (5,false)),
(.side 14 6 true (2)),
(.last 51 (5,false)),
(.last 41 (5,false)),
(.last 19 (5,false)),
(.side 15 3 true (2)),
(.last 68 (5,false)),
(.last 21 (5,false)),
(.last 105 (5,false)),
(.last 18 (5,false)),
(.side 13 5 true (1)),
(.last 18 (5,false))])
theorem checked_5_6 : check 208 p_5_6 cert_5_6 = true := by decide +kernel
theorem safe_5_6 : ∀ m, compatible p_5_6 m → WeightedBound 208 m := sound 208 _ cert_5_6 (by decide) checked_5_6
def p_5_7 := refine p_5 (4,false) (some ⟨true,true,1⟩)
def cert_5_7 : Tree := (.side 1 15 true (-2))
theorem checked_5_7 : check 208 p_5_7 cert_5_7 = true := by decide +kernel
theorem safe_5_7 : ∀ m, compatible p_5_7 m → WeightedBound 208 m := sound 208 _ cert_5_7 (by decide) checked_5_7
def p_5_8 := refine p_5 (4,false) (some ⟨false,false,2⟩)
def cert_5_8 : Tree := (split 59 (5,false) 6 #[
(.side 166 37 true (4)),
(.side 50 40 true (-1)),
(.side 162 35 true (4)),
(.side 50 38 true (-1)),
(.side 173 51 true (1)),
(.side 50 19 true (-1)),
(.side 57 3 true (3)),
(.side 43 17 true (-1)),
(.last 60 (2,true)),
(.side 41 19 true (-1)),
(.last 60 (2,true)),
(.side 174 41 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 182 45 true (4)),
(.side 158 33 true (4)),
(.side 170 39 true (4)),
(.side 58 2 true (4)),
(.side 170 39 true (4)),
(.side 50 21 true (-1)),
(.last 61 (2,true)),
(.side 152 70 true (4)),
(.side 59 1 true (5)),
(.side 186 47 true (4)),
(.side 59 1 true (5))])
theorem checked_5_8 : check 208 p_5_8 cert_5_8 = true := by decide +kernel
theorem safe_5_8 : ∀ m, compatible p_5_8 m → WeightedBound 208 m := sound 208 _ cert_5_8 (by decide) checked_5_8
def p_5_9 := refine p_5 (4,false) (some ⟨false,true,2⟩)
def cert_5_9 : Tree := (.side 0 17 true (-2))
theorem checked_5_9 : check 208 p_5_9 cert_5_9 = true := by decide +kernel
theorem safe_5_9 : ∀ m, compatible p_5_9 m → WeightedBound 208 m := sound 208 _ cert_5_9 (by decide) checked_5_9
def p_5_10 := refine p_5 (4,false) (some ⟨true,false,2⟩)
def cert_5_10 : Tree := (split 19 (2,true) 6 #[
(.last 59 (5,false)),
(.last 81 (5,false)),
(.last 55 (5,false)),
(.last 77 (5,false)),
(.last 63 (5,false)),
(.last 66 (5,false)),
(.last 22 (5,false)),
(.last 64 (5,false)),
(.side 43 32 false (2)),
(.last 66 (5,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[],[(true,2)],[],[],[],[(true,12)],[(false,5),(false,9)],[(true,5),(true,9)],[(false,10)],[],[],[(true,11)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15),(8,9),(10,11),(12,13),(14,15)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,6)],[(false,2)],[(true,2)],[],[(true,4)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,6),(7,2),(3,2),(3,2)]⟩,#[(.branch (.branch .leaf .leaf) (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .leaf) .empty)) .empty))),(.branch (.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf) .empty) (.branch .empty (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf) .empty)) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty (.branch .empty .leaf)))) (.branch .empty (.branch (.branch (.branch .empty .leaf) .leaf) .empty))) (.branch (.branch .empty (.branch .empty (.branch (.branch .empty .leaf) .empty))) (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch .empty (.branch .empty (.branch .empty .leaf)))))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch .empty .leaf) .leaf)) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf)))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) .empty) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch (.branch .empty (.branch .empty .leaf)) .leaf) .empty)) .empty) .empty),.empty,(.branch (.branch .empty (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .leaf) .empty)) .empty)) .empty)]⟩),
(.last 43 (5,false)),
(.last 53 (5,false)),
(.last 66 (5,false)),
(.last 51 (5,false)),
(.last 41 (5,false)),
(.last 21 (5,false)),
(.last 43 (5,false)),
(.last 68 (5,false)),
(.last 23 (5,false)),
(.last 47 (5,false)),
(.last 20 (5,false)),
(.side 13 7 true (1)),
(.last 20 (5,false))])
theorem checked_5_10 : check 208 p_5_10 cert_5_10 = true := by decide +kernel
theorem safe_5_10 : ∀ m, compatible p_5_10 m → WeightedBound 208 m := sound 208 _ cert_5_10 (by decide) checked_5_10
def p_5_11 := refine p_5 (4,false) (some ⟨true,true,2⟩)
def cert_5_11 : Tree := (split 97 (5,false) 6 #[
(.side 61 37 true (2)),
(.side 92 40 true (6)),
(.side 63 35 true (2)),
(.side 92 38 true (6)),
(.side 132 70 true (6)),
(.side 92 19 true (6)),
(.side 95 3 true (9)),
(.side 92 17 true (6)),
(.last 98 (2,true)),
(.side 92 19 true (6)),
(.last 98 (2,true)),
(.side 89 60 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 92 42 true (6)),
(.side 65 33 true (2)),
(.side 89 58 true (3)),
(.side 96 2 true (10)),
(.side 92 19 true (6)),
(.side 92 21 true (6)),
(.side 92 17 true (6)),
(.side 132 70 true (6)),
(.side 97 1 true (11)),
(.side 52 77 true (0)),
(.side 97 1 true (11))])
theorem checked_5_11 : check 208 p_5_11 cert_5_11 = true := by decide +kernel
theorem safe_5_11 : ∀ m, compatible p_5_11 m → WeightedBound 208 m := sound 208 _ cert_5_11 (by decide) checked_5_11
def p_5_12 := refine p_5 (4,false) (some ⟨false,false,3⟩)
def cert_5_12 : Tree := (split 55 (5,false) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 20 40 true (-4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 27 38 true (-4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 37 19 true (-1)),
(.side 53 3 true (3)),
(.side 46 17 true (-1)),
(.last 56 (2,true)),
(.side 46 19 true (-1)),
(.last 56 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 54 2 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 35 21 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 148 70 true (4)),
(.side 55 1 true (5)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf)))]⟩),
(.side 55 1 true (5))])
theorem checked_5_12 : check 208 p_5_12 cert_5_12 = true := by decide +kernel
theorem safe_5_12 : ∀ m, compatible p_5_12 m → WeightedBound 208 m := sound 208 _ cert_5_12 (by decide) checked_5_12
def p_5_13 := refine p_5 (4,false) (some ⟨false,true,3⟩)
def cert_5_13 : Tree := (.side 14 4 true (2))
theorem checked_5_13 : check 208 p_5_13 cert_5_13 = true := by decide +kernel
theorem safe_5_13 : ∀ m, compatible p_5_13 m → WeightedBound 208 m := sound 208 _ cert_5_13 (by decide) checked_5_13
def p_5_14 := refine p_5 (4,false) (some ⟨true,false,3⟩)
def cert_5_14 : Tree := (split 20 (5,false) 6 #[
(.side 33 37 true (-4)),
(.side 51 40 true (3)),
(.side 31 35 true (-4)),
(.side 49 38 true (3)),
(.side 14 7 true (1)),
(.side 80 19 true (6)),
(.side 18 3 true (2)),
(.side 76 17 true (6)),
(.last 21 (2,true)),
(.side 80 19 true (6)),
(.last 21 (2,true)),
(.side 116 27 true (6)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 76 17 true (6)),
(.side 29 33 true (-4)),
(.side 110 25 true (6)),
(.side 19 2 true (3)),
(.side 110 25 true (6)),
(.side 84 21 true (6)),
(.side 104 23 true (6)),
(.side 103 70 true (3)),
(.side 20 1 true (4)),
(.side 13 8 true (1)),
(.side 20 1 true (4))])
theorem checked_5_14 : check 208 p_5_14 cert_5_14 = true := by decide +kernel
theorem safe_5_14 : ∀ m, compatible p_5_14 m → WeightedBound 208 m := sound 208 _ cert_5_14 (by decide) checked_5_14
def p_5_15 := refine p_5 (4,false) (some ⟨true,true,3⟩)
def cert_5_15 : Tree := (split 93 (5,false) 6 #[
(.side 58 37 true (2)),
(.side 88 40 true (6)),
(.side 59 35 true (2)),
(.side 88 38 true (6)),
(.side 126 68 true (6)),
(.side 88 19 true (6)),
(.side 91 3 true (9)),
(.side 88 17 true (6)),
(.last 94 (2,true)),
(.side 88 19 true (6)),
(.last 94 (2,true)),
(.side 85 58 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 88 40 true (6)),
(.side 61 33 true (2)),
(.side 85 56 true (3)),
(.side 92 2 true (10)),
(.side 88 17 true (6)),
(.side 88 21 true (6)),
(.side 88 15 true (6)),
(.side 128 70 true (6)),
(.side 93 1 true (11)),
(.side 50 73 true (0)),
(.side 93 1 true (11))])
theorem checked_5_15 : check 208 p_5_15 cert_5_15 = true := by decide +kernel
theorem safe_5_15 : ∀ m, compatible p_5_15 m → WeightedBound 208 m := sound 208 _ cert_5_15 (by decide) checked_5_15
def p_5_16 := refine p_5 (4,false) (some ⟨false,false,4⟩)
def cert_5_16 : Tree := (split 19 (5,false) 6 #[
(.side 82 37 true (-3)),
(.side 42 40 true (0)),
(.side 78 35 true (-3)),
(.side 40 38 true (0)),
(.side 27 1 false (-1)),
(.side 47 19 true (-1)),
(.side 18 3 true (0)),
(.side 45 17 true (-1)),
(.last 20 (2,true)),
(.side 47 19 true (-1)),
(.last 20 (2,true)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 7 16 false (3)),
(.side 16 7 true (0)),
(.side 74 33 true (-3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 18 2 true (0)),
(.side 16 4 true (0)),
(.side 49 21 true (-1)),
(.side 17 3 true (0)),
(.side 94 70 true (0)),
(.side 19 1 true (1)),
(.side 30 1 false (0)),
(.side 19 1 true (1))])
theorem checked_5_16 : check 208 p_5_16 cert_5_16 = true := by decide +kernel
theorem safe_5_16 : ∀ m, compatible p_5_16 m → WeightedBound 208 m := sound 208 _ cert_5_16 (by decide) checked_5_16
def p_5_17 := refine p_5 (4,false) (some ⟨false,true,4⟩)
def cert_5_17 : Tree := (.side 15 1 true (3))
theorem checked_5_17 : check 208 p_5_17 cert_5_17 = true := by decide +kernel
theorem safe_5_17 : ∀ m, compatible p_5_17 m → WeightedBound 208 m := sound 208 _ cert_5_17 (by decide) checked_5_17
def p_5_18 := refine p_5 (4,false) (some ⟨true,false,4⟩)
def cert_5_18 : Tree := (split 22 (5,false) 6 #[
(.side 68 37 true (2)),
(.side 18 40 true (0)),
(.side 66 35 true (2)),
(.side 18 38 true (0)),
(.side 18 29 true (0)),
(.side 18 19 true (0)),
(.side 20 3 true (2)),
(.side 18 17 true (0)),
(.last 23 (2,true)),
(.side 18 19 true (0)),
(.last 23 (2,true)),
(.side 2 21 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 12 16 true (0)),
(.side 64 33 true (2)),
(.side 4 19 true (-2)),
(.side 21 2 true (3)),
(.side 12 13 true (0)),
(.side 18 21 true (0)),
(.side 18 42 true (0)),
(.side 107 70 true (3)),
(.side 22 1 true (4)),
(.side 11 21 true (-1)),
(.side 22 1 true (4))])
theorem checked_5_18 : check 208 p_5_18 cert_5_18 = true := by decide +kernel
theorem safe_5_18 : ∀ m, compatible p_5_18 m → WeightedBound 208 m := sound 208 _ cert_5_18 (by decide) checked_5_18
def p_5_19 := refine p_5 (4,false) (some ⟨true,true,4⟩)
def cert_5_19 : Tree := (.side 15 1 true (3))
theorem checked_5_19 : check 208 p_5_19 cert_5_19 = true := by decide +kernel
theorem safe_5_19 : ∀ m, compatible p_5_19 m → WeightedBound 208 m := sound 208 _ cert_5_19 (by decide) checked_5_19
def p_5_20 := refine p_5 (4,false) (some ⟨false,false,5⟩)
def cert_5_20 : Tree := (split 16 (5,false) 6 #[
(.side 166 37 true (4)),
(.side 0 17 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 40 38 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 96 19 true (6)),
(.last 18 (2,true)),
(.side 38 17 true (0)),
(.last 35 (2,true)),
(.side 40 19 true (0)),
(.last 54 (2,true)),
(.side 174 41 true (4)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 14 5 true (2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 160 37 true (4)),
(.side 56 2 true (4)),
(.side 15 2 true (2)),
(.last 20 (2,true)),
(.side 100 21 true (6)),
(.side 92 70 true (0)),
(.side 16 1 true (2)),
(.side 59 1 false (5)),
(.side 16 1 true (2))])
theorem checked_5_20 : check 208 p_5_20 cert_5_20 = true := by decide +kernel
theorem safe_5_20 : ∀ m, compatible p_5_20 m → WeightedBound 208 m := sound 208 _ cert_5_20 (by decide) checked_5_20
def p_5_21 := refine p_5 (4,false) (some ⟨false,true,5⟩)
def cert_5_21 : Tree := (split 16 (5,false) 6 #[
(.side 0 17 true (-2)),
(.side 0 17 true (-2)),
(.side 14 4 true (2)),
(.side 25 38 true (2)),
(.side 138 72 true (6)),
(.side 11 38 true (-1)),
(.last 18 (2,true)),
(.side 1 16 true (-2)),
(.last 46 (2,true)),
(.side 0 18 true (-2)),
(.last 20 (2,true)),
(.side 117 91 true (3)),
(.side 14 5 true (2)),
(.side 14 5 true (2)),
(.side 97 33 true (3)),
(.side 111 87 true (3)),
(.side 15 2 true (3)),
(.side 15 2 true (3)),
(.side 11 40 true (-1)),
(.side 15 2 true (3)),
(.side 94 70 true (0)),
(.side 16 1 true (4)),
(.side 11 10 true (-1)),
(.side 16 1 true (4))])
theorem checked_5_21 : check 208 p_5_21 cert_5_21 = true := by decide +kernel
theorem safe_5_21 : ∀ m, compatible p_5_21 m → WeightedBound 208 m := sound 208 _ cert_5_21 (by decide) checked_5_21
def p_5_22 := refine p_5 (4,false) (some ⟨true,false,5⟩)
def cert_5_22 : Tree := (split 16 (5,false) 6 #[
(.last 19 (2,true)),
(.side 92 40 true (6)),
(.side 31 35 true (-4)),
(.side 36 38 true (0)),
(.side 163 49 true (1)),
(.side 14 3 true (2)),
(.last 18 (2,true)),
(.side 14 3 true (2)),
(.last 35 (2,true)),
(.last 17 (2,true)),
(.last 52 (2,true)),
(.last 17 (2,true)),
(.last 70 (2,true)),
(.side 84 19 true (6)),
(.side 140 33 true (4)),
(.side 150 35 true (4)),
(.side 23 2 true (-2)),
(.side 15 4 true (2)),
(.side 20 21 true (0)),
(.side 13 7 true (1)),
(.side 7 17 true (-2)),
(.side 66 1 true (8)),
(.side 35 14 true (1)),
(.side 66 1 true (8))])
theorem checked_5_22 : check 208 p_5_22 cert_5_22 = true := by decide +kernel
theorem safe_5_22 : ∀ m, compatible p_5_22 m → WeightedBound 208 m := sound 208 _ cert_5_22 (by decide) checked_5_22
def p_5_23 := refine p_5 (4,false) (some ⟨true,true,5⟩)
def cert_5_23 : Tree := (split 16 (5,false) 6 #[
(.side 60 37 true (2)),
(.side 16 40 true (1)),
(.side 58 35 true (2)),
(.side 16 38 true (1)),
(.side 14 3 true (2)),
(.side 16 19 true (1)),
(.side 16 3 true (3)),
(.side 16 17 true (1)),
(.last 17 (2,true)),
(.side 16 19 true (1)),
(.last 17 (2,true)),
(.side 2 15 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 14 5 true (2)),
(.side 56 33 true (2)),
(.side 4 13 true (-2)),
(.side 16 2 true (3)),
(.side 15 2 true (3)),
(.side 16 21 true (1)),
(.side 15 2 true (3)),
(.side 101 70 true (3)),
(.side 16 1 true (4)),
(.side 13 4 true (1)),
(.side 16 1 true (4))])
theorem checked_5_23 : check 208 p_5_23 cert_5_23 = true := by decide +kernel
theorem safe_5_23 : ∀ m, compatible p_5_23 m → WeightedBound 208 m := sound 208 _ cert_5_23 (by decide) checked_5_23
theorem safe_5 : ∀ m, compatible p_5 m → WeightedBound 208 m := by
  apply split_safe 208 p_5 15 (4,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_5_0 | exact safe_5_1 | exact safe_5_2 | exact safe_5_3 | exact safe_5_4 | exact safe_5_5 | exact safe_5_6 | exact safe_5_7 | exact safe_5_8 | exact safe_5_9 | exact safe_5_10 | exact safe_5_11 | exact safe_5_12 | exact safe_5_13 | exact safe_5_14 | exact safe_5_15 | exact safe_5_16 | exact safe_5_17 | exact safe_5_18 | exact safe_5_19 | exact safe_5_20 | exact safe_5_21 | exact safe_5_22 | exact safe_5_23
def p_6 := refine parent (5,true) (some ⟨true,false,1⟩)
def p_6_0 := refine p_6 (5,false) (some ⟨false,false,0⟩)
def cert_6_0 : Tree := (.side 14 13 true (0))
theorem checked_6_0 : check 208 p_6_0 cert_6_0 = true := by decide +kernel
theorem safe_6_0 : ∀ m, compatible p_6_0 m → WeightedBound 208 m := sound 208 _ cert_6_0 (by decide) checked_6_0
def p_6_1 := refine p_6 (5,false) (some ⟨false,true,0⟩)
def cert_6_1 : Tree := (.side 11 30 true (-1))
theorem checked_6_1 : check 208 p_6_1 cert_6_1 = true := by decide +kernel
theorem safe_6_1 : ∀ m, compatible p_6_1 m → WeightedBound 208 m := sound 208 _ cert_6_1 (by decide) checked_6_1
def p_6_2 := refine p_6 (5,false) (some ⟨true,false,0⟩)
def cert_6_2 : Tree := (.side 14 11 true (0))
theorem checked_6_2 : check 208 p_6_2 cert_6_2 = true := by decide +kernel
theorem safe_6_2 : ∀ m, compatible p_6_2 m → WeightedBound 208 m := sound 208 _ cert_6_2 (by decide) checked_6_2
def p_6_3 := refine p_6 (5,false) (some ⟨true,true,0⟩)
def cert_6_3 : Tree := (.side 11 28 true (-1))
theorem checked_6_3 : check 208 p_6_3 cert_6_3 = true := by decide +kernel
theorem safe_6_3 : ∀ m, compatible p_6_3 m → WeightedBound 208 m := sound 208 _ cert_6_3 (by decide) checked_6_3
def p_6_4 := refine p_6 (5,false) (some ⟨false,false,1⟩)
def cert_6_4 : Tree := (split 21 (4,false) 6 #[
(.side 0 22 true (-2)),
(.side 0 22 true (-2)),
(.side 20 3 true (2)),
(.side 11 26 true (-1)),
(.side 14 17 true (0)),
(.side 14 17 true (0)),
(.last 23 (2,true)),
(.side 1 21 true (-2)),
(.side 0 23 true (-2)),
(.side 0 23 true (-2)),
(.last 25 (2,true)),
(.side 14 16 true (0)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 20 4 true (2)),
(.side 17 7 true (1)),
(.side 14 14 true (0)),
(.side 29 1 false (-1)),
(.side 21 1 true (3)),
(.side 44 1 false (4)),
(.side 21 1 true (3)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) .empty),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))]⟩),
(.side 14 18 true (0)),
(.side 7 21 true (-2)),
(.side 19 3 true (2))])
theorem checked_6_4 : check 208 p_6_4 cert_6_4 = true := by decide +kernel
theorem safe_6_4 : ∀ m, compatible p_6_4 m → WeightedBound 208 m := sound 208 _ cert_6_4 (by decide) checked_6_4
def p_6_5 := refine p_6 (5,false) (some ⟨false,true,1⟩)
def cert_6_5 : Tree := (.side 11 25 true (-1))
theorem checked_6_5 : check 208 p_6_5 cert_6_5 = true := by decide +kernel
theorem safe_6_5 : ∀ m, compatible p_6_5 m → WeightedBound 208 m := sound 208 _ cert_6_5 (by decide) checked_6_5
def p_6_6 := refine p_6 (5,false) (some ⟨true,false,1⟩)
def cert_6_6 : Tree := (.side 17 3 true (1))
theorem checked_6_6 : check 208 p_6_6 cert_6_6 = true := by decide +kernel
theorem safe_6_6 : ∀ m, compatible p_6_6 m → WeightedBound 208 m := sound 208 _ cert_6_6 (by decide) checked_6_6
def p_6_7 := refine p_6 (5,false) (some ⟨true,true,1⟩)
def cert_6_7 : Tree := (.side 11 23 true (-1))
theorem checked_6_7 : check 208 p_6_7 cert_6_7 = true := by decide +kernel
theorem safe_6_7 : ∀ m, compatible p_6_7 m → WeightedBound 208 m := sound 208 _ cert_6_7 (by decide) checked_6_7
def p_6_8 := refine p_6 (5,false) (some ⟨false,false,2⟩)
def cert_6_8 : Tree := (split 20 (2,true) 6 #[
(.side 0 21 true (-2)),
(.side 0 21 true (-2)),
(.last 23 (4,false)),
(.side 11 25 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,4),(false,6)],[(true,2),(true,4),(true,6)],[(false,3),(false,5),(false,7)],[(true,3),(true,5),(true,7)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty),(.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) .empty),(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) (.branch .leaf .leaf))) .empty) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))))),.empty,(.branch (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) .empty))),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty),(.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch .empty (.branch (.branch .empty .leaf) .empty))))]⟩),
(.side 14 16 true (0)),
(.side 17 6 true (1)),
(.side 1 20 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 0 22 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch .leaf (.branch (.branch .leaf .leaf) .leaf)) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 14 15 true (0)),
(.last 24 (4,false)),
(.last 24 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 14 13 true (0)),
(.last 21 (4,false)),
(.last 21 (4,false)),
(.last 21 (4,false)),
(.last 21 (4,false)),
(.side 61 54 false (1)),
(.side 0 23 true (-2)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)],[(true,1)],[(false,2),(false,6)],[(true,2),(true,6)],[(false,5)],[(true,3),(true,7),(true,5)]],#[(0,1),(2,3),(4,5),(6,7),(4,5),(6,7),(4,5),(6,7)]⟩,#[(.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .leaf)) .empty) (.branch .empty (.branch .empty (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch .empty (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)))),.empty,(.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)))),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))))]⟩),
(.side 19 2 true (2))])
theorem checked_6_8 : check 208 p_6_8 cert_6_8 = true := by decide +kernel
theorem safe_6_8 : ∀ m, compatible p_6_8 m → WeightedBound 208 m := sound 208 _ cert_6_8 (by decide) checked_6_8
def p_6_9 := refine p_6 (5,false) (some ⟨false,true,2⟩)
def cert_6_9 : Tree := (.side 11 25 true (-1))
theorem checked_6_9 : check 208 p_6_9 cert_6_9 = true := by decide +kernel
theorem safe_6_9 : ∀ m, compatible p_6_9 m → WeightedBound 208 m := sound 208 _ cert_6_9 (by decide) checked_6_9
def p_6_10 := refine p_6 (5,false) (some ⟨true,false,2⟩)
def cert_6_10 : Tree := (split 20 (2,true) 6 #[
(.side 3 21 true (-2)),
(.side 14 14 true (0)),
(.side 17 5 true (1)),
(.side 3 18 true (-2)),
(.side 7 19 true (-2)),
(.last 22 (4,false)),
(.side 14 9 true (0)),
(.last 22 (4,false)),
(.side 43 25 true (-1)),
(.side 0 23 true (-2)),
(.side 70 6 false (-2)),
(.side 2 20 true (-2)),
(.last 24 (4,false)),
(.side 17 7 true (1)),
(.side 14 9 true (0)),
(.side 14 11 true (0)),
(.last 21 (4,false)),
(.side 18 3 true (2)),
(.last 21 (4,false)),
(.side 18 3 true (2)),
(.side 31 10 false (-1)),
(.side 7 22 true (-2)),
(.side 11 19 true (-1)),
(.side 16 5 true (1))])
theorem checked_6_10 : check 208 p_6_10 cert_6_10 = true := by decide +kernel
theorem safe_6_10 : ∀ m, compatible p_6_10 m → WeightedBound 208 m := sound 208 _ cert_6_10 (by decide) checked_6_10
def p_6_11 := refine p_6 (5,false) (some ⟨true,true,2⟩)
def cert_6_11 : Tree := (.side 2 18 true (-2))
theorem checked_6_11 : check 208 p_6_11 cert_6_11 = true := by decide +kernel
theorem safe_6_11 : ∀ m, compatible p_6_11 m → WeightedBound 208 m := sound 208 _ cert_6_11 (by decide) checked_6_11
def p_6_12 := refine p_6 (5,false) (some ⟨false,false,3⟩)
def cert_6_12 : Tree := (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩)
theorem checked_6_12 : check 208 p_6_12 cert_6_12 = true := by decide +kernel
theorem safe_6_12 : ∀ m, compatible p_6_12 m → WeightedBound 208 m := sound 208 _ cert_6_12 (by decide) checked_6_12
def p_6_13 := refine p_6 (5,false) (some ⟨false,true,3⟩)
def cert_6_13 : Tree := (split 23 (4,false) 6 #[
(.side 11 32 true (-1)),
(.side 0 24 true (-2)),
(.side 21 3 true (3)),
(.side 11 42 true (-1)),
(.side 11 27 true (-1)),
(.side 14 19 true (0)),
(.last 25 (2,true)),
(.side 11 37 true (-1)),
(.side 2 22 true (-2)),
(.side 11 39 true (-1)),
(.side 11 25 true (-1)),
(.side 11 32 true (-1)),
(.side 4 20 true (-2)),
(.side 20 4 true (3)),
(.side 11 23 true (-1)),
(.side 11 30 true (-1)),
(.side 18 7 true (2)),
(.side 23 1 true (5)),
(.side 12 13 true (0)),
(.side 23 1 true (5)),
(.side 19 5 true (3)),
(.side 19 5 true (3)),
(.side 11 25 true (-1)),
(.side 19 5 true (3))])
theorem checked_6_13 : check 208 p_6_13 cert_6_13 = true := by decide +kernel
theorem safe_6_13 : ∀ m, compatible p_6_13 m → WeightedBound 208 m := sound 208 _ cert_6_13 (by decide) checked_6_13
def p_6_14 := refine p_6 (5,false) (some ⟨true,false,3⟩)
def cert_6_14 : Tree := (.side 14 9 true (0))
theorem checked_6_14 : check 208 p_6_14 cert_6_14 = true := by decide +kernel
theorem safe_6_14 : ∀ m, compatible p_6_14 m → WeightedBound 208 m := sound 208 _ cert_6_14 (by decide) checked_6_14
def p_6_15 := refine p_6 (5,false) (some ⟨true,true,3⟩)
def cert_6_15 : Tree := (.side 4 16 true (-2))
theorem checked_6_15 : check 208 p_6_15 cert_6_15 = true := by decide +kernel
theorem safe_6_15 : ∀ m, compatible p_6_15 m → WeightedBound 208 m := sound 208 _ cert_6_15 (by decide) checked_6_15
def p_6_16 := refine p_6 (5,false) (some ⟨false,false,4⟩)
def cert_6_16 : Tree := (.side 18 2 true (2))
theorem checked_6_16 : check 208 p_6_16 cert_6_16 = true := by decide +kernel
theorem safe_6_16 : ∀ m, compatible p_6_16 m → WeightedBound 208 m := sound 208 _ cert_6_16 (by decide) checked_6_16
def p_6_17 := refine p_6 (5,false) (some ⟨false,true,4⟩)
def cert_6_17 : Tree := (split 20 (4,false) 6 #[
(.side 11 25 true (-1)),
(.side 0 21 true (-2)),
(.side 20 3 true (3)),
(.side 11 35 true (-1)),
(.side 1 20 true (-2)),
(.side 14 16 true (0)),
(.last 22 (2,true)),
(.side 11 30 true (-1)),
(.side 14 15 true (0)),
(.side 11 32 true (-1)),
(.side 7 18 true (-2)),
(.side 11 25 true (-1)),
(.side 14 13 true (0)),
(.side 20 4 true (4)),
(.side 7 16 true (-2)),
(.side 11 23 true (-1)),
(.side 18 4 true (2)),
(.side 20 1 true (4)),
(.side 12 10 true (0)),
(.side 20 1 true (4)),
(.side 19 2 true (3)),
(.side 19 2 true (3)),
(.side 18 4 true (2)),
(.side 19 2 true (3))])
theorem checked_6_17 : check 208 p_6_17 cert_6_17 = true := by decide +kernel
theorem safe_6_17 : ∀ m, compatible p_6_17 m → WeightedBound 208 m := sound 208 _ cert_6_17 (by decide) checked_6_17
def p_6_18 := refine p_6 (5,false) (some ⟨true,false,4⟩)
def cert_6_18 : Tree := (.side 15 5 true (1))
theorem checked_6_18 : check 208 p_6_18 cert_6_18 = true := by decide +kernel
theorem safe_6_18 : ∀ m, compatible p_6_18 m → WeightedBound 208 m := sound 208 _ cert_6_18 (by decide) checked_6_18
def p_6_19 := refine p_6 (5,false) (some ⟨true,true,4⟩)
def cert_6_19 : Tree := (split 20 (4,false) 6 #[
(.side 3 18 true (-2)),
(.side 11 35 true (-1)),
(.side 5 16 true (-2)),
(.side 11 33 true (-1)),
(.side 1 22 true (-2)),
(.side 11 30 true (-1)),
(.side 17 4 true (1)),
(.side 11 28 true (-1)),
(.last 21 (2,true)),
(.side 11 30 true (-1)),
(.last 21 (2,true)),
(.side 11 23 true (-1)),
(.side 14 11 true (0)),
(.side 20 4 true (4)),
(.side 7 14 true (-2)),
(.side 11 21 true (-1)),
(.side 18 3 true (2)),
(.side 20 1 true (4)),
(.side 15 6 true (1)),
(.side 20 1 true (4)),
(.side 16 5 true (1)),
(.side 19 2 true (3)),
(.side 13 8 true (0)),
(.side 19 2 true (3))])
theorem checked_6_19 : check 208 p_6_19 cert_6_19 = true := by decide +kernel
theorem safe_6_19 : ∀ m, compatible p_6_19 m → WeightedBound 208 m := sound 208 _ cert_6_19 (by decide) checked_6_19
def p_6_20 := refine p_6 (5,false) (some ⟨false,false,5⟩)
def cert_6_20 : Tree := (split 22 (2,true) 6 #[
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) .empty)),(.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 11 33 true (-1)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) .empty)),(.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 11 31 true (-1)),
(.last 24 (4,false)),
(.side 11 28 true (-1)),
(.side 17 6 true (1)),
(.side 11 26 true (-1)),
(.side 65 58 false (1)),
(.side 11 28 true (-1)),
(.side 28 6 false (0)),
(.side 2 21 true (-2)),
(.side 6 26 false (3)),
(.last 26 (4,false)),
(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch .leaf (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) .empty)),(.branch .empty (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch (.branch .leaf .leaf) .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))]⟩),
(.side 4 19 true (-2)),
(.side 37 5 false (0)),
(.last 23 (4,false)),
(.side 15 8 true (1)),
(.last 23 (4,false)),
(.side 33 3 false (-1)),
(.side 38 5 false (0)),
(.side 42 3 false (2)),
(.side 16 8 true (1))])
theorem checked_6_20 : check 208 p_6_20 cert_6_20 = true := by decide +kernel
theorem safe_6_20 : ∀ m, compatible p_6_20 m → WeightedBound 208 m := sound 208 _ cert_6_20 (by decide) checked_6_20
def p_6_21 := refine p_6 (5,false) (some ⟨false,true,5⟩)
def cert_6_21 : Tree := (.side 19 1 true (3))
theorem checked_6_21 : check 208 p_6_21 cert_6_21 = true := by decide +kernel
theorem safe_6_21 : ∀ m, compatible p_6_21 m → WeightedBound 208 m := sound 208 _ cert_6_21 (by decide) checked_6_21
def p_6_22 := refine p_6 (5,false) (some ⟨true,false,5⟩)
def cert_6_22 : Tree := (split 22 (2,true) 6 #[
(.side 7 19 true (-2)),
(.side 11 26 true (-1)),
(.side 7 17 true (-2)),
(.side 11 24 true (-1)),
(.last 24 (4,false)),
(.last 24 (4,false)),
(.side 14 9 true (0)),
(.last 24 (4,false)),
(.side 65 58 false (1)),
(.side 11 35 true (-1)),
(.side 28 6 false (0)),
(.side 11 26 true (-1)),
(.side 6 26 false (3)),
(.side 7 19 true (-2)),
(.side 8 15 true (-2)),
(.side 6 17 true (-2)),
(.side 49 5 false (4)),
(.side 18 5 true (1)),
(.side 12 11 true (0)),
(.side 13 12 true (0)),
(.side 33 3 false (-1)),
(.side 11 18 true (-1)),
(.side 45 3 false (3)),
(.side 16 7 true (1))])
theorem checked_6_22 : check 208 p_6_22 cert_6_22 = true := by decide +kernel
theorem safe_6_22 : ∀ m, compatible p_6_22 m → WeightedBound 208 m := sound 208 _ cert_6_22 (by decide) checked_6_22
def p_6_23 := refine p_6 (5,false) (some ⟨true,true,5⟩)
def cert_6_23 : Tree := (.side 19 1 true (3))
theorem checked_6_23 : check 208 p_6_23 cert_6_23 = true := by decide +kernel
theorem safe_6_23 : ∀ m, compatible p_6_23 m → WeightedBound 208 m := sound 208 _ cert_6_23 (by decide) checked_6_23
theorem safe_6 : ∀ m, compatible p_6 m → WeightedBound 208 m := by
  apply split_safe 208 p_6 19 (5,false) 6 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_6_0 | exact safe_6_1 | exact safe_6_2 | exact safe_6_3 | exact safe_6_4 | exact safe_6_5 | exact safe_6_6 | exact safe_6_7 | exact safe_6_8 | exact safe_6_9 | exact safe_6_10 | exact safe_6_11 | exact safe_6_12 | exact safe_6_13 | exact safe_6_14 | exact safe_6_15 | exact safe_6_16 | exact safe_6_17 | exact safe_6_18 | exact safe_6_19 | exact safe_6_20 | exact safe_6_21 | exact safe_6_22 | exact safe_6_23
end BB6.Agent47Root51
