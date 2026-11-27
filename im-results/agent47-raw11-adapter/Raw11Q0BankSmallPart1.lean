import PhaseTree
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw11Q0BankSmall
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def p22 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
def p22_0 : PartialMachine := refine p22 (4,false) (some ⟨false,false,0⟩)
theorem safe_p22_0 : ∀ m, compatible p22_0 m → WeightedBound 100 m :=
  sound 100 p22_0 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_1 : PartialMachine := refine p22 (4,false) (some ⟨false,true,0⟩)
theorem safe_p22_1 : ∀ m, compatible p22_1 m → WeightedBound 100 m :=
  sound 100 p22_1 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_2 : PartialMachine := refine p22 (4,false) (some ⟨true,false,0⟩)
theorem safe_p22_2 : ∀ m, compatible p22_2 m → WeightedBound 100 m :=
  sound 100 p22_2 (.side 44 3 true (3)) (by decide) (by decide +kernel)
def p22_3 : PartialMachine := refine p22 (4,false) (some ⟨true,true,0⟩)
theorem safe_p22_3 : ∀ m, compatible p22_3 m → WeightedBound 100 m :=
  sound 100 p22_3 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_4 : PartialMachine := refine p22 (4,false) (some ⟨false,false,1⟩)
theorem safe_p22_4 : ∀ m, compatible p22_4 m → WeightedBound 100 m :=
  sound 100 p22_4 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_5 : PartialMachine := refine p22 (4,false) (some ⟨false,true,1⟩)
theorem safe_p22_5 : ∀ m, compatible p22_5 m → WeightedBound 100 m :=
  sound 100 p22_5 (.side 40 15 true (1)) (by decide) (by decide +kernel)
def p22_6 : PartialMachine := refine p22 (4,false) (some ⟨true,false,1⟩)
theorem safe_p22_6 : ∀ m, compatible p22_6 m → WeightedBound 100 m :=
  sound 100 p22_6 (.side 42 3 true (2)) (by decide) (by decide +kernel)
def p22_7 : PartialMachine := refine p22 (4,false) (some ⟨true,true,1⟩)
theorem safe_p22_7 : ∀ m, compatible p22_7 m → WeightedBound 100 m :=
  sound 100 p22_7 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_8 : PartialMachine := refine p22 (4,false) (some ⟨false,false,2⟩)
theorem safe_p22_8 : ∀ m, compatible p22_8 m → WeightedBound 100 m :=
  sound 100 p22_8 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_9 : PartialMachine := refine p22 (4,false) (some ⟨false,true,2⟩)
theorem safe_p22_9 : ∀ m, compatible p22_9 m → WeightedBound 100 m :=
  sound 100 p22_9 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_10 : PartialMachine := refine p22 (4,false) (some ⟨true,false,2⟩)
theorem safe_p22_10 : ∀ m, compatible p22_10 m → WeightedBound 100 m :=
  sound 100 p22_10 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_11 : PartialMachine := refine p22 (4,false) (some ⟨true,true,2⟩)
theorem safe_p22_11 : ∀ m, compatible p22_11 m → WeightedBound 100 m :=
  sound 100 p22_11 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_12 : PartialMachine := refine p22 (4,false) (some ⟨false,false,3⟩)
theorem safe_p22_12 : ∀ m, compatible p22_12 m → WeightedBound 100 m :=
  sound 100 p22_12 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_13 : PartialMachine := refine p22 (4,false) (some ⟨false,true,3⟩)
theorem safe_p22_13 : ∀ m, compatible p22_13 m → WeightedBound 100 m :=
  sound 100 p22_13 (.side 44 4 true (4)) (by decide) (by decide +kernel)
def p22_14 : PartialMachine := refine p22 (4,false) (some ⟨true,false,3⟩)
theorem safe_p22_14 : ∀ m, compatible p22_14 m → WeightedBound 100 m :=
  sound 100 p22_14 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_15 : PartialMachine := refine p22 (4,false) (some ⟨true,true,3⟩)
theorem safe_p22_15 : ∀ m, compatible p22_15 m → WeightedBound 100 m :=
  sound 100 p22_15 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_16 : PartialMachine := refine p22 (4,false) (some ⟨false,false,4⟩)
theorem safe_p22_16 : ∀ m, compatible p22_16 m → WeightedBound 100 m :=
  sound 100 p22_16 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_17 : PartialMachine := refine p22 (4,false) (some ⟨false,true,4⟩)
theorem safe_p22_17 : ∀ m, compatible p22_17 m → WeightedBound 100 m :=
  sound 100 p22_17 (.side 44 1 true (4)) (by decide) (by decide +kernel)
def p22_18 : PartialMachine := refine p22 (4,false) (some ⟨true,false,4⟩)
theorem safe_p22_18 : ∀ m, compatible p22_18 m → WeightedBound 100 m :=
  sound 100 p22_18 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p22_19 : PartialMachine := refine p22 (4,false) (some ⟨true,true,4⟩)
theorem safe_p22_19 : ∀ m, compatible p22_19 m → WeightedBound 100 m :=
  sound 100 p22_19 (.side 44 1 true (4)) (by decide) (by decide +kernel)
def p22_20 : PartialMachine := refine p22 (4,false) (some ⟨false,false,5⟩)
theorem safe_p22_20 : ∀ m, compatible p22_20 m → WeightedBound 100 m :=
  sound 100 p22_20 (BB6.Agent5PhaseTree.split 45 (5,false) 6 #[(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.side 56 25 false (0)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.side 0 68 false (4)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.side 44 5 true (3)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),.empty]⟩),(.side 44 2 true (3)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),.empty]⟩),(.last 47 (5,true)),(.last 46 (5,true)),(.side 45 1 true (3)),(.last 46 (5,true)),(.side 45 1 true (3))]) (by decide) (by decide +kernel)
def p22_21 : PartialMachine := refine p22 (4,false) (some ⟨false,true,5⟩)
theorem safe_p22_21 : ∀ m, compatible p22_21 m → WeightedBound 100 m :=
  sound 100 p22_21 (BB6.Agent5PhaseTree.split 45 (5,false) 6 #[(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 44 4 true (4)),(.side 36 23 true (-1)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 40 16 true (1)),(.side 42 4 true (2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 41 6 true (1)),(.side 40 15 true (1)),(.side 44 5 true (3)),(.side 44 5 true (4)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 40 13 true (1)),(.side 44 2 true (4)),(.side 44 2 true (4)),(.last 47 (5,true)),(.side 44 2 true (4)),(.last 48 (5,true)),(.side 45 1 true (5)),(.last 48 (5,true)),(.side 45 1 true (5))]) (by decide) (by decide +kernel)
def p22_22 : PartialMachine := refine p22 (4,false) (some ⟨true,false,5⟩)
theorem safe_p22_22 : ∀ m, compatible p22_22 m → WeightedBound 100 m :=
  sound 100 p22_22 (BB6.Agent5PhaseTree.split 45 (5,false) 6 #[(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty]⟩),(.side 44 3 true (3)),(.side 40 7 true (1)),(.side 44 3 true (3)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty]⟩),(.side 43 3 true (3)),(.side 39 7 true (1)),(.side 43 3 true (3)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),.empty]⟩),(.last 46 (5,true)),(.last 46 (5,true)),(.last 46 (5,true)),(.last 46 (5,true))]) (by decide) (by decide +kernel)
def p22_23 : PartialMachine := refine p22 (4,false) (some ⟨true,true,5⟩)
theorem safe_p22_23 : ∀ m, compatible p22_23 m → WeightedBound 100 m :=
  sound 100 p22_23 (BB6.Agent5PhaseTree.split 45 (5,false) 6 #[(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 44 3 true (4)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 43 3 true (3)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 44 5 true (4)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 44 2 true (4)),(.side 40 6 true (1)),(.side 44 2 true (4)),(.last 46 (5,true)),(.side 45 1 true (5)),(.last 46 (5,true)),(.side 45 1 true (5))]) (by decide) (by decide +kernel)
theorem safe_p22 : ∀ m, compatible p22 m → WeightedBound 100 m := by
  apply split_safe 100 p22 44 (4,false) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_p22_0 | exact safe_p22_1 | exact safe_p22_2 | exact safe_p22_3 | exact safe_p22_4 | exact safe_p22_5 | exact safe_p22_6 | exact safe_p22_7 | exact safe_p22_8 | exact safe_p22_9 | exact safe_p22_10 | exact safe_p22_11 | exact safe_p22_12 | exact safe_p22_13 | exact safe_p22_14 | exact safe_p22_15 | exact safe_p22_16 | exact safe_p22_17 | exact safe_p22_18 | exact safe_p22_19 | exact safe_p22_20 | exact safe_p22_21 | exact safe_p22_22 | exact safe_p22_23 | (simp at h)
theorem cover_p22 : Cover (WeightedBound 100) p22 := .leaf _ safe_p22

def p23 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p23 : ∀ m, compatible p23 m → WeightedBound 100 m :=
  sound 100 p23 (.side 3 14 false (2)) (by decide) (by decide +kernel)
theorem cover_p23 : Cover (WeightedBound 100) p23 := .leaf _ safe_p23

def p24 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p24 : ∀ m, compatible p24 m → WeightedBound 100 m :=
  sound 100 p24 (.side 6 16 false (2)) (by decide) (by decide +kernel)
theorem cover_p24 : Cover (WeightedBound 100) p24 := .leaf _ safe_p24

def p29 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,true,0⟩)
  | _,_ => none)
theorem safe_p29 : ∀ m, compatible p29 m → WeightedBound 100 m :=
  sound 100 p29 (.side 13 9 true (-1)) (by decide) (by decide +kernel)
theorem cover_p29 : Cover (WeightedBound 100) p29 := .leaf _ safe_p29

def p31 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨true,true,0⟩)
  | _,_ => none)
theorem safe_p31 : ∀ m, compatible p31 m → WeightedBound 100 m :=
  sound 100 p31 (.side 7 12 false (2)) (by decide) (by decide +kernel)
theorem cover_p31 : Cover (WeightedBound 100) p31 := .leaf _ safe_p31

def p32 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,1⟩)
  | _,_ => none)
theorem safe_p32 : ∀ m, compatible p32 m → WeightedBound 100 m :=
  sound 100 p32 (.side 1 12 false (2)) (by decide) (by decide +kernel)
theorem cover_p32 : Cover (WeightedBound 100) p32 := .leaf _ safe_p32

def p36 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,2⟩)
  | _,_ => none)
theorem safe_p36 : ∀ m, compatible p36 m → WeightedBound 100 m :=
  sound 100 p36 (.side 7 10 false (1)) (by decide) (by decide +kernel)
theorem cover_p36 : Cover (WeightedBound 100) p36 := .leaf _ safe_p36

def p38 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨true,false,2⟩)
  | _,_ => none)
theorem safe_p38 : ∀ m, compatible p38 m → WeightedBound 100 m :=
  sound 100 p38 (.side 7 10 false (1)) (by decide) (by decide +kernel)
theorem cover_p38 : Cover (WeightedBound 100) p38 := .leaf _ safe_p38

def p40 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,3⟩)
  | _,_ => none)
theorem safe_p40 : ∀ m, compatible p40 m → WeightedBound 100 m :=
  sound 100 p40 (.side 7 8 false (1)) (by decide) (by decide +kernel)
theorem cover_p40 : Cover (WeightedBound 100) p40 := .leaf _ safe_p40

def p42 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨true,false,3⟩)
  | _,_ => none)
theorem safe_p42 : ∀ m, compatible p42 m → WeightedBound 100 m :=
  sound 100 p42 (.side 7 8 false (1)) (by decide) (by decide +kernel)
theorem cover_p42 : Cover (WeightedBound 100) p42 := .leaf _ safe_p42

def p43 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨true,true,3⟩)
  | _,_ => none)
theorem safe_p43 : ∀ m, compatible p43 m → WeightedBound 100 m :=
  sound 100 p43 (.side 7 10 false (1)) (by decide) (by decide +kernel)
theorem cover_p43 : Cover (WeightedBound 100) p43 := .leaf _ safe_p43

def p54 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,true,3⟩)
  | _,_ => none)
theorem safe_p54 : ∀ m, compatible p54 m → WeightedBound 100 m :=
  sound 100 p54 (.side 4 3 true (1)) (by decide) (by decide +kernel)
theorem cover_p54 : Cover (WeightedBound 100) p54 := .leaf _ safe_p54

def p59 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,true,0⟩)
  | _,_ => none)
theorem safe_p59 : ∀ m, compatible p59 m → WeightedBound 100 m :=
  sound 100 p59 (.side 0 5 true (0)) (by decide) (by decide +kernel)
theorem cover_p59 : Cover (WeightedBound 100) p59 := .leaf _ safe_p59

def p61 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | _,_ => none)
theorem safe_p61 : ∀ m, compatible p61 m → WeightedBound 100 m :=
  sound 100 p61 (.side 1 4 true (1)) (by decide) (by decide +kernel)
theorem cover_p61 : Cover (WeightedBound 100) p61 := .leaf _ safe_p61

def p63 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,true,1⟩)
  | _,_ => none)
theorem safe_p63 : ∀ m, compatible p63 m → WeightedBound 100 m :=
  sound 100 p63 (.side 1 4 true (1)) (by decide) (by decide +kernel)
theorem cover_p63 : Cover (WeightedBound 100) p63 := .leaf _ safe_p63

def p65 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨false,true,2⟩)
  | _,_ => none)
theorem safe_p65 : ∀ m, compatible p65 m → WeightedBound 100 m :=
  sound 100 p65 (.side 0 6 true (0)) (by decide) (by decide +kernel)
theorem cover_p65 : Cover (WeightedBound 100) p65 := .leaf _ safe_p65

def p67 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,true,2⟩)
  | _,_ => none)
theorem safe_p67 : ∀ m, compatible p67 m → WeightedBound 100 m :=
  sound 100 p67 (.side 2 3 true (1)) (by decide) (by decide +kernel)
theorem cover_p67 : Cover (WeightedBound 100) p67 := .leaf _ safe_p67

def p69 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨false,true,3⟩)
  | _,_ => none)
theorem safe_p69 : ∀ m, compatible p69 m → WeightedBound 100 m :=
  sound 100 p69 (.side 4 1 true (2)) (by decide) (by decide +kernel)
theorem cover_p69 : Cover (WeightedBound 100) p69 := .leaf _ safe_p69

def p71 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,true,3⟩)
  | _,_ => none)
theorem safe_p71 : ∀ m, compatible p71 m → WeightedBound 100 m :=
  sound 100 p71 (.side 4 1 true (2)) (by decide) (by decide +kernel)
theorem cover_p71 : Cover (WeightedBound 100) p71 := .leaf _ safe_p71

def p79 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | _,_ => none)
theorem safe_p79 : ∀ m, compatible p79 m → WeightedBound 100 m :=
  sound 100 p79 (.side 3 2 true (0)) (by decide) (by decide +kernel)
theorem cover_p79 : Cover (WeightedBound 100) p79 := .leaf _ safe_p79

def p84 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,true => some (some ⟨false,false,2⟩)
  | _,_ => none)
theorem safe_p84 : ∀ m, compatible p84 m → WeightedBound 100 m :=
  sound 100 p84 (.side 0 6 false (2)) (by decide) (by decide +kernel)
theorem cover_p84 : Cover (WeightedBound 100) p84 := .leaf _ safe_p84

def p96 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p96 : ∀ m, compatible p96 m → WeightedBound 100 m :=
  sound 100 p96 (.side 0 5 true (0)) (by decide) (by decide +kernel)
theorem cover_p96 : Cover (WeightedBound 100) p96 := .leaf _ safe_p96

def p97 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨false,true,0⟩)
  | _,_ => none)
theorem safe_p97 : ∀ m, compatible p97 m → WeightedBound 100 m :=
  sound 100 p97 (.side 0 5 true (0)) (by decide) (by decide +kernel)
theorem cover_p97 : Cover (WeightedBound 100) p97 := .leaf _ safe_p97

def p99 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,true,0⟩)
  | _,_ => none)
theorem safe_p99 : ∀ m, compatible p99 m → WeightedBound 100 m :=
  sound 100 p99 (.side 0 5 true (0)) (by decide) (by decide +kernel)
theorem cover_p99 : Cover (WeightedBound 100) p99 := .leaf _ safe_p99

def p100 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨false,false,1⟩)
  | _,_ => none)
theorem safe_p100 : ∀ m, compatible p100 m → WeightedBound 100 m :=
  sound 100 p100 (.side 1 4 true (1)) (by decide) (by decide +kernel)
theorem cover_p100 : Cover (WeightedBound 100) p100 := .leaf _ safe_p100

def p101 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨false,true,1⟩)
  | _,_ => none)
theorem safe_p101 : ∀ m, compatible p101 m → WeightedBound 100 m :=
  sound 100 p101 (.side 1 4 true (1)) (by decide) (by decide +kernel)
theorem cover_p101 : Cover (WeightedBound 100) p101 := .leaf _ safe_p101

def p103 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,true,1⟩)
  | _,_ => none)
theorem safe_p103 : ∀ m, compatible p103 m → WeightedBound 100 m :=
  sound 100 p103 (.side 1 4 true (1)) (by decide) (by decide +kernel)
theorem cover_p103 : Cover (WeightedBound 100) p103 := .leaf _ safe_p103

def p104 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨false,false,2⟩)
  | _,_ => none)
theorem safe_p104 : ∀ m, compatible p104 m → WeightedBound 100 m :=
  sound 100 p104 (.side 0 9 false (2)) (by decide) (by decide +kernel)
theorem cover_p104 : Cover (WeightedBound 100) p104 := .leaf _ safe_p104

def p105 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨false,true,2⟩)
  | _,_ => none)
theorem safe_p105 : ∀ m, compatible p105 m → WeightedBound 100 m :=
  sound 100 p105 (.side 0 6 true (0)) (by decide) (by decide +kernel)
theorem cover_p105 : Cover (WeightedBound 100) p105 := .leaf _ safe_p105

def p107 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,true,2⟩)
  | _,_ => none)
theorem safe_p107 : ∀ m, compatible p107 m → WeightedBound 100 m :=
  sound 100 p107 (.side 2 3 true (1)) (by decide) (by decide +kernel)
theorem cover_p107 : Cover (WeightedBound 100) p107 := .leaf _ safe_p107

def p109 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨false,true,3⟩)
  | _,_ => none)
theorem safe_p109 : ∀ m, compatible p109 m → WeightedBound 100 m :=
  sound 100 p109 (.side 4 1 true (2)) (by decide) (by decide +kernel)
theorem cover_p109 : Cover (WeightedBound 100) p109 := .leaf _ safe_p109

def p111 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,true,3⟩)
  | _,_ => none)
theorem safe_p111 : ∀ m, compatible p111 m → WeightedBound 100 m :=
  sound 100 p111 (.side 4 1 true (2)) (by decide) (by decide +kernel)
theorem cover_p111 : Cover (WeightedBound 100) p111 := .leaf _ safe_p111

def p116 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p116 : ∀ m, compatible p116 m → WeightedBound 100 m :=
  sound 100 p116 (.side 0 5 false (2)) (by decide) (by decide +kernel)
theorem cover_p116 : Cover (WeightedBound 100) p116 := .leaf _ safe_p116

def p117 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,true => some (some ⟨false,true,0⟩)
  | _,_ => none)
theorem safe_p117 : ∀ m, compatible p117 m → WeightedBound 100 m :=
  sound 100 p117 (.side 0 5 true (0)) (by decide) (by decide +kernel)
theorem cover_p117 : Cover (WeightedBound 100) p117 := .leaf _ safe_p117

def p119 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,true => some (some ⟨true,true,0⟩)
  | _,_ => none)
theorem safe_p119 : ∀ m, compatible p119 m → WeightedBound 100 m :=
  sound 100 p119 (.side 0 5 true (0)) (by decide) (by decide +kernel)
theorem cover_p119 : Cover (WeightedBound 100) p119 := .leaf _ safe_p119

def p123 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,true => some (some ⟨true,true,1⟩)
  | _,_ => none)
theorem safe_p123 : ∀ m, compatible p123 m → WeightedBound 100 m :=
  sound 100 p123 (.side 1 4 true (0)) (by decide) (by decide +kernel)
theorem cover_p123 : Cover (WeightedBound 100) p123 := .leaf _ safe_p123

def p124 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,true => some (some ⟨false,false,2⟩)
  | _,_ => none)
theorem safe_p124 : ∀ m, compatible p124 m → WeightedBound 100 m :=
  sound 100 p124 (.side 0 6 false (2)) (by decide) (by decide +kernel)
theorem cover_p124 : Cover (WeightedBound 100) p124 := .leaf _ safe_p124

def p125 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨false,false,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,true => some (some ⟨false,true,2⟩)
  | _,_ => none)
theorem safe_p125 : ∀ m, compatible p125 m → WeightedBound 100 m :=
  sound 100 p125 (.side 0 6 true (0)) (by decide) (by decide +kernel)
theorem cover_p125 : Cover (WeightedBound 100) p125 := .leaf _ safe_p125

end BB6.Agent47Raw11Q0BankSmall
