import PhaseTree
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw11Q0BankSmall
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def p0 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,false,4⟩)
  | _,_ => none)
theorem safe_p0 : ∀ m, compatible p0 m → WeightedBound 100 m :=
  sound 100 p0 (.last 20 (5,true)) (by decide) (by decide +kernel)
theorem cover_p0 : Cover (WeightedBound 100) p0 := .leaf _ safe_p0

def p1 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,true,4⟩)
  | _,_ => none)
theorem safe_p1 : ∀ m, compatible p1 m → WeightedBound 100 m :=
  sound 100 p1 (.side 17 2 true (2)) (by decide) (by decide +kernel)
theorem cover_p1 : Cover (WeightedBound 100) p1 := .leaf _ safe_p1

def p2 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,4⟩)
  | _,_ => none)
theorem safe_p2 : ∀ m, compatible p2 m → WeightedBound 100 m :=
  sound 100 p2 (.last 20 (5,true)) (by decide) (by decide +kernel)
theorem cover_p2 : Cover (WeightedBound 100) p2 := .leaf _ safe_p2

def p3 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,true,4⟩)
  | _,_ => none)
theorem safe_p3 : ∀ m, compatible p3 m → WeightedBound 100 m :=
  sound 100 p3 (.last 20 (5,true)) (by decide) (by decide +kernel)
theorem cover_p3 : Cover (WeightedBound 100) p3 := .leaf _ safe_p3

def p4 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,false,5⟩)
  | _,_ => none)
theorem safe_p4 : ∀ m, compatible p4 m → WeightedBound 100 m :=
  sound 100 p4 (.last 20 (5,true)) (by decide) (by decide +kernel)
theorem cover_p4 : Cover (WeightedBound 100) p4 := .leaf _ safe_p4

def p5 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨false,true,5⟩)
  | _,_ => none)
theorem safe_p5 : ∀ m, compatible p5 m → WeightedBound 100 m :=
  sound 100 p5 (.side 18 1 true (2)) (by decide) (by decide +kernel)
theorem cover_p5 : Cover (WeightedBound 100) p5 := .leaf _ safe_p5

def p6 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,false,5⟩)
  | _,_ => none)
theorem safe_p6 : ∀ m, compatible p6 m → WeightedBound 100 m :=
  sound 100 p6 (.last 20 (5,true)) (by decide) (by decide +kernel)
theorem cover_p6 : Cover (WeightedBound 100) p6 := .leaf _ safe_p6

def p7 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨false,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | 5,false => some (some ⟨true,true,5⟩)
  | _,_ => none)
theorem safe_p7 : ∀ m, compatible p7 m → WeightedBound 100 m :=
  sound 100 p7 (.side 18 1 true (2)) (by decide) (by decide +kernel)
theorem cover_p7 : Cover (WeightedBound 100) p7 := .leaf _ safe_p7

def p8 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨false,true,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p8 : ∀ m, compatible p8 m → WeightedBound 100 m :=
  sound 100 p8 (BB6.Agent5PhaseTree.split 18 (5,false) 6 #[(.side 0 19 true (-2)),(.side 0 19 true (-2)),(.side 16 4 true (2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 11 42 true (-1)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 1 18 true (-2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 0 20 true (-2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 16 5 true (2)),(.side 16 5 true (2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 17 2 true (3)),(.side 17 2 true (3)),(.last 20 (5,true)),(.side 17 2 true (3)),(.last 22 (5,true)),(.side 18 1 true (4)),(.last 22 (5,true)),(.side 18 1 true (4))]) (by decide) (by decide +kernel)
theorem cover_p8 : Cover (WeightedBound 100) p8 := .leaf _ safe_p8

def p9 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨true,false,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p9 : ∀ m, compatible p9 m → WeightedBound 100 m :=
  sound 100 p9 (BB6.Agent5PhaseTree.split 18 (5,false) 6 #[(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .leaf),.empty]⟩),(.side 16 3 true (2)),(.side 14 5 true (0)),(.side 16 3 true (2)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.last 20 (5,true)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.last 20 (5,true)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .empty .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty (.branch .empty .leaf))),.empty]⟩),(.last 20 (5,true)),(.last 19 (5,true)),(.last 20 (5,true)),(.last 19 (5,true))]) (by decide) (by decide +kernel)
theorem cover_p9 : Cover (WeightedBound 100) p9 := .leaf _ safe_p9

def p10 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,false => some (some ⟨true,true,5⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p10 : ∀ m, compatible p10 m → WeightedBound 100 m :=
  sound 100 p10 (BB6.Agent5PhaseTree.split 18 (5,false) 6 #[(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 16 3 true (2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 0 21 true (-2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 15 4 true (1)),(.side 2 17 true (-2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 16 5 true (2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 4 15 true (-2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 17 2 true (3)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),.empty]⟩),(.side 17 2 true (3)),(.last 19 (5,true)),(.side 18 1 true (4)),(.last 19 (5,true)),(.side 18 1 true (4))]) (by decide) (by decide +kernel)
theorem cover_p10 : Cover (WeightedBound 100) p10 := .leaf _ safe_p10

def p11 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p11 : ∀ m, compatible p11 m → WeightedBound 100 m :=
  sound 100 p11 (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .leaf .leaf) .empty) .empty) (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty))),.empty,.empty]⟩) (by decide) (by decide +kernel)
theorem cover_p11 : Cover (WeightedBound 100) p11 := .leaf _ safe_p11

def p12 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,1⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
def p12_0 : PartialMachine := refine p12 (4,false) (some ⟨false,false,0⟩)
theorem safe_p12_0 : ∀ m, compatible p12_0 m → WeightedBound 100 m :=
  sound 100 p12_0 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_1 : PartialMachine := refine p12 (4,false) (some ⟨false,true,0⟩)
theorem safe_p12_1 : ∀ m, compatible p12_1 m → WeightedBound 100 m :=
  sound 100 p12_1 (.side 0 18 true (-2)) (by decide) (by decide +kernel)
def p12_2 : PartialMachine := refine p12 (4,false) (some ⟨true,false,0⟩)
theorem safe_p12_2 : ∀ m, compatible p12_2 m → WeightedBound 100 m :=
  sound 100 p12_2 (.side 16 3 true (2)) (by decide) (by decide +kernel)
def p12_3 : PartialMachine := refine p12 (4,false) (some ⟨true,true,0⟩)
theorem safe_p12_3 : ∀ m, compatible p12_3 m → WeightedBound 100 m :=
  sound 100 p12_3 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_4 : PartialMachine := refine p12 (4,false) (some ⟨false,false,1⟩)
theorem safe_p12_4 : ∀ m, compatible p12_4 m → WeightedBound 100 m :=
  sound 100 p12_4 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_5 : PartialMachine := refine p12 (4,false) (some ⟨false,true,1⟩)
theorem safe_p12_5 : ∀ m, compatible p12_5 m → WeightedBound 100 m :=
  sound 100 p12_5 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_6 : PartialMachine := refine p12 (4,false) (some ⟨true,false,1⟩)
theorem safe_p12_6 : ∀ m, compatible p12_6 m → WeightedBound 100 m :=
  sound 100 p12_6 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_7 : PartialMachine := refine p12 (4,false) (some ⟨true,true,1⟩)
theorem safe_p12_7 : ∀ m, compatible p12_7 m → WeightedBound 100 m :=
  sound 100 p12_7 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_8 : PartialMachine := refine p12 (4,false) (some ⟨false,false,2⟩)
theorem safe_p12_8 : ∀ m, compatible p12_8 m → WeightedBound 100 m :=
  sound 100 p12_8 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_9 : PartialMachine := refine p12 (4,false) (some ⟨false,true,2⟩)
theorem safe_p12_9 : ∀ m, compatible p12_9 m → WeightedBound 100 m :=
  sound 100 p12_9 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_10 : PartialMachine := refine p12 (4,false) (some ⟨true,false,2⟩)
theorem safe_p12_10 : ∀ m, compatible p12_10 m → WeightedBound 100 m :=
  sound 100 p12_10 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_11 : PartialMachine := refine p12 (4,false) (some ⟨true,true,2⟩)
theorem safe_p12_11 : ∀ m, compatible p12_11 m → WeightedBound 100 m :=
  sound 100 p12_11 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_12 : PartialMachine := refine p12 (4,false) (some ⟨false,false,3⟩)
theorem safe_p12_12 : ∀ m, compatible p12_12 m → WeightedBound 100 m :=
  sound 100 p12_12 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_13 : PartialMachine := refine p12 (4,false) (some ⟨false,true,3⟩)
theorem safe_p12_13 : ∀ m, compatible p12_13 m → WeightedBound 100 m :=
  sound 100 p12_13 (.side 16 4 true (2)) (by decide) (by decide +kernel)
def p12_14 : PartialMachine := refine p12 (4,false) (some ⟨true,false,3⟩)
theorem safe_p12_14 : ∀ m, compatible p12_14 m → WeightedBound 100 m :=
  sound 100 p12_14 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_15 : PartialMachine := refine p12 (4,false) (some ⟨true,true,3⟩)
theorem safe_p12_15 : ∀ m, compatible p12_15 m → WeightedBound 100 m :=
  sound 100 p12_15 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_16 : PartialMachine := refine p12 (4,false) (some ⟨false,false,4⟩)
theorem safe_p12_16 : ∀ m, compatible p12_16 m → WeightedBound 100 m :=
  sound 100 p12_16 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_17 : PartialMachine := refine p12 (4,false) (some ⟨false,true,4⟩)
theorem safe_p12_17 : ∀ m, compatible p12_17 m → WeightedBound 100 m :=
  sound 100 p12_17 (.side 17 1 true (3)) (by decide) (by decide +kernel)
def p12_18 : PartialMachine := refine p12 (4,false) (some ⟨true,false,4⟩)
theorem safe_p12_18 : ∀ m, compatible p12_18 m → WeightedBound 100 m :=
  sound 100 p12_18 (.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.leaf,.empty,.empty]⟩) (by decide) (by decide +kernel)
def p12_19 : PartialMachine := refine p12 (4,false) (some ⟨true,true,4⟩)
theorem safe_p12_19 : ∀ m, compatible p12_19 m → WeightedBound 100 m :=
  sound 100 p12_19 (.side 17 1 true (3)) (by decide) (by decide +kernel)
def p12_20 : PartialMachine := refine p12 (4,false) (some ⟨false,false,5⟩)
theorem safe_p12_20 : ∀ m, compatible p12_20 m → WeightedBound 100 m :=
  sound 100 p12_20 (BB6.Agent5PhaseTree.split 18 (5,false) 6 #[(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.side 16 61 false (3)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1),(false,2)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.side 15 4 true (1)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.side 16 5 true (2)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),.empty]⟩),(.side 17 2 true (2)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),.empty]⟩),(.last 20 (5,true)),(.last 19 (5,true)),(.side 18 1 true (2)),(.last 19 (5,true)),(.side 18 1 true (2))]) (by decide) (by decide +kernel)
def p12_21 : PartialMachine := refine p12 (4,false) (some ⟨false,true,5⟩)
theorem safe_p12_21 : ∀ m, compatible p12_21 m → WeightedBound 100 m :=
  sound 100 p12_21 (BB6.Agent5PhaseTree.split 18 (5,false) 6 #[(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 0 19 true (-2)),(.side 16 4 true (2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 1 18 true (-2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 0 20 true (-2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 16 5 true (2)),(.side 16 5 true (2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 17 2 true (3)),(.side 17 2 true (3)),(.last 20 (5,true)),(.side 17 2 true (3)),(.last 21 (5,true)),(.side 18 1 true (4)),(.last 21 (5,true)),(.side 18 1 true (4))]) (by decide) (by decide +kernel)
def p12_22 : PartialMachine := refine p12 (4,false) (some ⟨true,false,5⟩)
theorem safe_p12_22 : ∀ m, compatible p12_22 m → WeightedBound 100 m :=
  sound 100 p12_22 (BB6.Agent5PhaseTree.split 18 (5,false) 6 #[(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty]⟩),(.side 16 3 true (2)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),(.branch .leaf .leaf),.empty]⟩),(.side 16 3 true (2)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch (.branch .empty .leaf) .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .empty .leaf) .empty),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,#[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) .empty),(.branch (.branch .leaf .leaf) .leaf),(.branch .empty .leaf),.empty]⟩),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch .leaf (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .leaf .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),.empty]⟩),(.last 19 (5,true)),(.last 19 (5,true)),(.last 19 (5,true)),(.last 19 (5,true))]) (by decide) (by decide +kernel)
def p12_23 : PartialMachine := refine p12 (4,false) (some ⟨true,true,5⟩)
theorem safe_p12_23 : ∀ m, compatible p12_23 m → WeightedBound 100 m :=
  sound 100 p12_23 (BB6.Agent5PhaseTree.split 18 (5,false) 6 #[(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 16 3 true (2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 15 4 true (1)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 16 5 true (2)),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.automata ⟨⟨#[[(false,0),(true,0)]],#[(0,0)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,(.branch .leaf .leaf),.leaf,.empty]⟩),(.side 17 2 true (3)),(.automata ⟨⟨#[[(false,0)],[(true,0),(true,1),(true,2)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,#[(.branch (.branch .leaf .leaf) (.branch (.branch .leaf .leaf) .leaf)),(.branch (.branch (.branch (.branch .leaf .leaf) .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),(.branch .empty (.branch .empty .leaf)),.empty]⟩),(.side 17 2 true (3)),(.last 19 (5,true)),(.side 18 1 true (4)),(.last 19 (5,true)),(.side 18 1 true (4))]) (by decide) (by decide +kernel)
theorem safe_p12 : ∀ m, compatible p12 m → WeightedBound 100 m := by
  apply split_safe 100 p12 17 (4,false) 5 (by decide) (by decide +kernel) (by decide) (by decide)
  intro mv h
  rcases mv with ⟨w,r,q⟩
  rcases statesCases q with hq|hq|hq|hq|hq|hq <;> subst q <;> cases w <;> cases r <;> first | exact safe_p12_0 | exact safe_p12_1 | exact safe_p12_2 | exact safe_p12_3 | exact safe_p12_4 | exact safe_p12_5 | exact safe_p12_6 | exact safe_p12_7 | exact safe_p12_8 | exact safe_p12_9 | exact safe_p12_10 | exact safe_p12_11 | exact safe_p12_12 | exact safe_p12_13 | exact safe_p12_14 | exact safe_p12_15 | exact safe_p12_16 | exact safe_p12_17 | exact safe_p12_18 | exact safe_p12_19 | exact safe_p12_20 | exact safe_p12_21 | exact safe_p12_22 | exact safe_p12_23 | (simp at h)
theorem cover_p12 : Cover (WeightedBound 100) p12 := .leaf _ safe_p12

def p13 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,2⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p13 : ∀ m, compatible p13 m → WeightedBound 100 m :=
  sound 100 p13 (.side 0 20 false (2)) (by decide) (by decide +kernel)
theorem cover_p13 : Cover (WeightedBound 100) p13 := .leaf _ safe_p13

def p14 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,2⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p14 : ∀ m, compatible p14 m → WeightedBound 100 m :=
  sound 100 p14 (.side 0 46 true (-4)) (by decide) (by decide +kernel)
theorem cover_p14 : Cover (WeightedBound 100) p14 := .leaf _ safe_p14

def p15 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,2⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p15 : ∀ m, compatible p15 m → WeightedBound 100 m :=
  sound 100 p15 (.side 16 6 false (0)) (by decide) (by decide +kernel)
theorem cover_p15 : Cover (WeightedBound 100) p15 := .leaf _ safe_p15

def p16 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,2⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p16 : ∀ m, compatible p16 m → WeightedBound 100 m :=
  sound 100 p16 (.automata ⟨⟨#[[(false,0)],[(true,0),(true,1)],[(false,1)]],#[(0,1),(2,1),(2,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]],#[(0,1),(2,3),(2,3),(2,3)]⟩,#[(.branch (.branch (.branch .leaf .leaf) (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch .empty (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,.empty]⟩) (by decide) (by decide +kernel)
theorem cover_p16 : Cover (WeightedBound 100) p16 := .leaf _ safe_p16

def p17 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,3⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p17 : ∀ m, compatible p17 m → WeightedBound 100 m :=
  sound 100 p17 (.side 6 10 false (2)) (by decide) (by decide +kernel)
theorem cover_p17 : Cover (WeightedBound 100) p17 := .leaf _ safe_p17

def p18 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,true,3⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p18 : ∀ m, compatible p18 m → WeightedBound 100 m :=
  sound 100 p18 (.side 6 14 false (2)) (by decide) (by decide +kernel)
theorem cover_p18 : Cover (WeightedBound 100) p18 := .leaf _ safe_p18

def p19 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,false,3⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p19 : ∀ m, compatible p19 m → WeightedBound 100 m :=
  sound 100 p19 (.side 6 10 false (2)) (by decide) (by decide +kernel)
theorem cover_p19 : Cover (WeightedBound 100) p19 := .leaf _ safe_p19

def p20 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨true,true,3⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p20 : ∀ m, compatible p20 m → WeightedBound 100 m :=
  sound 100 p20 (.side 6 12 false (2)) (by decide) (by decide +kernel)
theorem cover_p20 : Cover (WeightedBound 100) p20 := .leaf _ safe_p20

def p21 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 2,true => some (some ⟨false,false,4⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨false,false,0⟩)
  | _,_ => none)
theorem safe_p21 : ∀ m, compatible p21 m → WeightedBound 100 m :=
  sound 100 p21 (.side 3 14 false (2)) (by decide) (by decide +kernel)
theorem cover_p21 : Cover (WeightedBound 100) p21 := .leaf _ safe_p21

end BB6.Agent47Raw11Q0BankSmall
