import PhaseTree
import Q0RosterConsume

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent47Raw11Q0BankLarge
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent5PhaseTree
def p35 : PartialMachine := (fun s => match s.1.val,s.2 with
  | 0,false => some (some ⟨true,true,1⟩)
  | 0,true => some (some ⟨true,true,3⟩)
  | 1,false => some (some ⟨true,true,2⟩)
  | 1,true => some (some ⟨false,true,4⟩)
  | 2,false => some (some ⟨false,false,0⟩)
  | 3,false => some (some ⟨true,false,0⟩)
  | 3,true => some (some ⟨true,false,3⟩)
  | 4,true => some (some ⟨true,true,1⟩)
  | _,_ => none)
theorem safe_p35 : ∀ m, compatible p35 m → WeightedBound 100 m :=
  sound 100 p35 (.automata ⟨⟨#[[(false,0)],[],[(true,0),(true,3)],[(false,2)],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,⟨#[[(false,0)],[(false,0)],[(true,0),(true,4)],[],[(true,2)],[]],#[(1,2),(1,2),(3,4),(5,2),(3,2),(3,2)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),(.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) .empty)),(.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty),(.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) .empty),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch .leaf (.branch .empty .leaf))) .empty),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))) (.branch .empty (.branch (.branch .empty .leaf) .leaf))) .empty),.empty,(.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))) .empty),.empty,.empty]⟩) (by decide) (by decide +kernel)
theorem cover_p35 : Cover (WeightedBound 100) p35 := .leaf _ safe_p35

end BB6.Agent47Raw11Q0BankLarge
