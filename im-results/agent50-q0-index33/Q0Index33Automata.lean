import TwoSidedAutomata
set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent50Q0Index33Automata
open BB6Coverage

/--
Exact R33L0 two-sided finite-stack certificate, isolated from the larger
q0-open-automata roster.  The table is the q0 sibling-scan index-33 residual:
only C1 is unassigned.  The checker validates every transition in both
stack automata; no bounded simulation is a proof premise.
-/
namespace R33L0
def table : PartialMachine := fun s => match s with
  | (0,false) => some (some ⟨true,true,1⟩)
  | (0,true) => some (some ⟨true,true,3⟩)
  | (1,false) => some (some ⟨true,true,2⟩)
  | (1,true) => some (some ⟨false,true,4⟩)
  | (2,false) => some (some ⟨false,false,0⟩)
  | (2,true) => none
  | (3,false) => some (some ⟨true,false,0⟩)
  | (3,true) => some (some ⟨true,false,3⟩)
  | (4,false) => some (some ⟨false,false,5⟩)
  | (4,true) => some (some ⟨false,true,1⟩)
  | (5,false) => some (some ⟨true,false,5⟩)
  | (5,true) => some (some ⟨false,false,2⟩)
  | _ => none
def cert : BB6.Agent4Automata.Cert := ⟨⟨#[[(false,0)],[(true,0),(false,8)],[(false,1)],[(true,1)],[(false,2)],[(true,2)],[(false,3)],[(true,3)],[(false,4)],[(true,4)],[(false,5),(true,5),(false,6),(true,6),(false,10),(true,10),(false,11),(true,11),(false,12),(true,12),(false,13),(true,13),(false,15),(true,15),(false,17),(true,17),(false,19),(true,19),(false,21),(true,21)],[(false,7)],[(true,7)],[(true,8)],[(false,9),(false,20)],[(true,9),(true,20)],[(false,14)],[(true,14)],[(false,16)],[(true,16)],[(false,18)],[(true,18)]],#[(0,1),(2,3),(4,5),(6,7),(8,9),(10,10),(10,10),(11,12),(1,13),(14,15),(10,10),(10,10),(10,10),(10,10),(16,17),(10,10),(18,19),(10,10),(20,21),(10,10),(14,15),(10,10)]⟩, ⟨#[[(false,0)],[(true,0)],[(true,1),(true,7)],[(true,2)],[(true,3)],[(false,3)],[(false,5)],[(true,4)]],#[(0,1),(0,2),(0,3),(5,4),(0,7),(6,0),(0,0),(0,2)]⟩, #[(.branch (.branch (.branch .leaf .leaf) (.branch .empty (.branch .empty .leaf))) (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) .empty) (.branch (.branch (.branch .empty .leaf) (.branch .empty (.branch .empty .leaf))) .empty)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .empty)))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) .empty) (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty))),.empty,(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch .empty (.branch (.branch .leaf (.branch .empty (.branch .empty .leaf))) .empty))),(.branch (.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch .empty (.branch .empty .leaf))) .leaf) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) (.branch .empty .leaf)))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)))),(.branch (.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)) (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty)) (.branch (.branch (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty) .empty) (.branch (.branch (.branch .empty (.branch (.branch (.branch .empty .leaf) .empty) .empty)) .empty) (.branch (.branch .empty (.branch .empty (.branch .empty .leaf))) .empty)))),(.branch .empty (.branch .empty (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty))) ]⟩
theorem checked : BB6.Agent4Automata.check table cert = true := by decide
theorem never (m : Machine) (hm : compatible table m) : NeverHalts m :=
  BB6.Agent4Automata.never table cert checked m hm
#print axioms never
end R33L0

end BB6.Agent50Q0Index33Automata
