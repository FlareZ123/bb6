import F412Partition
import NGramCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412NGram
open BB6Coverage BB6.Agent1NGram BB6.Agent26F412Graft

/-! Four previously unclassified ordinary F412 siblings have finite
    inductive local-window invariants. These certificates are entirely
    independent of F412's unresolved primitive clock and of E1 (which
    remains an unconstrained slot in each cylinder). The theorem checker,
    not the search/generator, proves each NeverHalts conclusion. -/

/-- Branch depth 6, 0RB; window width 4, 71 abstract states. -/
def p0 : PartialMachine := fChild ⟨6, by decide⟩ ⟨false,true,1⟩
def c0 : Cert := ⟨3, 0x100f15, 0x503c55, #[(.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty) .empty) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)) .empty),(.branch (.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)),.empty,(.branch .empty (.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty))),(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty))),(.branch (.branch .empty (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty))) .empty),(.branch (.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)) .empty),(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .leaf (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty))),.empty,.empty,(.branch (.branch (.branch (.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .empty) .empty) .empty) (.branch (.branch (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty) (.branch (.branch .empty (.branch (.branch .leaf .leaf) .empty)) .empty)) .empty)) ]⟩
theorem ok0 : check p0 c0 = true := by decide
theorem never0 (m : Machine) (hm : compatible p0 m) : NeverHalts m :=
  never p0 c0 ok0 m hm
#print axioms never0

/-- Branch depth 8, 0LA; window width 1, 30 abstract states. -/
def p1 : PartialMachine := fChild ⟨8, by decide⟩ ⟨false,false,0⟩
def c1 : Cert := ⟨0, 0xf, 0xf, #[(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)) ]⟩
theorem ok1 : check p1 c1 = true := by decide
theorem never1 (m : Machine) (hm : compatible p1 m) : NeverHalts m :=
  never p1 c1 ok1 m hm
#print axioms never1

/-- Branch depth 8, 0LC; window width 1, 30 abstract states. -/
def p2 : PartialMachine := fChild ⟨8, by decide⟩ ⟨false,false,2⟩
def c2 : Cert := ⟨0, 0xf, 0xf, #[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)) ]⟩
theorem ok2 : check p2 c2 = true := by decide
theorem never2 (m : Machine) (hm : compatible p2 m) : NeverHalts m :=
  never p2 c2 ok2 m hm
#print axioms never2

/-- Branch depth 8, 0RB; window width 1, 30 abstract states. -/
def p3 : PartialMachine := fChild ⟨8, by decide⟩ ⟨false,true,1⟩
def c3 : Cert := ⟨0, 0xf, 0xf, #[(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)) ]⟩
theorem ok3 : check p3 c3 = true := by decide
theorem never3 (m : Machine) (hm : compatible p3 m) : NeverHalts m :=
  never p3 c3 ok3 m hm
#print axioms never3

end BB6.Agent26F412NGram
