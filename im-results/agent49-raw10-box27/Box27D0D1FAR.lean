import TwoSidedAutomata
import Raw10EncodedSourceBridge
import Box17AuditCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-!
Thirty-four disjoint (D0,D1) two-symbol cylinders within raw10 Box27
are nonhalting for every completion of the other six free transition
slots. Two-state (33 pairs) or four-state (one pair) stack automata check
the invariant. This is independent of the D0=0/5/7/9/10 macro closures.
-/
namespace BB6.Agent49.Box27D0D1FAR
open BB6Coverage BB6Coverage.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)

def table (d0 d1 : Fin 25) : PartialMachine := fun s => match s with
  | (0,false) => some (decode 8)
  | (1,false) => some (decode 11)
  | (2,false) | (2,true) => some (decode 13)
  | (3,false) => some (decode d0)
  | (3,true) => some (decode d1)
  | _ => none

def c06_06 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_06_06 :
    BB6.Agent4Automata.check (table 6 6) c06_06 = true := by decide

def c06_08 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_06_08 :
    BB6.Agent4Automata.check (table 6 8) c06_08 = true := by decide

def c06_09 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_06_09 :
    BB6.Agent4Automata.check (table 6 9) c06_09 = true := by decide

def c06_10 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,(.branch .leaf (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_06_10 :
    BB6.Agent4Automata.check (table 6 10) c06_10 = true := by decide

def c06_11 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_06_11 :
    BB6.Agent4Automata.check (table 6 11) c06_11 = true := by decide

def c06_12 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_06_12 :
    BB6.Agent4Automata.check (table 6 12) c06_12 = true := by decide

def c06_13 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_06_13 :
    BB6.Agent4Automata.check (table 6 13) c06_13 = true := by decide

def c12_06 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_12_06 :
    BB6.Agent4Automata.check (table 12 6) c12_06 = true := by decide

def c12_08 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_12_08 :
    BB6.Agent4Automata.check (table 12 8) c12_08 = true := by decide

def c12_09 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_12_09 :
    BB6.Agent4Automata.check (table 12 9) c12_09 = true := by decide

def c12_10 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_12_10 :
    BB6.Agent4Automata.check (table 12 10) c12_10 = true := by decide

def c12_11 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_12_11 :
    BB6.Agent4Automata.check (table 12 11) c12_11 = true := by decide

def c12_12 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_12_12 :
    BB6.Agent4Automata.check (table 12 12) c12_12 = true := by decide

def c12_13 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_12_13 :
    BB6.Agent4Automata.check (table 12 13) c12_13 = true := by decide

def c12_14 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_12_14 :
    BB6.Agent4Automata.check (table 12 14) c12_14 = true := by decide

def c12_15 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,.empty,.empty,.empty]⟩
theorem checked_12_15 :
    BB6.Agent4Automata.check (table 12 15) c12_15 = true := by decide

def c12_16 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty]⟩
theorem checked_12_16 :
    BB6.Agent4Automata.check (table 12 16) c12_16 = true := by decide

def c14_01 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(false,2),(false,3)],[(true,0),(true,1)],[(true,2),(true,3)]], #[(0,2),(0,2),(1,3),(1,3)]⟩, ⟨#[[(false,0),(false,1)],[(false,2),(false,3)],[(true,0),(true,1)],[(true,2),(true,3)]], #[(0,2),(0,2),(1,3),(1,3)]⟩, #[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch .leaf .leaf) .empty)),.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch .empty .leaf) .empty))),.empty,.empty,(.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch .leaf .leaf))),(.branch (.branch .empty (.branch .leaf .leaf)) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch .leaf .leaf))),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,.empty,.empty,.empty]⟩
theorem checked_14_01 :
    BB6.Agent4Automata.check (table 14 1) c14_01 = true := by decide

def c14_09 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),.empty,.empty,.empty,.empty]⟩
theorem checked_14_09 :
    BB6.Agent4Automata.check (table 14 9) c14_09 = true := by decide

def c14_10 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .leaf .leaf),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),.empty,.empty,.empty,.empty]⟩
theorem checked_14_10 :
    BB6.Agent4Automata.check (table 14 10) c14_10 = true := by decide

def c14_11 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),.empty,.empty,.empty,.empty]⟩
theorem checked_14_11 :
    BB6.Agent4Automata.check (table 14 11) c14_11 = true := by decide

def c14_12 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),.empty,.empty,.empty,.empty]⟩
theorem checked_14_12 :
    BB6.Agent4Automata.check (table 14 12) c14_12 = true := by decide

def c14_13 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),.empty,.empty,.empty,.empty]⟩
theorem checked_14_13 :
    BB6.Agent4Automata.check (table 14 13) c14_13 = true := by decide

def c14_14 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) .leaf),(.branch (.branch .leaf .leaf) .leaf),.empty,.empty,.empty,.empty]⟩
theorem checked_14_14 :
    BB6.Agent4Automata.check (table 14 14) c14_14 = true := by decide

def c14_15 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,.empty,.empty,.empty]⟩
theorem checked_14_15 :
    BB6.Agent4Automata.check (table 14 15) c14_15 = true := by decide

def c14_16 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,.empty,.empty,.empty]⟩
theorem checked_14_16 :
    BB6.Agent4Automata.check (table 14 16) c14_16 = true := by decide

def c16_09 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .leaf .leaf) .empty),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,.empty,.empty,.empty]⟩
theorem checked_16_09 :
    BB6.Agent4Automata.check (table 16 9) c16_09 = true := by decide

def c16_10 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .leaf .leaf),(.branch .leaf (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,.empty,.empty,.empty]⟩
theorem checked_16_10 :
    BB6.Agent4Automata.check (table 16 10) c16_10 = true := by decide

def c16_11 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf .leaf)),(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,.empty,.empty,.empty]⟩
theorem checked_16_11 :
    BB6.Agent4Automata.check (table 16 11) c16_11 = true := by decide

def c16_12 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,.empty,.empty,.empty]⟩
theorem checked_16_12 :
    BB6.Agent4Automata.check (table 16 12) c16_12 = true := by decide

def c16_13 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,.empty,.empty,.empty]⟩
theorem checked_16_13 :
    BB6.Agent4Automata.check (table 16 13) c16_13 = true := by decide

def c16_14 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,.empty,.empty,.empty]⟩
theorem checked_16_14 :
    BB6.Agent4Automata.check (table 16 14) c16_14 = true := by decide

def c16_15 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,.empty,.empty,.empty]⟩
theorem checked_16_15 :
    BB6.Agent4Automata.check (table 16 15) c16_15 = true := by decide

def c16_16 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, ⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩, #[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,.empty,.empty,.empty]⟩
theorem checked_16_16 :
    BB6.Agent4Automata.check (table 16 16) c16_16 = true := by decide

def pairs : List (Fin 25 × Fin 25) :=
  [(6,6),(6,8),(6,9),(6,10),(6,11),(6,12),(6,13),(12,6),(12,8),(12,9),(12,10),(12,11),(12,12),(12,13),(12,14),(12,15),(12,16),(14,1),(14,9),(14,10),(14,11),(14,12),(14,13),(14,14),(14,15),(14,16),(16,9),(16,10),(16,11),(16,12),(16,13),(16,14),(16,15),(16,16)]

theorem source_compatible (d0 d1 : Fin 25) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (hd0 : m (3,false) = decode d0)
    (hd1 : m (3,true) = decode d1) : compatible (table d0 d1) m := by
  have e0 : raw10Remainder[27]! (0,false) = [decode 8] := by decide
  have e1 : raw10Remainder[27]! (1,false) = [decode 11] := by decide
  have e2 : raw10Remainder[27]! (2,false) = [decode 13] := by decide
  have e3 : raw10Remainder[27]! (2,true) = [decode 13] := by decide
  have h0 : m (0,false) = decode 8 := by simpa [e0] using hm (0,false)
  have h1 : m (1,false) = decode 11 := by simpa [e1] using hm (1,false)
  have h2 : m (2,false) = decode 13 := by simpa [e2] using hm (2,false)
  have h3 : m (2,true) = decode 13 := by simpa [e3] using hm (2,true)
  intro s t ht
  obtain ⟨q,b⟩ := s
  have hq : q=0 ∨ q=1 ∨ q=2 ∨ q=3 ∨ q=4 ∨ q=5 := by omega
  rcases hq with rfl|rfl|rfl|rfl|rfl|rfl <;>
    cases b <;> simp [table] at ht ⊢ <;> simp_all

theorem source_never (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 d1 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hd1 : m (3,true) = decode d1)
    (hp : (d0,d1) ∈ pairs) : NeverHalts m := by
  have hcases : (d0=6 ∧ d1=6) ∨ (d0=6 ∧ d1=8) ∨ (d0=6 ∧ d1=9) ∨ (d0=6 ∧ d1=10) ∨ (d0=6 ∧ d1=11) ∨ (d0=6 ∧ d1=12) ∨ (d0=6 ∧ d1=13) ∨ (d0=12 ∧ d1=6) ∨ (d0=12 ∧ d1=8) ∨ (d0=12 ∧ d1=9) ∨ (d0=12 ∧ d1=10) ∨ (d0=12 ∧ d1=11) ∨ (d0=12 ∧ d1=12) ∨ (d0=12 ∧ d1=13) ∨ (d0=12 ∧ d1=14) ∨ (d0=12 ∧ d1=15) ∨ (d0=12 ∧ d1=16) ∨ (d0=14 ∧ d1=1) ∨ (d0=14 ∧ d1=9) ∨ (d0=14 ∧ d1=10) ∨ (d0=14 ∧ d1=11) ∨ (d0=14 ∧ d1=12) ∨ (d0=14 ∧ d1=13) ∨ (d0=14 ∧ d1=14) ∨ (d0=14 ∧ d1=15) ∨ (d0=14 ∧ d1=16) ∨ (d0=16 ∧ d1=9) ∨ (d0=16 ∧ d1=10) ∨ (d0=16 ∧ d1=11) ∨ (d0=16 ∧ d1=12) ∨ (d0=16 ∧ d1=13) ∨ (d0=16 ∧ d1=14) ∨ (d0=16 ∧ d1=15) ∨ (d0=16 ∧ d1=16) := by
    simpa [pairs] using hp
  rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact BB6.Agent4Automata.never (table 6 6) c06_06
      checked_06_06 m (source_compatible 6 6 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 6 8) c06_08
      checked_06_08 m (source_compatible 6 8 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 6 9) c06_09
      checked_06_09 m (source_compatible 6 9 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 6 10) c06_10
      checked_06_10 m (source_compatible 6 10 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 6 11) c06_11
      checked_06_11 m (source_compatible 6 11 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 6 12) c06_12
      checked_06_12 m (source_compatible 6 12 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 6 13) c06_13
      checked_06_13 m (source_compatible 6 13 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 12 6) c12_06
      checked_12_06 m (source_compatible 12 6 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 12 8) c12_08
      checked_12_08 m (source_compatible 12 8 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 12 9) c12_09
      checked_12_09 m (source_compatible 12 9 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 12 10) c12_10
      checked_12_10 m (source_compatible 12 10 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 12 11) c12_11
      checked_12_11 m (source_compatible 12 11 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 12 12) c12_12
      checked_12_12 m (source_compatible 12 12 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 12 13) c12_13
      checked_12_13 m (source_compatible 12 13 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 12 14) c12_14
      checked_12_14 m (source_compatible 12 14 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 12 15) c12_15
      checked_12_15 m (source_compatible 12 15 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 12 16) c12_16
      checked_12_16 m (source_compatible 12 16 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 1) c14_01
      checked_14_01 m (source_compatible 14 1 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 9) c14_09
      checked_14_09 m (source_compatible 14 9 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 10) c14_10
      checked_14_10 m (source_compatible 14 10 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 11) c14_11
      checked_14_11 m (source_compatible 14 11 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 12) c14_12
      checked_14_12 m (source_compatible 14 12 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 13) c14_13
      checked_14_13 m (source_compatible 14 13 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 14) c14_14
      checked_14_14 m (source_compatible 14 14 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 15) c14_15
      checked_14_15 m (source_compatible 14 15 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 16) c14_16
      checked_14_16 m (source_compatible 14 16 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 16 9) c16_09
      checked_16_09 m (source_compatible 16 9 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 16 10) c16_10
      checked_16_10 m (source_compatible 16 10 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 16 11) c16_11
      checked_16_11 m (source_compatible 16 11 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 16 12) c16_12
      checked_16_12 m (source_compatible 16 12 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 16 13) c16_13
      checked_16_13 m (source_compatible 16 13 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 16 14) c16_14
      checked_16_14 m (source_compatible 16 14 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 16 15) c16_15
      checked_16_15 m (source_compatible 16 15 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 16 16) c16_16
      checked_16_16 m (source_compatible 16 16 m hm hd0 hd1)

theorem source_bound (B : Nat) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 d1 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hd1 : m (3,true) = decode d1)
    (hp : (d0,d1) ∈ pairs) : WeightedBound B m :=
  weighted_of_never B m (source_never m hm d0 d1 hd0 hd1 hp)

#print axioms source_compatible
#print axioms source_never
#print axioms source_bound
end BB6.Agent49.Box27D0D1FAR
