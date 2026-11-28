import TwoSidedAutomata
import Raw10EncodedSourceBridge
import Box17AuditCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! 36 extra source-relative Raw10 Box27 D0/F0 pair cylinders,
    each leaving the other six slots free. Distinct from existing D0-fast
    and D0D1/D0E0/triple cuts by D0 code.
    All finite-stack relations are explicitly Lean-checked. -/
namespace BB6.Agent49.Box27D0F0FAR
open BB6Coverage BB6Coverage.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)

def table (d0 v : Fin 25) : PartialMachine := fun s => match s with
  | (0,false) => some (decode 8)
  | (1,false) => some (decode 11)
  | (2,false) | (2,true) => some (decode 13)
  | (3,false) => some (decode d0)
  | (5,false) => some (decode v)
  | _ => none

def cert21_1 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_1 :
    BB6.Agent4Automata.check (table 21 1) cert21_1 = true := by decide

def cert21_2 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,2)],[(true,0),(true,2)],[(false,1),(false,3)],[(true,1),(true,3)]], #[(0,1),(2,3),(0,1),(2,3)]⟩,#[(.branch (.branch .leaf .leaf) .empty),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),.empty,.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) .empty),.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_2 :
    BB6.Agent4Automata.check (table 21 2) cert21_2 = true := by decide

def cert21_5 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_5 :
    BB6.Agent4Automata.check (table 21 5) cert21_5 = true := by decide

def cert21_6 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_6 :
    BB6.Agent4Automata.check (table 21 6) cert21_6 = true := by decide

def cert21_7 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_7 :
    BB6.Agent4Automata.check (table 21 7) cert21_7 = true := by decide

def cert21_8 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_8 :
    BB6.Agent4Automata.check (table 21 8) cert21_8 = true := by decide

def cert21_9 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.leaf,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_9 :
    BB6.Agent4Automata.check (table 21 9) cert21_9 = true := by decide

def cert21_10 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .leaf .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_10 :
    BB6.Agent4Automata.check (table 21 10) cert21_10 = true := by decide

def cert21_11 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_11 :
    BB6.Agent4Automata.check (table 21 11) cert21_11 = true := by decide

def cert21_13 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_13 :
    BB6.Agent4Automata.check (table 21 13) cert21_13 = true := by decide

def cert21_14 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),(.branch .leaf .leaf),.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_14 :
    BB6.Agent4Automata.check (table 21 14) cert21_14 = true := by decide

def cert21_15 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),(.branch .leaf .leaf),.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_15 :
    BB6.Agent4Automata.check (table 21 15) cert21_15 = true := by decide

def cert21_21 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.leaf,.empty]⟩
theorem checked21_21 :
    BB6.Agent4Automata.check (table 21 21) cert21_21 = true := by decide

def cert21_23 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .leaf .leaf),.empty]⟩
theorem checked21_23 :
    BB6.Agent4Automata.check (table 21 23) cert21_23 = true := by decide

def cert22_1 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .leaf .leaf),.empty]⟩
theorem checked22_1 :
    BB6.Agent4Automata.check (table 22 1) cert22_1 = true := by decide

def cert22_5 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .leaf .leaf),.empty]⟩
theorem checked22_5 :
    BB6.Agent4Automata.check (table 22 5) cert22_5 = true := by decide

def cert22_7 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .leaf .leaf),.empty]⟩
theorem checked22_7 :
    BB6.Agent4Automata.check (table 22 7) cert22_7 = true := by decide

def cert22_9 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.leaf,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .leaf .leaf),.empty]⟩
theorem checked22_9 :
    BB6.Agent4Automata.check (table 22 9) cert22_9 = true := by decide

def cert22_10 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .leaf .leaf),(.branch .leaf .leaf),.leaf,.empty,.empty,.empty,(.branch .leaf .leaf),.empty]⟩
theorem checked22_10 :
    BB6.Agent4Automata.check (table 22 10) cert22_10 = true := by decide

def cert22_11 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .leaf .leaf),.empty]⟩
theorem checked22_11 :
    BB6.Agent4Automata.check (table 22 11) cert22_11 = true := by decide

def cert22_13 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .leaf .leaf),.empty]⟩
theorem checked22_13 :
    BB6.Agent4Automata.check (table 22 13) cert22_13 = true := by decide

def cert22_21 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .leaf .leaf),.empty]⟩
theorem checked22_21 :
    BB6.Agent4Automata.check (table 22 21) cert22_21 = true := by decide

def cert22_23 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .leaf .leaf),.empty]⟩
theorem checked22_23 :
    BB6.Agent4Automata.check (table 22 23) cert22_23 = true := by decide

def cert23_1 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .empty .leaf),.empty]⟩
theorem checked23_1 :
    BB6.Agent4Automata.check (table 23 1) cert23_1 = true := by decide

def cert23_5 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .empty .leaf),.empty]⟩
theorem checked23_5 :
    BB6.Agent4Automata.check (table 23 5) cert23_5 = true := by decide

def cert23_7 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .empty .leaf),.empty]⟩
theorem checked23_7 :
    BB6.Agent4Automata.check (table 23 7) cert23_7 = true := by decide

def cert23_9 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.leaf,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .empty .leaf),.empty]⟩
theorem checked23_9 :
    BB6.Agent4Automata.check (table 23 9) cert23_9 = true := by decide

def cert23_10 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .leaf .leaf),.leaf,.empty,.empty,.empty,(.branch .empty .leaf),.empty]⟩
theorem checked23_10 :
    BB6.Agent4Automata.check (table 23 10) cert23_10 = true := by decide

def cert23_11 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .empty .leaf),.empty]⟩
theorem checked23_11 :
    BB6.Agent4Automata.check (table 23 11) cert23_11 = true := by decide

def cert23_13 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .empty .leaf),.empty]⟩
theorem checked23_13 :
    BB6.Agent4Automata.check (table 23 13) cert23_13 = true := by decide

def cert23_15 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),(.branch .leaf .leaf),.empty,.empty,.empty,(.branch .empty .leaf),.empty]⟩
theorem checked23_15 :
    BB6.Agent4Automata.check (table 23 15) cert23_15 = true := by decide

def cert23_21 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .leaf .leaf),.empty]⟩
theorem checked23_21 :
    BB6.Agent4Automata.check (table 23 21) cert23_21 = true := by decide

def cert23_23 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch .empty .leaf),.empty]⟩
theorem checked23_23 :
    BB6.Agent4Automata.check (table 23 23) cert23_23 = true := by decide

def cert24_9 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .leaf .leaf),.leaf,.empty,.empty,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty]⟩
theorem checked24_9 :
    BB6.Agent4Automata.check (table 24 9) cert24_9 = true := by decide

def cert24_10 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]], #[(0,1),(2,3),(0,0),(2,3)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)]], #[(0,1),(2,0),(0,0)]⟩,#[.leaf,.empty,(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch .empty (.branch .empty .leaf)) .empty),(.branch (.branch .empty (.branch .empty .leaf)) .leaf),(.branch (.branch .empty .leaf) (.branch (.branch (.branch .empty .leaf) .empty) .leaf)),.empty,.empty,.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)),.empty]⟩
theorem checked24_10 :
    BB6.Agent4Automata.check (table 24 10) cert24_10 = true := by decide

def cert24_11 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty]⟩
theorem checked24_11 :
    BB6.Agent4Automata.check (table 24 11) cert24_11 = true := by decide


def pairs : List (Fin 25 × Fin 25) := [(21,1),(21,2),(21,5),(21,6),(21,7),(21,8),(21,9),(21,10),(21,11),(21,13),(21,14),(21,15),(21,21),(21,23),(22,1),(22,5),(22,7),(22,9),(22,10),(22,11),(22,13),(22,21),(22,23),(23,1),(23,5),(23,7),(23,9),(23,10),(23,11),(23,13),(23,15),(23,21),(23,23),(24,9),(24,10),(24,11)]

theorem source_compatible (d0 v : Fin 25) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (hd0 : m (3,false) = decode d0)
    (hv : m (5,false) = decode v) : compatible (table d0 v) m := by
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

theorem source_never (m : Machine) (hm : Fits raw10Remainder[27]! m)
    (d0 v : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hv : m (5,false) = decode v)
    (hp : (d0,v) ∈ pairs) : NeverHalts m := by
  have hcases : (d0=21 ∧ v=1) ∨ (d0=21 ∧ v=2) ∨ (d0=21 ∧ v=5) ∨ (d0=21 ∧ v=6) ∨ (d0=21 ∧ v=7) ∨ (d0=21 ∧ v=8) ∨ (d0=21 ∧ v=9) ∨ (d0=21 ∧ v=10) ∨ (d0=21 ∧ v=11) ∨ (d0=21 ∧ v=13) ∨ (d0=21 ∧ v=14) ∨ (d0=21 ∧ v=15) ∨ (d0=21 ∧ v=21) ∨ (d0=21 ∧ v=23) ∨ (d0=22 ∧ v=1) ∨ (d0=22 ∧ v=5) ∨ (d0=22 ∧ v=7) ∨ (d0=22 ∧ v=9) ∨ (d0=22 ∧ v=10) ∨ (d0=22 ∧ v=11) ∨ (d0=22 ∧ v=13) ∨ (d0=22 ∧ v=21) ∨ (d0=22 ∧ v=23) ∨ (d0=23 ∧ v=1) ∨ (d0=23 ∧ v=5) ∨ (d0=23 ∧ v=7) ∨ (d0=23 ∧ v=9) ∨ (d0=23 ∧ v=10) ∨ (d0=23 ∧ v=11) ∨ (d0=23 ∧ v=13) ∨ (d0=23 ∧ v=15) ∨ (d0=23 ∧ v=21) ∨ (d0=23 ∧ v=23) ∨ (d0=24 ∧ v=9) ∨ (d0=24 ∧ v=10) ∨ (d0=24 ∧ v=11) := by
    simpa [pairs] using hp
  rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact BB6.Agent4Automata.never (table 21 1) cert21_1
      checked21_1 m (source_compatible 21 1 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 2) cert21_2
      checked21_2 m (source_compatible 21 2 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 5) cert21_5
      checked21_5 m (source_compatible 21 5 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 6) cert21_6
      checked21_6 m (source_compatible 21 6 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 7) cert21_7
      checked21_7 m (source_compatible 21 7 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 8) cert21_8
      checked21_8 m (source_compatible 21 8 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 9) cert21_9
      checked21_9 m (source_compatible 21 9 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 10) cert21_10
      checked21_10 m (source_compatible 21 10 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 11) cert21_11
      checked21_11 m (source_compatible 21 11 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 13) cert21_13
      checked21_13 m (source_compatible 21 13 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 14) cert21_14
      checked21_14 m (source_compatible 21 14 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 15) cert21_15
      checked21_15 m (source_compatible 21 15 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 21) cert21_21
      checked21_21 m (source_compatible 21 21 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 21 23) cert21_23
      checked21_23 m (source_compatible 21 23 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 22 1) cert22_1
      checked22_1 m (source_compatible 22 1 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 22 5) cert22_5
      checked22_5 m (source_compatible 22 5 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 22 7) cert22_7
      checked22_7 m (source_compatible 22 7 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 22 9) cert22_9
      checked22_9 m (source_compatible 22 9 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 22 10) cert22_10
      checked22_10 m (source_compatible 22 10 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 22 11) cert22_11
      checked22_11 m (source_compatible 22 11 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 22 13) cert22_13
      checked22_13 m (source_compatible 22 13 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 22 21) cert22_21
      checked22_21 m (source_compatible 22 21 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 22 23) cert22_23
      checked22_23 m (source_compatible 22 23 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 23 1) cert23_1
      checked23_1 m (source_compatible 23 1 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 23 5) cert23_5
      checked23_5 m (source_compatible 23 5 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 23 7) cert23_7
      checked23_7 m (source_compatible 23 7 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 23 9) cert23_9
      checked23_9 m (source_compatible 23 9 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 23 10) cert23_10
      checked23_10 m (source_compatible 23 10 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 23 11) cert23_11
      checked23_11 m (source_compatible 23 11 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 23 13) cert23_13
      checked23_13 m (source_compatible 23 13 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 23 15) cert23_15
      checked23_15 m (source_compatible 23 15 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 23 21) cert23_21
      checked23_21 m (source_compatible 23 21 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 23 23) cert23_23
      checked23_23 m (source_compatible 23 23 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 24 9) cert24_9
      checked24_9 m (source_compatible 24 9 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 24 10) cert24_10
      checked24_10 m (source_compatible 24 10 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 24 11) cert24_11
      checked24_11 m (source_compatible 24 11 m hm hd0 hv)

theorem source_bound (B : Nat) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 v : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hv : m (5,false) = decode v)
    (hp : (d0,v) ∈ pairs) : WeightedBound B m :=
  weighted_of_never B m (source_never m hm d0 v hd0 hv hp)

#print axioms source_compatible
#print axioms source_never
#print axioms source_bound
end BB6.Agent49.Box27D0F0FAR
