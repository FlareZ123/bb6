import TwoSidedAutomata
import Raw10EncodedSourceBridge
import Box17AuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! Nine additional original-source Box27 (D0,D1) complete cylinders.
    The finite-stack certificates use exact learned inverse push edges, as
    opposed to the full inverse relation used in Box27D0D1FAR.
    D0=6 is handled more generally by Box27D0FastPumps.never06. -/
namespace BB6.Agent49.Box27D0D1FARExt
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)

def table (d0 d1 : Fin 25) : PartialMachine := fun s => match s with
  | (0,false) => some (decode 8)
  | (1,false) => some (decode 11)
  | (2,false) | (2,true) => some (decode 13)
  | (3,false) => some (decode d0)
  | (3,true) => some (decode d1)
  | _ => none

def cert12_1 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .empty .leaf),.leaf,.leaf,.empty,.empty,.empty,.empty]⟩

theorem checked12_1 :
    BB6.Agent4Automata.check (table 12 1) cert12_1 = true := by decide

def cert12_5 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch .empty .leaf),.leaf,.leaf,.empty,.empty,.empty,.empty]⟩

theorem checked12_5 :
    BB6.Agent4Automata.check (table 12 5) cert12_5 = true := by decide

def cert12_7 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch .empty .leaf),.leaf,.leaf,.empty,.empty,.empty,.empty]⟩

theorem checked12_7 :
    BB6.Agent4Automata.check (table 12 7) cert12_7 = true := by decide

def cert14_2 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)]], #[(0,1),(2,0),(0,0)]⟩,#[.leaf,.empty,(.branch .empty (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),(.branch (.branch .empty .leaf) .leaf),.leaf,.empty,.empty,.empty,.empty]⟩

theorem checked14_2 :
    BB6.Agent4Automata.check (table 14 2) cert14_2 = true := by decide

def cert14_5 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.empty,.empty,.empty,.empty]⟩

theorem checked14_5 :
    BB6.Agent4Automata.check (table 14 5) cert14_5 = true := by decide

def cert14_6 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)]], #[(0,1),(2,0),(0,0)]⟩,#[.leaf,.empty,(.branch .leaf (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .empty .leaf) .leaf),.leaf,.empty,.empty,.empty,.empty]⟩

theorem checked14_6 :
    BB6.Agent4Automata.check (table 14 6) cert14_6 = true := by decide

def cert14_7 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),(.branch .leaf .leaf),(.branch .leaf .leaf),.empty,.empty,.empty,.empty]⟩

theorem checked14_7 :
    BB6.Agent4Automata.check (table 14 7) cert14_7 = true := by decide

def cert14_8 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)]], #[(0,1),(2,0),(0,0)]⟩,#[.leaf,.empty,(.branch .empty (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),(.branch (.branch .empty .leaf) .leaf),.leaf,.empty,.empty,.empty,.empty]⟩

theorem checked14_8 :
    BB6.Agent4Automata.check (table 14 8) cert14_8 = true := by decide

def cert16_2 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0),(true,3)],[(true,1),(true,2)],[(false,2)]], #[(0,1),(0,2),(3,2),(0,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)]], #[(0,1),(2,0),(0,0)]⟩,#[(.branch .leaf (.branch (.branch (.branch .empty .leaf) .empty) .empty)),.empty,(.branch .empty (.branch .empty .leaf)),.empty,.empty,(.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf),(.branch (.branch (.branch (.branch .empty .leaf) .leaf) .leaf) (.branch .empty (.branch .empty .leaf))),(.branch (.branch .empty (.branch .empty .leaf)) .empty),.empty,.empty,.empty,.empty]⟩

theorem checked16_2 :
    BB6.Agent4Automata.check (table 16 2) cert16_2 = true := by decide


def pairs : List (Fin 25 × Fin 25) :=
  [(12,1),(12,5),(12,7),(14,2),(14,5),(14,6),(14,7),(14,8),(16,2)]

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
  have hcases : (d0=12 ∧ d1=1) ∨ (d0=12 ∧ d1=5) ∨ (d0=12 ∧ d1=7) ∨ (d0=14 ∧ d1=2) ∨ (d0=14 ∧ d1=5) ∨ (d0=14 ∧ d1=6) ∨ (d0=14 ∧ d1=7) ∨ (d0=14 ∧ d1=8) ∨ (d0=16 ∧ d1=2) := by
    simpa [pairs] using hp
  rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact BB6.Agent4Automata.never (table 12 1) cert12_1
      checked12_1 m (source_compatible 12 1 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 12 5) cert12_5
      checked12_5 m (source_compatible 12 5 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 12 7) cert12_7
      checked12_7 m (source_compatible 12 7 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 2) cert14_2
      checked14_2 m (source_compatible 14 2 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 5) cert14_5
      checked14_5 m (source_compatible 14 5 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 6) cert14_6
      checked14_6 m (source_compatible 14 6 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 7) cert14_7
      checked14_7 m (source_compatible 14 7 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 14 8) cert14_8
      checked14_8 m (source_compatible 14 8 m hm hd0 hd1)
  · exact BB6.Agent4Automata.never (table 16 2) cert16_2
      checked16_2 m (source_compatible 16 2 m hm hd0 hd1)

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
end BB6.Agent49.Box27D0D1FARExt
