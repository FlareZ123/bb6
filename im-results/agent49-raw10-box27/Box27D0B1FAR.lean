import TwoSidedAutomata
import Raw10EncodedSourceBridge
import Box17AuditCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! 15 extra source-relative Raw10 Box27 D0/B1 pair cylinders,
    each leaving the other six slots free. Distinct from existing D0-fast
    and D0D1/D0E0/triple cuts by D0 code.
    All finite-stack relations are explicitly Lean-checked. -/
namespace BB6.Agent49.Box27D0B1FAR
open BB6Coverage BB6Coverage.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)

def table (d0 v : Fin 25) : PartialMachine := fun s => match s with
  | (0,false) => some (decode 8)
  | (1,false) => some (decode 11)
  | (2,false) | (2,true) => some (decode 13)
  | (3,false) => some (decode d0)
  | (1,true) => some (decode v)
  | _ => none

def cert2_2 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0),(true,2)],[(false,1)]], #[(0,1),(2,0),(0,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)]], #[(0,1),(2,0),(0,0)]⟩,#[(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .leaf (.branch .empty .leaf))),.empty,(.branch .empty (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty (.branch .leaf (.branch .empty .leaf))),(.branch (.branch .empty .leaf) (.branch (.branch .empty .leaf) .empty)),.empty,.empty,.empty,.empty,.empty]⟩
theorem checked2_2 :
    BB6.Agent4Automata.check (table 2 2) cert2_2 = true := by decide

def cert2_5 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.empty,.empty]⟩
theorem checked2_5 :
    BB6.Agent4Automata.check (table 2 5) cert2_5 = true := by decide

def cert2_7 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.empty,.empty]⟩
theorem checked2_7 :
    BB6.Agent4Automata.check (table 2 7) cert2_7 = true := by decide

def cert2_9 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .leaf .leaf),.leaf,.empty,.empty,.empty,.empty,.empty]⟩
theorem checked2_9 :
    BB6.Agent4Automata.check (table 2 9) cert2_9 = true := by decide

def cert2_10 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch .leaf .leaf),(.branch .leaf .leaf),(.branch (.branch .leaf .leaf) .empty),.empty,.empty,.empty,.empty,.empty]⟩
theorem checked2_10 :
    BB6.Agent4Automata.check (table 2 10) cert2_10 = true := by decide

def cert2_11 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.empty,.empty]⟩
theorem checked2_11 :
    BB6.Agent4Automata.check (table 2 11) cert2_11 = true := by decide

def cert2_14 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,2)],[(true,0)],[(false,1)]], #[(0,1),(2,0),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)]], #[(0,1),(2,0),(0,0)]⟩,#[(.branch .leaf .leaf),.empty,(.branch .empty (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) .empty),.empty,.empty,.empty,.empty,.empty]⟩
theorem checked2_14 :
    BB6.Agent4Automata.check (table 2 14) cert2_14 = true := by decide

def cert2_16 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0),(true,3)],[(true,1)],[(false,2)]], #[(0,1),(0,2),(3,0),(0,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)]], #[(0,1),(2,0),(0,0)]⟩,#[(.branch (.branch .leaf (.branch (.branch .empty .leaf) .empty)) (.branch (.branch (.branch .leaf .leaf) .empty) .empty)),.empty,(.branch .empty (.branch .empty .leaf)),(.branch .empty (.branch .empty .leaf)),.empty,(.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf),(.branch (.branch (.branch (.branch .empty .leaf) .empty) (.branch .leaf .leaf)) .empty),.empty,.empty,.empty,.empty,.empty]⟩
theorem checked2_16 :
    BB6.Agent4Automata.check (table 2 16) cert2_16 = true := by decide

def cert3_5 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[(.branch .leaf .leaf),.empty,(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.empty,.empty]⟩
theorem checked3_5 :
    BB6.Agent4Automata.check (table 3 5) cert3_5 = true := by decide

def cert3_7 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.empty,.empty]⟩
theorem checked3_7 :
    BB6.Agent4Automata.check (table 3 7) cert3_7 = true := by decide

def cert3_9 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .leaf .leaf),.leaf,.empty,.empty,.empty,.empty,.empty]⟩
theorem checked3_9 :
    BB6.Agent4Automata.check (table 3 9) cert3_9 = true := by decide

def cert3_11 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[(.branch .leaf .leaf),.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),.leaf,.empty,.empty,.empty,.empty,.empty]⟩
theorem checked3_11 :
    BB6.Agent4Automata.check (table 3 11) cert3_11 = true := by decide

def cert4_2 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0),(true,3)],[(true,1),(true,2)],[(false,2)]], #[(0,1),(0,2),(3,2),(0,1)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)]], #[(0,1),(2,0),(0,0)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf))),.empty,(.branch .empty (.branch .empty .leaf)),(.branch (.branch .empty (.branch .empty .leaf)) .empty),.empty,(.branch (.branch .empty (.branch (.branch .empty .leaf) .empty)) .leaf),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .leaf) .empty),.empty,.empty,.empty,.empty,.empty]⟩
theorem checked4_2 :
    BB6.Agent4Automata.check (table 4 2) cert4_2 = true := by decide

def cert4_5 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)],[(true,1)]], #[(0,1),(0,2),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1)]], #[(0,1),(2,0),(0,0)]⟩,#[(.branch (.branch (.branch .leaf .leaf) .empty) .empty),.empty,(.branch .leaf (.branch .empty .leaf)),(.branch (.branch .leaf (.branch .empty .leaf)) (.branch .empty .leaf)),(.branch .empty .leaf),(.branch .empty .leaf),(.branch (.branch .empty .leaf) .empty),.empty,.empty,.empty,.empty,.empty]⟩
theorem checked4_5 :
    BB6.Agent4Automata.check (table 4 5) cert4_5 = true := by decide

def cert4_7 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0)],[(true,0)],[(true,1)]], #[(0,1),(0,2),(0,0)]⟩,⟨#[[(false,0)],[(true,0)],[(false,1),(false,3)],[(true,1),(true,3)]], #[(0,1),(2,3),(0,0),(2,3)]⟩,#[(.branch .leaf (.branch (.branch .empty .leaf) (.branch .empty .leaf))),.empty,(.branch (.branch (.branch .empty .leaf) .empty) (.branch .empty .leaf)),(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .leaf) (.branch (.branch .leaf .leaf) .leaf))),(.branch .empty (.branch .empty .leaf)),(.branch .empty .leaf),(.branch (.branch .empty .leaf) .empty),.empty,.empty,.empty,.empty,.empty]⟩
theorem checked4_7 :
    BB6.Agent4Automata.check (table 4 7) cert4_7 = true := by decide


def pairs : List (Fin 25 × Fin 25) := [(2,2),(2,5),(2,7),(2,9),(2,10),(2,11),(2,14),(2,16),(3,5),(3,7),(3,9),(3,11),(4,2),(4,5),(4,7)]

theorem source_compatible (d0 v : Fin 25) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (hd0 : m (3,false) = decode d0)
    (hv : m (1,true) = decode v) : compatible (table d0 v) m := by
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
    (hv : m (1,true) = decode v)
    (hp : (d0,v) ∈ pairs) : NeverHalts m := by
  have hcases : (d0=2 ∧ v=2) ∨ (d0=2 ∧ v=5) ∨ (d0=2 ∧ v=7) ∨ (d0=2 ∧ v=9) ∨ (d0=2 ∧ v=10) ∨ (d0=2 ∧ v=11) ∨ (d0=2 ∧ v=14) ∨ (d0=2 ∧ v=16) ∨ (d0=3 ∧ v=5) ∨ (d0=3 ∧ v=7) ∨ (d0=3 ∧ v=9) ∨ (d0=3 ∧ v=11) ∨ (d0=4 ∧ v=2) ∨ (d0=4 ∧ v=5) ∨ (d0=4 ∧ v=7) := by
    simpa [pairs] using hp
  rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact BB6.Agent4Automata.never (table 2 2) cert2_2
      checked2_2 m (source_compatible 2 2 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 2 5) cert2_5
      checked2_5 m (source_compatible 2 5 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 2 7) cert2_7
      checked2_7 m (source_compatible 2 7 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 2 9) cert2_9
      checked2_9 m (source_compatible 2 9 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 2 10) cert2_10
      checked2_10 m (source_compatible 2 10 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 2 11) cert2_11
      checked2_11 m (source_compatible 2 11 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 2 14) cert2_14
      checked2_14 m (source_compatible 2 14 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 2 16) cert2_16
      checked2_16 m (source_compatible 2 16 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 3 5) cert3_5
      checked3_5 m (source_compatible 3 5 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 3 7) cert3_7
      checked3_7 m (source_compatible 3 7 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 3 9) cert3_9
      checked3_9 m (source_compatible 3 9 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 3 11) cert3_11
      checked3_11 m (source_compatible 3 11 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 4 2) cert4_2
      checked4_2 m (source_compatible 4 2 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 4 5) cert4_5
      checked4_5 m (source_compatible 4 5 m hm hd0 hv)
  · exact BB6.Agent4Automata.never (table 4 7) cert4_7
      checked4_7 m (source_compatible 4 7 m hm hd0 hv)

theorem source_bound (B : Nat) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 v : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (hv : m (1,true) = decode v)
    (hp : (d0,v) ∈ pairs) : WeightedBound B m :=
  weighted_of_never B m (source_never m hm d0 v hd0 hv hp)

#print axioms source_compatible
#print axioms source_never
#print axioms source_bound
end BB6.Agent49.Box27D0B1FAR
