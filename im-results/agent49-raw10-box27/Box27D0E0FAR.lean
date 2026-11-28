import TwoSidedAutomata
import Raw10EncodedSourceBridge
import Box17AuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0
/-! Four genuine Box27 D0/E0 cylinders, with D1 entirely unrestricted.
    They lie outside the previously selected 160 D0/D1 pairs. -/
namespace BB6.Agent49.Box27D0E0FAR
open BB6Coverage BB6Coverage.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)

def table (d0 e0 : Fin 25) : PartialMachine := fun s => match s with
  | (0,false) => some (decode 8)
  | (1,false) => some (decode 11)
  | (2,false) | (2,true) => some (decode 13)
  | (3,false) => some (decode d0)
  | (4,false) => some (decode e0)
  | _ => none

def cert17_14 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(false,2),(false,3)],[(false,4),(false,5)],[(false,6),(false,7)],[(true,0),(true,1)],[(true,2),(true,3)],[(true,4),(true,5)],[(true,6),(true,7)]], #[(0,4),(0,4),(1,5),(1,5),(2,6),(2,6),(3,7),(3,7)]⟩, ⟨#[[(false,0),(false,1)],[(false,2),(false,3)],[(false,4),(false,5)],[(false,6),(false,7)],[(true,0),(true,1)],[(true,2),(true,3)],[(true,4),(true,5)],[(true,6),(true,7)]], #[(0,4),(0,4),(1,5),(1,5),(2,6),(2,6),(3,7),(3,7)]⟩, #[.leaf,.empty,(.branch (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty) (.branch (.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) .empty) .empty)),.empty,.empty,(.branch (.branch (.branch .empty (.branch .leaf .leaf)) .empty) .empty),(.branch (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)) (.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty))),.empty,(.branch .empty (.branch (.branch (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) (.branch (.branch .leaf .leaf) (.branch .leaf .leaf))) .empty) .empty)),.empty,.empty,.empty]⟩
theorem checked17_14 :
    BB6.Agent4Automata.check (table 17 14) cert17_14 = true := by decide

def cert18_10 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(false,2),(false,3)],[(true,0),(true,1)],[(true,2),(true,3)]], #[(0,2),(0,2),(1,3),(1,3)]⟩, ⟨#[[(false,0),(false,1)],[(false,2),(false,3)],[(true,0),(true,1)],[(true,2),(true,3)]], #[(0,2),(0,2),(1,3),(1,3)]⟩, #[.leaf,.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)),.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),(.branch (.branch .leaf (.branch .leaf .leaf)) (.branch .leaf .leaf)),(.branch (.branch (.branch .leaf .leaf) .empty) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)),.empty,(.branch (.branch .leaf (.branch .leaf .leaf)) (.branch .leaf (.branch .leaf .leaf))),.empty,.empty,.empty]⟩
theorem checked18_10 :
    BB6.Agent4Automata.check (table 18 10) cert18_10 = true := by decide

def cert18_13 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(false,2),(false,3)],[(true,0),(true,1)],[(true,2),(true,3)]], #[(0,2),(0,2),(1,3),(1,3)]⟩, ⟨#[[(false,0),(false,1)],[(false,2),(false,3)],[(true,0),(true,1)],[(true,2),(true,3)]], #[(0,2),(0,2),(1,3),(1,3)]⟩, #[.leaf,.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)),.empty,.empty,(.branch (.branch .empty (.branch .leaf .leaf)) .empty),(.branch .empty (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)),.empty,(.branch (.branch .empty (.branch .leaf .leaf)) (.branch .empty (.branch .leaf .leaf))),.empty,.empty,.empty]⟩
theorem checked18_13 :
    BB6.Agent4Automata.check (table 18 13) cert18_13 = true := by decide

def cert20_10 : BB6.Agent4Automata.Cert :=
  ⟨⟨#[[(false,0),(false,1)],[(false,2),(false,3)],[(true,0),(true,1)],[(true,2),(true,3)]], #[(0,2),(0,2),(1,3),(1,3)]⟩, ⟨#[[(false,0),(false,1)],[(false,2),(false,3)],[(true,0),(true,1)],[(true,2),(true,3)]], #[(0,2),(0,2),(1,3),(1,3)]⟩, #[.leaf,.empty,(.branch (.branch (.branch (.branch .empty .leaf) .empty) .empty) (.branch (.branch (.branch .empty .leaf) .empty) .empty)),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch .empty .leaf) (.branch .leaf .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),(.branch (.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) .empty) (.branch (.branch (.branch .leaf .leaf) (.branch .leaf .leaf)) .empty)),.empty,(.branch (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))) (.branch (.branch .empty (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf)))),.empty,.empty,.empty]⟩
theorem checked20_10 :
    BB6.Agent4Automata.check (table 20 10) cert20_10 = true := by decide

def pairs : List (Fin 25 × Fin 25) := [(17,14),(18,10),(18,13),(20,10)]

theorem source_compatible (d0 e0 : Fin 25) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (hd0 : m (3,false) = decode d0)
    (he0 : m (4,false) = decode e0) : compatible (table d0 e0) m := by
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
    (d0 e0 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (he0 : m (4,false) = decode e0)
    (hp : (d0,e0) ∈ pairs) : NeverHalts m := by
  have hcases : (d0=17 ∧ e0=14) ∨ (d0=18 ∧ e0=10) ∨ (d0=18 ∧ e0=13) ∨ (d0=20 ∧ e0=10) := by
    simpa [pairs] using hp
  rcases hcases with ⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩|⟨rfl,rfl⟩
  · exact BB6.Agent4Automata.never (table 17 14) cert17_14
      checked17_14 m (source_compatible 17 14 m hm hd0 he0)
  · exact BB6.Agent4Automata.never (table 18 10) cert18_10
      checked18_10 m (source_compatible 18 10 m hm hd0 he0)
  · exact BB6.Agent4Automata.never (table 18 13) cert18_13
      checked18_13 m (source_compatible 18 13 m hm hd0 he0)
  · exact BB6.Agent4Automata.never (table 20 10) cert20_10
      checked20_10 m (source_compatible 20 10 m hm hd0 he0)

theorem source_bound (B : Nat) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 e0 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (he0 : m (4,false) = decode e0)
    (hp : (d0,e0) ∈ pairs) : WeightedBound B m :=
  weighted_of_never B m (source_never m hm d0 e0 hd0 he0 hp)

#print axioms source_compatible
#print axioms source_never
#print axioms source_bound
end BB6.Agent49.Box27D0E0FAR
