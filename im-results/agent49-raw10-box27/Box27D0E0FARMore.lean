import TwoSidedAutomata
import Raw10EncodedSourceBridge
import Box17AuditCore
set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-! Thirty-two additional fixed (D0,E0) Raw10 Box27 pair cylinders.
    They are distinct from the 4 previously certified in Box27D0E0FAR.
    D1,A1,B1,E1,F0,F1 remain freely variable, 25^6 completions per pair.
    All 32 finite-stack invariants are explicitly Lean-checked; the
    generator is untrusted. This is a local source-relative result. -/
namespace BB6.Agent49.Box27D0E0FARMore
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent49Box BB6.Agent49BoxBridge
open BB6.Agent13.Box17 (decode)

def table (d0 e0 : Fin 25) : PartialMachine := fun s => match s with
  | (0,false) => some (decode 8)
  | (1,false) => some (decode 11)
  | (2,false) | (2,true) => some (decode 13)
  | (3,false) => some (decode d0)
  | (4,false) => some (decode e0)
  | _ => none

structure Item where
  d0 : Fin 25
  e0 : Fin 25
  cert : BB6.Agent4Automata.Cert

def cases : List Item := [
  ⟨17,1,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.leaf,.empty,.empty,.empty]⟩⟩,
  ⟨17,2,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,2)],[(true,0),(true,2)],[(false,1),(false,3)],[(true,1),(true,3)]], #[(0,1),(2,3),(0,1),(2,3)]⟩,#[(.branch (.branch .leaf .leaf) .empty),.empty,(.branch (.branch (.branch .empty .leaf) (.branch .empty .leaf)) (.branch (.branch .empty .leaf) (.branch .empty .leaf))),.empty,.empty,(.branch .empty (.branch .leaf .leaf)),(.branch (.branch .empty .leaf) .empty),.empty,.leaf,.empty,.empty,.empty]⟩⟩,
  ⟨17,5,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.leaf,.empty,.empty,.empty]⟩⟩,
  ⟨17,6,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.leaf,.empty,.empty,.empty]⟩⟩,
  ⟨17,7,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.leaf,.empty,.empty,.empty]⟩⟩,
  ⟨17,8,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.leaf,.empty,.empty,.empty]⟩⟩,
  ⟨17,9,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.leaf,(.branch .empty .leaf),.leaf,.empty,.leaf,.empty,.empty,.empty]⟩⟩,
  ⟨17,10,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .leaf .leaf),(.branch .empty .leaf),.leaf,.empty,.leaf,.empty,.empty,.empty]⟩⟩,
  ⟨17,11,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,.leaf,.empty,.empty,.empty]⟩⟩,
  ⟨17,13,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.leaf,.empty,.empty,.empty]⟩⟩,
  ⟨17,15,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),(.branch .leaf .leaf),.empty,.leaf,.empty,.empty,.empty]⟩⟩,
  ⟨17,17,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,.leaf,.empty,.empty,.empty]⟩⟩,
  ⟨17,19,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,(.branch .leaf .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨18,1,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,(.branch .leaf .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨18,5,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,(.branch .leaf .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨18,7,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,(.branch .leaf .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨18,9,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.leaf,(.branch .empty .leaf),.leaf,.empty,(.branch .leaf .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨18,11,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,(.branch .leaf .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨18,17,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,(.branch .leaf .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨18,19,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,(.branch .leaf .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨19,1,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,(.branch .empty .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨19,5,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .leaf .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,(.branch .empty .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨19,7,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .leaf .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,(.branch .empty .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨19,9,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.leaf,(.branch .empty .leaf),.leaf,.empty,(.branch .empty .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨19,10,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .leaf .leaf),.leaf,.empty,(.branch .empty .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨19,11,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,(.branch .empty .leaf),(.branch .empty .leaf),.leaf,.empty,(.branch .empty .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨19,13,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,(.branch .empty .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨19,15,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),(.branch .leaf .leaf),.empty,(.branch .empty .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨19,17,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,(.branch .leaf .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨19,19,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,(.branch .empty .leaf),.empty,.empty,.empty]⟩⟩,
  ⟨20,9,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .leaf .leaf),.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,.empty]⟩⟩,
  ⟨20,11,⟨⟨#[[(false,0)],[(true,0)]], #[(0,1),(0,0)]⟩,⟨#[[(false,0),(false,1)],[(true,0),(true,1)]], #[(0,1),(0,1)]⟩,#[.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,(.branch .empty .leaf),.leaf,.empty,(.branch (.branch .empty .leaf) (.branch .empty .leaf)),.empty,.empty,.empty]⟩⟩
]

def pairs : List (Fin 25 × Fin 25) :=
  cases.map (fun c => (c.d0,c.e0))

theorem cases_count : cases.length = 32 := by decide

theorem all_checked :
    cases.all (fun c =>
      BB6.Agent4Automata.check (table c.d0 c.e0) c.cert) = true := by decide

theorem source_compatible (d0 e0 : Fin 25) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (hd0 : m (3,false) = decode d0)
    (he0 : m (4,false) = decode e0) : compatible (table d0 e0) m := by
  have e0s : raw10Remainder[27]! (0,false) = [decode 8] := by decide
  have e1s : raw10Remainder[27]! (1,false) = [decode 11] := by decide
  have e2s : raw10Remainder[27]! (2,false) = [decode 13] := by decide
  have e3s : raw10Remainder[27]! (2,true) = [decode 13] := by decide
  have h0 : m (0,false) = decode 8 := by simpa [e0s] using hm (0,false)
  have h1 : m (1,false) = decode 11 := by simpa [e1s] using hm (1,false)
  have h2 : m (2,false) = decode 13 := by simpa [e2s] using hm (2,false)
  have h3 : m (2,true) = decode 13 := by simpa [e3s] using hm (2,true)
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
  change (d0,e0) ∈ cases.map (fun c => (c.d0,c.e0)) at hp
  obtain ⟨c,hmem,heq⟩ := List.mem_map.mp hp
  have hcheck : BB6.Agent4Automata.check
      (table c.d0 c.e0) c.cert = true :=
    List.all_eq_true.mp all_checked c hmem
  obtain ⟨a,e,w⟩ := c
  dsimp at heq hcheck
  simp only [Prod.mk.injEq] at heq
  rcases heq with ⟨rfl,rfl⟩
  exact BB6.Agent4Automata.never (table a e) w hcheck m
    (source_compatible a e m hm hd0 he0)

theorem source_bound (B : Nat) (m : Machine)
    (hm : Fits raw10Remainder[27]! m)
    (d0 e0 : Fin 25)
    (hd0 : m (3,false) = decode d0)
    (he0 : m (4,false) = decode e0)
    (hp : (d0,e0) ∈ pairs) : WeightedBound B m :=
  weighted_of_never B m (source_never m hm d0 e0 hd0 he0 hp)

#print axioms cases_count
#print axioms all_checked
#print axioms source_compatible
#print axioms source_never
#print axioms source_bound
end BB6.Agent49.Box27D0E0FARMore
