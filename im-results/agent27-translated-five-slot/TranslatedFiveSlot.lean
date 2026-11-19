import TranslatedFiniteOracle
import FrontierMass

namespace BB6Coverage

/-- Five-slot translated finite-support cylinder found by a targeted search
    of the P4 depth-four frontier leaf. -/
def agent27A0 : Slot := (⟨0, by decide⟩, false)
def agent27B0 : Slot := (⟨1, by decide⟩, false)
def agent27C1 : Slot := (⟨2, by decide⟩, true)
def agent27D1 : Slot := (⟨3, by decide⟩, true)
def agent27E0 : Slot := (⟨4, by decide⟩, false)

def agent27A0Action : Transition := some ⟨true, true, 1⟩
def agent27B0Action : Transition := some ⟨true, false, 2⟩
def agent27C1Action : Transition := some ⟨false, true, 3⟩
def agent27D1Action : Transition := some ⟨true, true, 4⟩
def agent27E0Action : Transition := some ⟨true, false, 2⟩

def agent27P0 : PartialMachine := emptyTable
def agent27P1 : PartialMachine := refine agent27P0 agent27A0 agent27A0Action
def agent27P2 : PartialMachine := refine agent27P1 agent27B0 agent27B0Action
def agent27P3 : PartialMachine := refine agent27P2 agent27C1 agent27C1Action
def agent27P4 : PartialMachine := refine agent27P3 agent27D1 agent27D1Action
def agent27WordPump : PartialMachine := refine agent27P4 agent27E0 agent27E0Action

theorem agent27WordPump_is_P4_child :
    agent27WordPump = refine agent27P4 agent27E0 agent27E0Action := rfl

theorem agent27WordPump_translated_check :
    finiteTranslatedCheck agent27WordPump 2 3 = true := by decide

theorem agent27WordPump_cover (bound : Nat) :
    Cover (DecidedBelow bound) agent27WordPump :=
  finiteTranslatedCheck_sound agent27WordPump 2 3 bound
    (by decide) agent27WordPump_translated_check

theorem agent27WordPump_never (m : Machine)
    (hm : compatible agent27WordPump m) : NeverHalts m := by
  rcases (agent27WordPump_cover 0).sound m hm with hnever | ⟨n, hn, _⟩
  · exact hnever
  · omega

theorem agent27P4_mass : cylinderMass agent27P4 = 25^8 := by decide

theorem agent27WordPump_mass : cylinderMass agent27WordPump = 25^7 := by decide

/-- The larger five-slot cylinder is disjoint from Agent 32's seven-slot
    sibling, which uses E/0 = 1LF instead of E/0 = 1LC. -/
def agent32SecondWordE0Action : Transition := some ⟨true, false, 5⟩
def agent32SecondWordChild : PartialMachine :=
  refine agent27P4 agent27E0 agent32SecondWordE0Action

theorem agent27_disjoint_secondWord (m : Machine) :
    ¬ (compatible agent27WordPump m ∧ compatible agent32SecondWordChild m) := by
  intro h
  have hnew : m agent27E0 = agent27E0Action := by
    apply h.1
    simp [agent27WordPump, refine]
  have hold : m agent27E0 = agent32SecondWordE0Action := by
    apply h.2
    simp [agent32SecondWordChild, refine]
  have heq : agent27E0Action = agent32SecondWordE0Action :=
    hnew.symm.trans hold
  simp [agent27E0Action, agent32SecondWordE0Action] at heq

def agent32TwoMarkC1Action : Transition := some ⟨true, true, 3⟩
def agent32TwoMarkC1Cylinder : PartialMachine :=
  refine agent27P2 agent27C1 agent32TwoMarkC1Action

theorem agent27_disjoint_twoMark (m : Machine) :
    ¬ (compatible agent27WordPump m ∧ compatible agent32TwoMarkC1Cylinder m) := by
  intro h
  have hnew : m agent27C1 = agent27C1Action :=
    h.1 agent27C1 agent27C1Action (by decide)
  have hold : m agent27C1 = agent32TwoMarkC1Action :=
    h.2 agent27C1 agent32TwoMarkC1Action (by decide)
  have heq : agent27C1Action = agent32TwoMarkC1Action :=
    hnew.symm.trans hold
  simp [agent27C1Action, agent32TwoMarkC1Action] at heq

#print axioms agent27WordPump_translated_check
#print axioms agent27WordPump_cover
#print axioms agent27WordPump_never
#print axioms agent27P4_mass
#print axioms agent27WordPump_mass
#print axioms agent27_disjoint_secondWord
#print axioms agent27_disjoint_twoMark

end BB6Coverage

namespace BB6Coverage

set_option maxRecDepth 12000
set_option maxHeartbeats 0

/-- Exhaustively, among the 25 possible E/0 outcomes, this is the unique
    one-slot extension of P4 accepted by the three-step translated checker. -/
theorem agent27E0_three_step_unique (t : Transition) :
    finiteTranslatedCheck (refine agent27P4 agent27E0 t) 2 3 = true ↔
      t = agent27E0Action := by
  cases t with
  | none => decide
  | some mv =>
    cases mv with
    | mk write right next =>
      cases write <;> cases right <;>
        cases next with
        | mk n hn =>
          have hnCases : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
          rcases hnCases with h | h | h | h | h | h
          · subst n; cases Subsingleton.elim hn (by decide); decide
          · subst n; cases Subsingleton.elim hn (by decide); decide
          · subst n; cases Subsingleton.elim hn (by decide); decide
          · subst n; cases Subsingleton.elim hn (by decide); decide
          · subst n; cases Subsingleton.elim hn (by decide); decide
          · subst n; cases Subsingleton.elim hn (by decide); decide

#print axioms agent27E0_three_step_unique

end BB6Coverage
