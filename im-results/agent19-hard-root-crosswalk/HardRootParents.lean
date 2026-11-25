import HardRootCore

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent19HardRoot
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleRoster

abbrev root := BB6.CoverageAdapter.firstOneCylinder
noncomputable abbrev roster := BB6.Agent47CanonicalRaw114Accepted.roster

def p8 : PartialMachine := refine root (1,false) (some ⟨false,false,2⟩)
def p9 : PartialMachine := refine root (1,false) (some ⟨false,true,2⟩)
def p10 : PartialMachine := refine root (1,false) (some ⟨true,false,2⟩)
def p13 : PartialMachine := refine (refine root (1,false) (some ⟨true,true,2⟩)) (2,false) (some ⟨true,false,0⟩)
def p23 : PartialMachine := refine (refine root (1,false) (some ⟨true,true,2⟩)) (2,false) (some ⟨false,false,3⟩)
def p139 : PartialMachine := refine (refine root (1,false) (some ⟨true,true,2⟩)) (2,false) (some ⟨true,false,3⟩)

def addr8 : List Move := [⟨false,false,2⟩]
def addr9 : List Move := [⟨false,true,2⟩]
def addr10 : List Move := [⟨true,false,2⟩]
def addr13 : List Move := [⟨true,true,2⟩,⟨true,false,0⟩]
def addr23 : List Move := [⟨true,true,2⟩,⟨false,false,3⟩]
def addr139 : List Move := [⟨true,true,2⟩,⟨true,false,3⟩]

/-- Check actual address and all twelve slots, rather than classical equality. -/
def entryMatches (addr : List Move) (p : PartialMachine) (e : List Move × PartialMachine) : Bool :=
  decide (e.1 = addr) && sameTable e.2 p

theorem entryMatches_sound {addr : List Move} {p : PartialMachine}
    {e : List Move × PartialMachine} (h : entryMatches addr p e = true) : e = (addr,p) := by
  simp only [entryMatches, Bool.and_eq_true, decide_eq_true_eq] at h
  exact Prod.ext h.1 (sameTable_sound h.2)

theorem member_of_check (addr : List Move) (p : PartialMachine)
    (h : roster.any (entryMatches addr p) = true) : (addr,p) ∈ roster := by
  obtain ⟨e, he, hm⟩ := List.any_eq_true.mp h
  rw [← entryMatches_sound hm]
  exact he

theorem p8_mem : (addr8,p8) ∈ roster := member_of_check _ _ (by decide)
theorem p9_mem : (addr9,p9) ∈ roster := member_of_check _ _ (by decide)
theorem p10_mem : (addr10,p10) ∈ roster := member_of_check _ _ (by decide)
theorem p13_mem : (addr13,p13) ∈ roster := member_of_check _ _ (by decide)
theorem p23_mem : (addr23,p23) ∈ roster := member_of_check _ _ (by decide)
theorem p139_mem : (addr139,p139) ∈ roster := member_of_check _ _ (by decide)

#print axioms p8_mem
#print axioms p9_mem
#print axioms p10_mem
#print axioms p13_mem
#print axioms p23_mem
#print axioms p139_mem
end BB6.Agent19HardRoot
