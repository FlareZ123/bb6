import Agent46Raw13Data

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent46Raw13
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent46CanonicalCut

/-- The four-hole parent on the authentic #754 discovery path.
    A=1RB1LC B=1RC0LD C=1LA0RB D=1LB1LE E=------ F=------. -/
def pA := child ⟨true,false,2⟩
def pC := refine pA (2,true) (some ⟨false,true,1⟩)
def pB := refine pC (1,true) (some ⟨false,false,3⟩)
def pD0 := refine pB (3,false) (some ⟨true,false,1⟩)
def corridor := refine pD0 (3,true) (some ⟨true,false,4⟩)

def descend (t : Cut) (mv : Move) : Cut :=
  match t with
  | .split _ _ kids => kids mv
  | _ => .unresolved

/-- Extract the exact subcertificate, not a second independent enumeration. -/
def corridorCut : Cut :=
  descend (descend (descend (descend kid14 ⟨false,true,1⟩)
    ⟨false,false,3⟩) ⟨true,false,1⟩) ⟨true,false,4⟩

def corridorE0 := refine corridor (4,false) (some ⟨true,true,5⟩)
def corridorF1 := refine corridorE0 (5,true) (some ⟨false,true,4⟩)
def only754 := refine corridorF1 (4,true) (some ⟨false,false,0⟩)

theorem corridor_support : TNFSupport corridor 5 := by
  have ha : TNFSupport pA 3 :=
    refine_support raw13 (0,true) ⟨true,false,2⟩ 3 3 raw13_support (by decide) (by decide) (by decide)
  have hc : TNFSupport pC 3 :=
    refine_support pA (2,true) ⟨false,true,1⟩ 3 3 ha (by decide) (by decide) (by decide)
  have hb : TNFSupport pB 4 :=
    refine_support pC (1,true) ⟨false,false,3⟩ 3 4 hc (by decide) (by decide) (by decide)
  have hd : TNFSupport pD0 4 :=
    refine_support pB (3,false) ⟨true,false,1⟩ 4 4 hb (by decide) (by decide) (by decide)
  exact refine_support pD0 (3,true) ⟨true,false,4⟩ 4 5 hd (by decide) (by decide) (by decide)

theorem corridor_nohalt : weightedTNFNoAssignedHalt corridor :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (weightedTNFNoAssignedHalt_refine _ _ _
        (weightedTNFNoAssignedHalt_refine _ _ _
          (weightedTNFNoAssignedHalt_refine _ _ _ raw13_nohalt))))

theorem corridor_checked : check 7014 corridor 5 corridorCut = true := by decide

theorem corridor_complement :
    residuals corridor 5 corridorCut =
      [([⟨true,true,5⟩,⟨false,true,4⟩,⟨false,false,0⟩],only754)] := by rfl

theorem corridor_mass : openMass 4 5 corridorCut = 25 := by decide

/-- All 25^4 ordinary-label completions are discharged at weighted cutoff
    7014, except exactly the one-hole #754 cylinder (25 completions).
    The conclusion is modulo initial-state-fixing renaming. -/
theorem corridor_sound (m : Machine) (hm : TNFQuotientCompatible corridor m) :
    WeightedBound 7014 m ∨ TNFQuotientCompatible only754 m := by
  rcases sound 7014 corridor 5 corridorCut (by decide) corridor_support
    (by decide) corridor_nohalt corridor_checked m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · rw [corridor_complement] at he
    simp only [List.mem_singleton] at he
    subst e
    exact Or.inr hq

#print axioms corridor_checked
#print axioms corridor_complement
#print axioms corridor_sound
end BB6.Agent46Raw13
