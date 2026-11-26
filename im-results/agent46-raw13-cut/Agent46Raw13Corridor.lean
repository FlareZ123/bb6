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

/-- Extract the six-hole ancestor, before D0 is assigned. -/
def pBCut : Cut := descend (descend kid14 ⟨false,true,1⟩) ⟨false,false,3⟩

theorem pB_support : TNFSupport pB 4 := by
  have ha : TNFSupport pA 3 :=
    refine_support raw13 (0,true) ⟨true,false,2⟩ 3 3 raw13_support (by decide) (by decide) (by decide)
  have hc : TNFSupport pC 3 :=
    refine_support pA (2,true) ⟨false,true,1⟩ 3 3 ha (by decide) (by decide) (by decide)
  exact refine_support pC (1,true) ⟨false,false,3⟩ 3 4 hc (by decide) (by decide) (by decide)

theorem pB_nohalt : weightedTNFNoAssignedHalt pB :=
  weightedTNFNoAssignedHalt_refine _ _ _
    (weightedTNFNoAssignedHalt_refine _ _ _
      (weightedTNFNoAssignedHalt_refine _ _ _ raw13_nohalt))

def cutSlot : Cut → Option Slot
  | .split _ s _ => some s
  | _ => none

/-- Reuse the checked ancestor rather than re-running the whole child audit. -/
theorem descend_checked {B p cut t s} (h : check B p cut t = true)
    (hs : cutSlot t = some s) (mv : Move) (hmv : mv.next.val ≤ cut) :
    check B (refine p s (some mv)) (nextCut cut mv) (descend t mv) = true := by
  cases t with
  | split n s' kids =>
    simp only [cutSlot, Option.some.injEq] at hs
    subst s'
    simp only [check, Bool.and_eq_true] at h
    have hx := BB6.Agent31ThreeHole.allMoves_sound _ h.2 mv
    simpa only [hmv, if_pos, descend] using hx
  | unresolved => simp [cutSlot] at hs
  | closed => simp [cutSlot] at hs
  | bounded => simp [cutSlot] at hs
  | state => simp [cutSlot] at hs

theorem pB_checked : check 21269 pB 4 pBCut = true := by
  have h1 := descend_checked checked14 (by rfl : cutSlot kid14 = some (2,true))
    ⟨false,true,1⟩ (by decide)
  have h2 := descend_checked h1
    (by rfl : cutSlot (descend kid14 ⟨false,true,1⟩) = some (1,true))
    ⟨false,false,3⟩ (by decide)
  exact h2

theorem pB_complement : residuals pB 4 pBCut =
    [([⟨true,false,1⟩,⟨true,false,4⟩,⟨true,true,5⟩,⟨false,true,4⟩,
       ⟨false,false,0⟩],only754)] := by rfl

theorem pB_mass : openMass 6 4 pBCut = 50 := by decide

/-- The entire six-hole ancestor has only the #754 quotient cylinder left,
    including the factor of two for the first fresh state. -/
theorem pB_sound (m : Machine) (hm : TNFQuotientCompatible pB m) :
    WeightedBound 21269 m ∨ TNFQuotientCompatible only754 m := by
  rcases sound 21269 pB 4 pBCut (by decide) pB_support
    (by decide) pB_nohalt pB_checked m hm with hb | ⟨e,he,hq⟩
  · exact Or.inl hb
  · rw [pB_complement] at he
    simp only [List.mem_singleton] at he
    subst e
    exact Or.inr hq

/-- A weighted certificate for the single literal #754 cylinder suffices
    for every quotient-compatible completion of the six-hole ancestor. -/
theorem pB_cover_of_754 (B : Nat) (hB : 21269 ≤ B)
    (h754 : ∀ m, compatible only754 m → WeightedBound B m)
    (m : Machine) (hm : TNFQuotientCompatible pB m) : WeightedBound B m := by
  rcases pB_sound m hm with h | h
  · exact fun k d hk hd => Nat.le_trans (h k d hk hd) hB
  · exact safe_quotient (by decide) h754 m h

#print axioms pB_checked
#print axioms pB_complement
#print axioms pB_mass
#print axioms pB_sound
#print axioms pB_cover_of_754

end BB6.Agent46Raw13
