import FastZipWeight
import CanonicalPartial

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent29CanonicalFast
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent47CanonicalFrontier BB6.Agent29FastZipWeight

def check (B : Nat) (p : PartialMachine) (cut : Nat) : Audit → Bool
  | .last n s => fastCheck B p (.last n s)
  | .cycle e k r b => fastCheck B p (.cycle e k r b)
  | .far rev d C => fastCheck B p (.far rev d C)
  | .proven q safe => fastCheck B p (.proven q safe)
  | .split n s kids => fastQueryOK B p n s &&
      allMoves (fun mv => if mv.next.val ≤ cut then
        check B (refine p s (some mv)) (max cut (mv.next.val+1)) (kids mv)
        else true)
termination_by structural t => t

/-- A fully closed first-use canonical audit suffices directly. The omitted
    physical children are transported by the original TNF quotient theorem. -/
theorem sound (B : Nat) (p : PartialMachine) (cut : Nat) (t : Audit)
    (hcut : 0 < cut) (hs : TNFSupport p cut)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : check B p cut t = true) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound B m := by
  induction t generalizing p cut with
  | last n s =>
    exact quotientSafe hf (certifiedFast B p (.last n s) hf hno h).sound
  | cycle e k r b =>
    exact quotientSafe hf (certifiedFast B p (.cycle e k r b) hf hno h).sound
  | far rev d C =>
    exact quotientSafe hf (certifiedFast B p (.far rev d C) hf hno h).sound
  | proven q safe =>
    exact quotientSafe hf (certifiedFast B p (.proven q safe) hf hno h).sound
  | split n s kids ih =>
    have hv : fastQueryOK B p n s = true ∧ allMoves (fun mv => if mv.next.val ≤ cut then
        check B (refine p s (some mv)) (max cut (mv.next.val+1)) (kids mv) else true) = true := by
      simpa only [check, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound ((fastQueryOK_eq B p n s).symm.trans hv.1)
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hsc : readSlot c = s := by simpa [hr] using hread
      have hslot : s.1.val < cut := by
        rw [← hsc]
        exact knownRun_support p cut hcut hs n c hr
      have hh : ∀ m, compatible (refine p s none) m → WeightedBound B m := by
        simpa only [hsc] using first_hole_weighted_halt B p n c hf hr (by simpa only [hsc] using hhole)
          (by simpa only [hsc] using weightOK_sound p s n B hw)
      intro m hm
      rcases tnf_branch_frontier B cut p s hcut hs hhole hslot hf hh m hm with hb | ⟨mv,hv',hq⟩
      · exact hb
      · let c' := max cut (mv.next.val+1)
        have hc' : 0 < c' := Nat.lt_of_lt_of_le hcut (Nat.le_max_left _ _)
        have hs' : TNFSupport (refine p s (some mv)) c' :=
          refine_support p s mv cut c' hs (Nat.le_max_left _ _)
            (Nat.lt_of_lt_of_le hslot (Nat.le_max_left _ _))
            (Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _))
        have hf' := refine_preserves_firstOne p s (some mv) hhole hf
        have hn' := weightedTNFNoAssignedHalt_refine p s mv hno
        have hchild := allMoves_sound _ hv.2 mv
        simp only [if_pos hv'] at hchild
        exact ih mv (refine p s (some mv)) c' hc' hs' hf' hn' hchild m hq

theorem bound (B : Nat) (p : PartialMachine) (cut : Nat) (t : Audit)
    (hcut : 0 < cut) (hs : TNFSupport p cut)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : check B p cut t = true) :
    ∀ m, compatible p m → WeightedBound B m :=
  fun m hm => sound B p cut t hcut hs hf hno h m (compatible_quotient hm)

/-- Kernel-check the 24 move implications once; omitted fresh labels are
    discharged by reduction of the conditional, without checking their trees. -/
theorem split24 (B : Nat) (p : PartialMachine) (cut n : Nat) (s : Slot)
    (xs : List Audit) (hq : fastQueryOK B p n s = true)
    (h00 : (if 0 ≤ cut then check B (refine p s (some ⟨false,false,0⟩)) (max cut 1) (byMove xs ⟨false,false,0⟩) else true) = true)
    (h01 : (if 1 ≤ cut then check B (refine p s (some ⟨false,false,1⟩)) (max cut 2) (byMove xs ⟨false,false,1⟩) else true) = true)
    (h02 : (if 2 ≤ cut then check B (refine p s (some ⟨false,false,2⟩)) (max cut 3) (byMove xs ⟨false,false,2⟩) else true) = true)
    (h03 : (if 3 ≤ cut then check B (refine p s (some ⟨false,false,3⟩)) (max cut 4) (byMove xs ⟨false,false,3⟩) else true) = true)
    (h04 : (if 4 ≤ cut then check B (refine p s (some ⟨false,false,4⟩)) (max cut 5) (byMove xs ⟨false,false,4⟩) else true) = true)
    (h05 : (if 5 ≤ cut then check B (refine p s (some ⟨false,false,5⟩)) (max cut 6) (byMove xs ⟨false,false,5⟩) else true) = true)
    (h06 : (if 0 ≤ cut then check B (refine p s (some ⟨false,true,0⟩)) (max cut 1) (byMove xs ⟨false,true,0⟩) else true) = true)
    (h07 : (if 1 ≤ cut then check B (refine p s (some ⟨false,true,1⟩)) (max cut 2) (byMove xs ⟨false,true,1⟩) else true) = true)
    (h08 : (if 2 ≤ cut then check B (refine p s (some ⟨false,true,2⟩)) (max cut 3) (byMove xs ⟨false,true,2⟩) else true) = true)
    (h09 : (if 3 ≤ cut then check B (refine p s (some ⟨false,true,3⟩)) (max cut 4) (byMove xs ⟨false,true,3⟩) else true) = true)
    (h10 : (if 4 ≤ cut then check B (refine p s (some ⟨false,true,4⟩)) (max cut 5) (byMove xs ⟨false,true,4⟩) else true) = true)
    (h11 : (if 5 ≤ cut then check B (refine p s (some ⟨false,true,5⟩)) (max cut 6) (byMove xs ⟨false,true,5⟩) else true) = true)
    (h12 : (if 0 ≤ cut then check B (refine p s (some ⟨true,false,0⟩)) (max cut 1) (byMove xs ⟨true,false,0⟩) else true) = true)
    (h13 : (if 1 ≤ cut then check B (refine p s (some ⟨true,false,1⟩)) (max cut 2) (byMove xs ⟨true,false,1⟩) else true) = true)
    (h14 : (if 2 ≤ cut then check B (refine p s (some ⟨true,false,2⟩)) (max cut 3) (byMove xs ⟨true,false,2⟩) else true) = true)
    (h15 : (if 3 ≤ cut then check B (refine p s (some ⟨true,false,3⟩)) (max cut 4) (byMove xs ⟨true,false,3⟩) else true) = true)
    (h16 : (if 4 ≤ cut then check B (refine p s (some ⟨true,false,4⟩)) (max cut 5) (byMove xs ⟨true,false,4⟩) else true) = true)
    (h17 : (if 5 ≤ cut then check B (refine p s (some ⟨true,false,5⟩)) (max cut 6) (byMove xs ⟨true,false,5⟩) else true) = true)
    (h18 : (if 0 ≤ cut then check B (refine p s (some ⟨true,true,0⟩)) (max cut 1) (byMove xs ⟨true,true,0⟩) else true) = true)
    (h19 : (if 1 ≤ cut then check B (refine p s (some ⟨true,true,1⟩)) (max cut 2) (byMove xs ⟨true,true,1⟩) else true) = true)
    (h20 : (if 2 ≤ cut then check B (refine p s (some ⟨true,true,2⟩)) (max cut 3) (byMove xs ⟨true,true,2⟩) else true) = true)
    (h21 : (if 3 ≤ cut then check B (refine p s (some ⟨true,true,3⟩)) (max cut 4) (byMove xs ⟨true,true,3⟩) else true) = true)
    (h22 : (if 4 ≤ cut then check B (refine p s (some ⟨true,true,4⟩)) (max cut 5) (byMove xs ⟨true,true,4⟩) else true) = true)
    (h23 : (if 5 ≤ cut then check B (refine p s (some ⟨true,true,5⟩)) (max cut 6) (byMove xs ⟨true,true,5⟩) else true) = true)
    : check B p cut (.split n s (byMove xs)) = true := by
  simp only [check, Bool.and_eq_true]
  refine ⟨hq, allMoves_of _ ?_⟩
  intro mv
  rcases mv with ⟨w,r,q⟩
  have hq' : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq' with rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases w <;> cases r
  · exact h00
  · exact h06
  · exact h12
  · exact h18
  · exact h01
  · exact h07
  · exact h13
  · exact h19
  · exact h02
  · exact h08
  · exact h14
  · exact h20
  · exact h03
  · exact h09
  · exact h15
  · exact h21
  · exact h04
  · exact h10
  · exact h16
  · exact h22
  · exact h05
  · exact h11
  · exact h17
  · exact h23

#print axioms split24
#print axioms sound
#print axioms bound
end BB6.Agent29CanonicalFast
