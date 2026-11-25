import Agent46StateClosure
import ZipThreeHoleAudit
import WeightedTNFQueueOrbit

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent46CanonicalCut
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6.Agent46StateClosure

/-- A quotient-preserving partial audit. Only branches to introduced
    states and the least fresh state need certificates. -/
inductive Cut where
  | unresolved
  | closed (t : Audit)
  | bounded (q : PartialMachine) (C : Nat) (safe : ∀ m, compatible q m → WeightedBound C m)
  | state (mask : Nat)
  | split (n : Nat) (s : Slot) (kids : Move → Cut)

def nextCut (cut : Nat) (mv : Move) := max cut (mv.next.val+1)

def check (B : Nat) (p : PartialMachine) (cut : Nat) : Cut → Bool
  | .unresolved => true
  | .closed t => zipCheck B p t
  | .bounded q C _ => tableOK p q && decide (C ≤ B)
  | .state mask => stateCheck p mask
  | .split n s kids => zipQueryOK B p n s &&
      BB6.Agent31ThreeHole.allMoves (fun mv =>
        if mv.next.val ≤ cut then
          check B (refine p s (some mv)) (nextCut cut mv) (kids mv)
        else true)
termination_by structural t => t

def moves : List Move := (List.finRange 6).flatMap fun q =>
  [false,true].flatMap fun w => [false,true].map fun r => ⟨w,r,q⟩

theorem moves_complete (mv : Move) : mv ∈ moves := by
  rcases mv with ⟨w,r,q⟩
  exact List.mem_flatMap.mpr ⟨q, List.mem_finRange q,
    List.mem_flatMap.mpr ⟨w, by cases w <;> simp,
      List.mem_map.mpr ⟨r, by cases r <;> simp, rfl⟩⟩⟩

def residuals (p : PartialMachine) (cut : Nat) : Cut → List (List Move × PartialMachine)
  | .unresolved => [([],p)]
  | .closed _ => []
  | .bounded _ _ _ => []
  | .state _ => []
  | .split _ s kids =>
      (moves.filter fun mv => decide (mv.next.val ≤ cut)).flatMap fun mv =>
        (residuals (refine p s (some mv)) (nextCut cut mv) (kids mv)).map
          fun e => (mv :: e.1,e.2)
termination_by structural t => t

def byCutMove (xs : List Cut) (mv : Move) : Cut :=
  xs[12*mv.write.toNat+6*mv.right.toNat+mv.next.val]?.getD .unresolved

theorem safe_quotient {B : Nat} {p : PartialMachine}
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hs : ∀ m, compatible p m → WeightedBound B m)
    (m : Machine) (hq : TNFQuotientCompatible p m) : WeightedBound B m := by
  rcases hq with ⟨e,he,hm⟩
  have hz := firstOne_terminal p hf (renameTable e m) hm
  exact weighted_rename_back B e m he ((zeroNext_none_rename_iff e m he).mp hz) (hs _ hm)

/-- All discarded fresh labels are accounted for by the actual first-hole
    renaming theorem, including its incoming blank-delay transport. -/
theorem sound (B : Nat) (p : PartialMachine) (cut : Nat) (t : Cut)
    (hc : 0 < cut) (hs : TNFSupport p cut)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hn : weightedTNFNoAssignedHalt p) (hcheck : check B p cut t = true) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound B m ∨
      ∃ e ∈ residuals p cut t, TNFQuotientCompatible e.2 m := by
  induction t generalizing p cut with
  | unresolved =>
    intro m hm
    exact Or.inr ⟨([],p), by simp [residuals], hm⟩
  | closed t =>
    intro m hm
    exact Or.inl (safe_quotient hf (certifiedZip B p t hf hn hcheck).sound m hm)
  | bounded q C safe =>
    have hv : tableOK p q = true ∧ C ≤ B := by
      simpa only [check, Bool.and_eq_true, decide_eq_true_eq] using hcheck
    have he := tableOK_sound p q hv.1
    subst q
    intro m hm
    apply Or.inl
    apply safe_quotient hf _ m hm
    intro m' hm' k d hk hd
    exact Nat.le_trans (safe m' hm' k d hk hd) hv.2
  | state mask =>
    intro m hm
    apply Or.inl
    apply safe_quotient hf _ m hm
    intro m' hm'
    exact weighted_never B m' (stateCheck_sound p mask hcheck m' hm')
  | split n s kids ih =>
    have hv : zipQueryOK B p n s = true ∧
        BB6.Agent31ThreeHole.allMoves (fun mv =>
          if mv.next.val ≤ cut then
            check B (refine p s (some mv)) (nextCut cut mv) (kids mv)
          else true) = true := by
      simpa only [check, Bool.and_eq_true] using hcheck
    obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound hv.1
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have hslot : readSlot c = s := by simpa [hr] using hread
      have hslt : s.1.val < cut := by
        rw [← hslot]
        exact knownRun_support p cut hc hs n c hr
      have hhalt : ∀ m, compatible (refine p s none) m → WeightedBound B m := by
        rw [← hslot]
        exact first_hole_weighted_halt B p n c hf hr
          (by simpa only [hslot] using hhole)
          (by simpa only [hslot] using weightOK_sound p s n B hw)
      intro m hm
      rcases tnf_branch_frontier B cut p s hc hs hhole hslt hf hhalt m hm with
        hb | ⟨mv,hmv,hq⟩
      · exact Or.inl hb
      · have hle : cut ≤ nextCut cut mv := Nat.le_max_left _ _
        have hpos : 0 < nextCut cut mv := Nat.lt_of_lt_of_le hc hle
        have hnext : mv.next.val < nextCut cut mv :=
          Nat.lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_max_right _ _)
        have hs' := refine_support p s mv cut (nextCut cut mv) hs hle
          (Nat.lt_of_lt_of_le hslt hle) hnext
        have hf' := refine_preserves_firstOne p s (some mv) hhole hf
        have hn' := weightedTNFNoAssignedHalt_refine p s mv hn
        have hchild := allMoves_sound _ hv.2 mv
        have hchecked : check B (refine p s (some mv)) (nextCut cut mv) (kids mv) = true := by
          simpa [hmv] using hchild
        rcases ih mv (refine p s (some mv)) (nextCut cut mv) hpos hs' hf' hn' hchecked m hq with
          hb | ⟨e,he,heq⟩
        · exact Or.inl hb
        · exact Or.inr ⟨(mv :: e.1,e.2), List.mem_flatMap.mpr
            ⟨mv, List.mem_filter.mpr ⟨moves_complete mv, by simpa using hmv⟩,
              List.mem_map.mpr ⟨e,he,rfl⟩⟩, heq⟩

/-- Exact ordinary-label completion mass diagnostic. At a fresh label
    branch the representative accounts for every one of the unused names. -/
def openMass (holes cut : Nat) : Cut → Nat
  | .unresolved => 25^holes
  | .closed _ => 0
  | .bounded _ _ _ => 0
  | .state _ => 0
  | .split _ _ kids =>
      (moves.filter fun mv => decide (mv.next.val ≤ cut)).foldl
        (fun acc mv => acc +
          (if mv.next.val = cut then 6-cut else 1) *
            openMass (holes-1) (nextCut cut mv) (kids mv)) 0
termination_by structural t => t

#print axioms sound
end BB6.Agent46CanonicalCut
