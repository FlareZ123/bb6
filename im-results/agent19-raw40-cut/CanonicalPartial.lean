import PartialAudit
import CanonicalFrontier
import ZipPrefixAudit

set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent19CanonicalPartial
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31ThreeHole BB6.Agent10ZipAudit BB6.Agent48PrefixAudit BB6.Agent47PartialAudit BB6.Agent47CanonicalFrontier BB6.Agent50TNFPilot

def supportOK (p : PartialMachine) (cut : Nat) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun b =>
    match p (q,b) with
    | none => true
    | some none => decide (q.val < cut)
    | some (some mv) => decide (q.val < cut ∧ mv.next.val < cut)

theorem supportOK_sound (p : PartialMachine) (cut : Nat) (h : supportOK p cut = true) : TNFSupport p cut := by
  intro s t ht
  rcases s with ⟨q,b⟩
  have hq := List.all_eq_true.mp h q (List.mem_finRange q)
  have hb : b ∈ [false,true] := by cases b <;> simp
  have hc := List.all_eq_true.mp hq b hb
  rw [ht] at hc
  cases t with
  | none =>
    refine ⟨of_decide_eq_true hc,?_⟩
    intro mv he; contradiction
  | some mv =>
    have hlt : q.val < cut ∧ mv.next.val < cut := of_decide_eq_true hc
    refine ⟨hlt.1,?_⟩
    intro mv' he; cases he; exact hlt.2

/-- Retain only successor labels already introduced, plus the least fresh label.
    The soundness proof transports the omitted assignments by a root-fixing permutation. -/
def canonicalCheck (B : Nat) (p : PartialMachine) (cut : Nat) (t : PartialAudit) : Bool :=
  match t with
  | .unresolved => true
  | .closed a => prefixCheck B p a
  | .split n s kids => zipQueryOK B p n s &&
      allMoves (fun mv => if mv.next.val ≤ cut then
        canonicalCheck B (refine p s (some mv)) (max cut (mv.next.val+1)) (kids mv)
        else true)
termination_by structural t

def canonicalResiduals (p : PartialMachine) (cut : Nat) (t : PartialAudit) : List (List Move × PartialMachine) :=
  match t with
  | .unresolved => [([],p)]
  | .closed _ => []
  | .split _ s kids => (auditMoves.filter fun mv => mv.next.val ≤ cut).flatMap fun mv =>
      (canonicalResiduals (refine p s (some mv)) (max cut (mv.next.val+1)) (kids mv)).map fun e => (mv::e.1,e.2)
termination_by structural t

theorem canonicalSound (B : Nat) (p : PartialMachine) (cut : Nat) (t : PartialAudit)
    (hcut : 0 < cut) (hs : TNFSupport p cut)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hno : weightedTNFNoAssignedHalt p)
    (h : canonicalCheck B p cut t = true) :
    ∀ m, TNFQuotientCompatible p m → WeightedBound B m ∨
      ∃ e ∈ canonicalResiduals p cut t, TNFQuotientCompatible e.2 m := by
  induction t generalizing p cut with
  | unresolved =>
    intro m hm
    exact Or.inr ⟨([],p),by simp [canonicalResiduals],hm⟩
  | closed a =>
    intro m hm
    have ha : zipCheck B p a = true := by simpa only [canonicalCheck,prefixCheck_eq] using h
    exact Or.inl (quotientSafe hf (certifiedZip B p a hf hno ha).sound m hm)
  | split n s kids ih =>
    have hv : zipQueryOK B p n s = true ∧ allMoves (fun mv => if mv.next.val ≤ cut then
        canonicalCheck B (refine p s (some mv)) (max cut (mv.next.val+1)) (kids mv) else true) = true := by
      simpa only [canonicalCheck, Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound hv.1
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
      · exact Or.inl hb
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
        rcases ih mv (refine p s (some mv)) c' hc' hs' hf' hn' hchild m hq with hb | ⟨e,he,hm'⟩
        · exact Or.inl hb
        · refine Or.inr ⟨(mv::e.1,e.2),?_,hm'⟩
          simp only [canonicalResiduals]
          apply List.mem_flatMap.mpr
          exact ⟨mv,List.mem_filter.mpr ⟨auditMoves_complete mv,by simp [hv']⟩,List.mem_map.mpr ⟨e,he,rfl⟩⟩

#print axioms canonicalSound
end BB6.Agent19CanonicalPartial
