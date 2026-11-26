import CachedZipAudit
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace BB6.Agent11SemanticChunks
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31ThreeHole BB6.Agent10ZipAudit
open BB6Coverage.Agent10ZipAudit

abbrev Bound (B : Nat) (p : PartialMachine) : Prop :=
  ∀ m, compatible p m → WeightedBound B m

def supportOK (p : PartialMachine) (cut : Nat) : Bool :=
  (List.finRange 6).all fun q => [false,true].all fun a =>
    match p (q,a) with
    | none => true
    | some none => decide (q.val < cut)
    | some (some mv) => decide (q.val < cut ∧ mv.next.val < cut)

theorem supportOK_sound {p cut} (h : supportOK p cut = true) : TNFSupport p cut := by
  intro s t ht
  rcases s with ⟨q,a⟩
  have hh := List.all_eq_true.mp (List.all_eq_true.mp h q (List.mem_finRange q)) a (by cases a <;> simp)
  rw [ht] at hh
  cases t with
  | none => exact ⟨of_decide_eq_true hh,by intro mv hv; contradiction⟩
  | some v =>
    have hc : q.val < cut ∧ v.next.val < cut := of_decide_eq_true hh
    exact ⟨hc.1,by intro mv he; cases he; exact hc.2⟩

/-- Semantic composition at the actual first hole, checking only the existing
labels and least-fresh label. In particular E/F siblings need no duplicate audit. -/
theorem join_normalized (B cut : Nat) (p : PartialMachine) (n : Nat) (s : Slot)
    (hc : 0 < cut) (hs : supportOK p cut = true)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hq : zipQueryOK B p n s = true)
    (hk : ∀ mv, mv.next.val ≤ cut → Bound B (refine p s (some mv))) : Bound B p := by
  obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound hq
  cases hr : knownRun p n with
  | none => simp [hr] at hread
  | some c =>
    have he : readSlot c = s := by simpa [hr] using hread
    have h := first_hole_tnf_cover B cut p n c hc (supportOK_sound hs) hf hr
      (by simpa [he] using hhole)
      (by simpa [he] using weightOK_sound p s n B hw)
      (fun mv hm => by simpa [he] using hk mv (Nat.le_of_lt hm))
      (fun q hq w r => by simpa [he] using hk ⟨w,r,q⟩ (by simp [hq]))
    exact h.sound

/-- Semantic use of the original audit checker; the no-halt invariant is
unnecessary because each leaf independently proves a semantic bound. -/
theorem bound_of_check (B : Nat) (p : PartialMachine) (t : Audit)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (h : zipCheck B p t = true) : Bound B p := by
  induction t generalizing p with
  | last n s =>
    have hv : zipQueryOK B p n s = true ∧ restOK p s = true := by
      simpa only [zipCheck,Bool.and_eq_true] using h
    obtain ⟨hread,hhole,hw⟩ := zipQueryOK_sound hv.1
    cases hr : knownRun p n with
    | none => simp [hr] at hread
    | some c =>
      have he : readSlot c = s := by simpa [hr] using hread
      exact last_hole_sound B p n c hf hr (by simpa [he] using hhole)
        (by simpa [he] using restOK_sound p s hv.2)
        (by simpa [he] using weightOK_sound p s n B hw)
  | cycle e k r b =>
    have hv : 0 < k ∧ zipCycle p e k r b = true := by simpa only [zipCheck,Bool.and_eq_true,decide_eq_true_eq] using h
    exact fun m hm => weighted_never B m (zipCycle_sound p e k r b hv.1 hv.2 m hm)
  | far rev d cert => exact fun m hm => weighted_never B m (farSound p rev cert (by simpa only [zipCheck] using h) m hm)
  | proven q safe =>
    have he : p = q := tableOK_sound p q (by simpa only [zipCheck] using h)
    subst q
    exact fun m hm => weighted_never B m (safe m hm)
  | split n s kids ih =>
    have hv : zipQueryOK B p n s = true ∧ allMoves (fun mv => zipCheck B (refine p s (some mv)) (kids mv)) = true := by
      simpa only [zipCheck,Bool.and_eq_true] using h
    have hu := (zipQueryOK_sound hv.1).2.1
    refine join_normalized B 6 p n s (by decide) ?_ hf hv.1 ?_
    · unfold supportOK
      apply List.all_eq_true.mpr
      intro q _
      apply List.all_eq_true.mpr
      intro a _
      cases hp : p (q,a) with
      | none => rfl
      | some t =>
        cases t with
        | none => exact decide_eq_true q.isLt
        | some mv => exact decide_eq_true ⟨q.isLt,mv.next.isLt⟩
    · intro mv _
      exact ih mv _ (refine_preserves_firstOne p s (some mv) hu hf) (allMoves_sound _ hv.2 mv)

theorem bound_of_cached (B : Nat) (p : PartialMachine) (t : Audit)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (h : BB6.Agent10CachedAudit.cachedCheck B p BB6.Agent10CachedAudit.rootCursor t = true) : Bound B p :=
  bound_of_check B p t hf ((BB6.Agent10CachedAudit.root_check_eq B p t) ▸ h)

#print axioms bound_of_cached
#print axioms join_normalized
#print axioms bound_of_check
end BB6.Agent11SemanticChunks
