import FourHoleData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31FourHoleFrontier

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent31FourHole

/-- The exact ordinary refinement history from firstOneCylinder. -/
inductive RawRootPath : PartialMachine → Prop where
  | root : RawRootPath root
  | step {p n c mv}
      (parent : RawRootPath p)
      (hrun : knownRun p n = some c)
      (hhole : p (readSlot c) = none) :
      RawRootPath (refine p (readSlot c) (some mv))

theorem RawRootPath.rootRow {p : PartialMachine} (hp : RawRootPath p) :
    p initialSlot = some (some ⟨true, true, 1⟩) := by
  induction hp with
  | root => rfl
  | @step p n c mv parent hrun hhole ih =>
      exact refine_preserves_firstOne p (readSlot c) (some mv) hhole ih

/-- All 24 concrete ordinary instructions, in the certificate's stable order. -/
def allMoves : List Move :=
  (List.finRange 6).flatMap fun q =>
    [false, true].flatMap fun w =>
      [false, true].map fun r => ⟨w, r, q⟩

theorem allMoves_complete (mv : Move) : mv ∈ allMoves := by
  rcases mv with ⟨w, r, q⟩
  have hq : q ∈ List.finRange 6 := List.mem_finRange q
  have hw : w ∈ [false, true] := by cases w <;> simp
  have hr : r ∈ [false, true] := by cases r <;> simp
  unfold allMoves
  apply List.mem_flatMap.mpr
  refine ⟨q, hq, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨w, hw, ?_⟩
  apply List.mem_map.mpr
  exact ⟨r, hr, rfl⟩

theorem allMoves_length : allMoves.length = 24 := by decide

/-- A rooted frontier retains every off-path ordinary child explicitly.
    Closed nodes carry complete weighted certificates; residual nodes carry
    their exact ordinary refinement history. -/
inductive RootedFrontier (B : Nat) : PartialMachine → Type where
  | residual {p} (path : RawRootPath p) : RootedFrontier B p
  | closed {p} (path : RawRootPath p)
      (cert : WeightedTNFCertificate B p 6) : RootedFrontier B p
  | expand {p n c} (path : RawRootPath p)
      (hrun : knownRun p n = some c)
      (hhole : p (readSlot c) = none)
      (hweight : ∀ d ∈ possibleDelays (refine p (readSlot c) none) 0,
        d + n + 1 ≤ B)
      (children : ∀ mv : Move,
        RootedFrontier B (refine p (readSlot c) (some mv))) :
      RootedFrontier B p

inductive OpenLeaf {B : Nat} : {p : PartialMachine} →
    RootedFrontier B p → List Move → PartialMachine → Prop where
  | here {p} (path : RawRootPath p) :
      OpenLeaf (.residual path) [] p
  | child {p n c} (path : RawRootPath p)
      (hrun : knownRun p n = some c)
      (hhole : p (readSlot c) = none)
      (hweight : ∀ d ∈ possibleDelays (refine p (readSlot c) none) 0,
        d + n + 1 ≤ B)
      (children : ∀ mv : Move,
        RootedFrontier B (refine p (readSlot c) (some mv)))
      (mv : Move) {address : List Move} {q : PartialMachine}
      (hchild : OpenLeaf (children mv) address q) :
      OpenLeaf (.expand path hrun hhole hweight children) (mv :: address) q

theorem OpenLeaf.extends {B : Nat} {p : PartialMachine}
    {f : RootedFrontier B p} {address : List Move} {q : PartialMachine}
    (h : OpenLeaf f address q) :
    ∀ s t, p s = some t → q s = some t := by
  induction h with
  | here path =>
      intro s t hs
      exact hs
  | @child p n c path hrun hhole hweight children mv address q hchild ih =>
      intro s t hs
      have hne : s ≠ readSlot c := by
        intro he
        subst s
        rw [hhole] at hs
        contradiction
      have hchild' : (refine p (readSlot c) (some mv)) s = some t := by
        simp [refine, hne, hs]
      exact ih s t hchild'

def residuals {B : Nat} {p : PartialMachine} :
    RootedFrontier B p → List (List Move × PartialMachine)
  | .residual _ => [([], p)]
  | .closed _ _ => []
  | .expand _ _ _ _ children =>
      allMoves.flatMap fun mv =>
        (residuals (children mv)).map fun (address, q) => (mv :: address, q)

/-- Every completion is either bounded or belongs to an explicit residual
    cylinder. The halt child is charged with its exact incoming-delay weight. -/
theorem RootedFrontier.sound {B : Nat} {p : PartialMachine}
    (f : RootedFrontier B p) :
    ∀ m, compatible p m →
      WeightedBound B m ∨
        ∃ address q, OpenLeaf f address q ∧ compatible q m := by
  induction f with
  | @residual p path =>
      intro m hm
      exact Or.inr ⟨[], p, OpenLeaf.here path, hm⟩
  | closed path cert =>
      intro m hm
      exact Or.inl (cert.sound m hm)
  | @expand p n c path hrun hhole hweight children ih =>
      intro m hm
      cases hstep : m (readSlot c) with
      | none =>
          have hcomp : compatible (refine p (readSlot c) none) m := by
            intro s t h
            by_cases he : s = readSlot c
            · subst s
              have ht : t = none := by
                simpa [refine] using h.symm
              simpa [ht] using hstep
            · exact hm s t (by simpa [refine, he] using h)
          exact Or.inl (first_hole_weighted_halt B p n c
            (RawRootPath.rootRow path) hrun hhole hweight m hcomp)
      | some mv =>
          have hcomp : compatible (refine p (readSlot c) (some mv)) m := by
            intro s t h
            by_cases he : s = readSlot c
            · subst s
              have ht : t = some mv := by
                simpa [refine] using h.symm
              simpa [ht] using hstep
            · exact hm s t (by simpa [refine, he] using h)
          rcases ih mv m hcomp with hgood | ⟨address, q, hopen, hq⟩
          · exact Or.inl hgood
          · exact Or.inr ⟨mv :: address, q,
              OpenLeaf.child path hrun hhole hweight children mv hopen, hq⟩

/-- Distinct residual leaves have incompatible completion cylinders. -/
theorem RootedFrontier.openLeaves_disjoint {B : Nat} {p : PartialMachine}
    (f : RootedFrontier B p) :
    ∀ address1 q1 address2 q2,
      OpenLeaf f address1 q1 →
      OpenLeaf f address2 q2 →
      (address1, q1) ≠ (address2, q2) →
      ∀ m, ¬ (compatible q1 m ∧ compatible q2 m) := by
  induction f with
  | residual path =>
      intro address1 q1 address2 q2 h1 h2 hne m hcomp
      cases h1
      cases h2
      exact hne rfl
  | closed path cert =>
      intro address1 q1 address2 q2 h1
      cases h1
  | @expand p n c path hrun hhole hweight children ih =>
      intro address1 q1 address2 q2 h1 h2 hne m hcomp
      cases h1 with
      | @child p1 n1 c1 path1 hrun1 hhole1 hweight1 children1 mv1 address1 q1 hchild1 =>
        cases h2 with
        | @child p2 n2 c2 path2 hrun2 hhole2 hweight2 children2 mv2 address2 q2 hchild2 =>
          by_cases heq : mv1 = mv2
          · subst mv2
            have hne' : (address1, q1) ≠ (address2, q2) := by
              intro he
              apply hne
              cases he
              rfl
            exact ih mv1 address1 q1 address2 q2 hchild1 hchild2 hne' m hcomp
          · have h1ext := OpenLeaf.extends hchild1 (readSlot c) (some mv1)
              (by simp [refine])
            have h2ext := OpenLeaf.extends hchild2 (readSlot c) (some mv2)
              (by simp [refine])
            have hs1 := hcomp.1 (readSlot c) (some mv1) h1ext
            have hs2 := hcomp.2 (readSlot c) (some mv2) h2ext
            exact heq (Option.some.inj (hs1.symm.trans hs2))

/-- Weighted first-hole path validation at an arbitrary common bound. -/
def pathOKB (B : Nat) (p : PartialMachine) (cut : Nat) :
    List PathEntry → Bool
  | [] => true
  | (n, s, mv) :: xs =>
      decide (p s = none) &&
      decide ((knownRun p n).map readSlot = some s) &&
      decide (s.1.val < cut) &&
      decide (mv.next.val ≤ cut) &&
      weightOK p s n B &&
      pathOKB B (refine p s (some mv)) (advanceCut cut mv) xs

theorem pathOKB_cons {B : Nat} {p : PartialMachine} {cut n : Nat}
    {s : Slot} {mv : Move} {xs : List PathEntry}
    (h : pathOKB B p cut ((n, s, mv) :: xs) = true) :
    p s = none ∧
    (knownRun p n).map readSlot = some s ∧
    s.1.val < cut ∧
    mv.next.val ≤ cut ∧
    weightOK p s n B = true ∧
    pathOKB B (refine p s (some mv)) (advanceCut cut mv) xs = true := by
  simpa only [pathOKB, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

def extractRunConfig {p : PartialMachine} {n : Nat} {s : Slot}
    (h : (knownRun p n).map readSlot = some s) :
    {c // knownRun p n = some c} :=
  match hr : knownRun p n with
  | none => False.elim (by simp [hr] at h)
  | some c => ⟨c, rfl⟩

/-- Build a rooted frontier along a validated path, preserving all siblings. -/
def buildFrontierB (B : Nat) (p : PartialMachine) (cut : Nat)
    (hp : RawRootPath p) :
    (xs : List PathEntry) →
    pathOKB B p cut xs = true →
    WeightedTNFCertificate B (pathEnd p cut xs).1 6 →
    RootedFrontier B p
  | [], _, cert => .closed hp cert
  | (n, s, mv) :: xs, h, cert => by
      have hfields := pathOKB_cons h
      rcases hfields with ⟨hhole, hread, _, _, hweight, htail⟩
      let c := (extractRunConfig hread).val
      have hr : knownRun p n = some c := (extractRunConfig hread).property
      have hs : readSlot c = s := by
        have h' : (some c).map readSlot = some s := by
          simpa [hr] using hread
        simpa using h'
      have hhole' : p (readSlot c) = none := by
        simpa [hs] using hhole
      have hw : ∀ d ∈ possibleDelays (refine p (readSlot c) none) 0,
          d + n + 1 ≤ B := by
        simpa [hs.symm] using (weightOK_sound p s n B hweight)
      have htail' : pathOKB B (refine p (readSlot c) (some mv))
          (advanceCut cut mv) xs = true := by
        simpa [hs.symm] using htail
      have cert' : WeightedTNFCertificate B
          (pathEnd (refine p (readSlot c) (some mv)) (advanceCut cut mv) xs).1 6 := by
        simpa [pathEnd, hs.symm] using cert
      exact .expand hp hr hhole' hw (fun actual =>
        if heq : actual = mv then
          by
            simpa [heq] using
              (buildFrontierB B (refine p (readSlot c) (some mv))
                (advanceCut cut mv) (RawRootPath.step (mv := mv) hp hr hhole')
                xs htail' cert')
        else
          .residual (RawRootPath.step (mv := actual) hp hr hhole'))
termination_by structural xs => xs

/-- The four-hole certificate is rooted exactly at the authentic
    seven-edge descendant of firstOneCylinder. -/
def wideCertificate_root :
    WeightedTNFCertificate 395 (pathEnd root 2 (path.take 7)).1 6 := by
  simpa [wideParent] using BB6.Agent31FourHole.certificate

/-- All halt siblings along the seven-edge prefix fit the same local bound. -/
theorem path_prefix_checked :
    pathOKB 395 root 2 (path.take 7) = true := by
  decide

/-- A root-to-subtree frontier: all 23 off-path ordinary instructions are
    retained at each of seven first-hole expansions, and the four-hole
    cylinder at the end is closed by its complete weighted certificate. -/
def rootFrontier : RootedFrontier 395 root :=
  buildFrontierB 395 root 2 RawRootPath.root (path.take 7)
    path_prefix_checked wideCertificate_root

#print axioms rootFrontier_sound
#print axioms rootFrontier_openLeaves_disjoint


end BB6.Agent31FourHoleFrontier
