import TNFPilot

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6.Agent50RootFrontier
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot

/-- Any ordinary assignment at a first undefined query is a genuine
    blank-root descendant. Unlike the normalized TNF path, this relation
    keeps every one of the 24 concrete successor labels. -/
inductive RawRootPath : PartialMachine → Prop where
  | root : RawRootPath BB6.Agent50TNFPilot.root
  | step {p n c mv}
      (parent : RawRootPath p)
      (hrun : knownRun p n = some c)
      (hhole : p (readSlot c) = none) :
      RawRootPath (refine p (readSlot c) (some mv))

theorem RawRootPath.rootRow {p : PartialMachine} (hp : RawRootPath p) :
    p initialSlot = some (some ⟨true, true, 1⟩) := by
  induction hp with
  | root => rfl
  | step parent hrun hhole ih =>
      exact refine_preserves_firstOne p (readSlot c) (some mv) hhole ih

/-- The explicit alphabet of all 24 ordinary instructions. -/
def allMoves : List Move :=
  (List.finRange 6).flatMap fun q =>
    [false, true].flatMap fun w =>
      [false, true].map fun r => ⟨w, r, q⟩

theorem allMoves_complete (mv : Move) : mv ∈ allMoves := by
  rcases mv with ⟨w, r, q⟩
  have hq : q ∈ List.finRange 6 := List.mem_finRange q
  have hw : w ∈ [false, true] := by cases w <;> simp
  have hr : r ∈ [false, true] := by cases r <;> simp
  simp [allMoves, hq, hw, hr]

theorem allMoves_length : allMoves.length = 24 := by decide

/-- A rooted frontier has three kinds of leaves:
    * open: an explicit residual cylinder, with its blank-root path;
    * closed: a previously checked weighted certificate;
    * expand: all 24 ordinary instructions are retained, while the
      first-hole halt child is discharged by its exact incoming-delay bound.

    There is no fresh-state quotient in this structure: concrete labels are
    retained, so its residual manifest can be compared slot-for-slot. -/
inductive RootedFrontier (B : Nat) : PartialMachine → Type where
  | open {p} (path : RawRootPath p) : RootedFrontier B p
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

/-- A leaf address records the exact ordinary instructions taken from the
    root to an open residual cylinder. -/
inductive OpenLeaf {B : Nat} : {p : PartialMachine} →
    RootedFrontier B p → List Move → PartialMachine → Prop where
  | here {p} (path : RawRootPath p) :
      OpenLeaf (.open path) [] p
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

/-- Flatten a frontier to exact path-address/table pairs. The recursive
    order is deterministic and follows allMoves. -/
def residuals {B : Nat} {p : PartialMachine} :
    RootedFrontier B p → List (List Move × PartialMachine)
  | .open _ => [([], p)]
  | .closed _ _ => []
  | .expand _ _ _ _ children =>
      allMoves.flatMap fun mv =>
        (residuals (children mv)).map fun (address, q) => (mv :: address, q)

theorem OpenLeaf.mem {B : Nat} {p : PartialMachine}
    {f : RootedFrontier B p} {address : List Move} {q : PartialMachine}
    (h : OpenLeaf f address q) : (address, q) ∈ residuals f := by
  induction h with
  | here path => simp [residuals]
  | child path hrun hhole hweight children mv hchild ih =>
      apply List.mem_flatMap.mpr
      refine ⟨mv, allMoves_complete mv, ?_⟩
      apply List.mem_map.mpr
      exact ⟨(address, q), ih, rfl⟩

theorem OpenLeaf.extends {B : Nat} {p : PartialMachine}
    {f : RootedFrontier B p} {address : List Move} {q : PartialMachine}
    (h : OpenLeaf f address q) :
    ∀ s t, p s = some t → q s = some t := by
  induction h with
  | here path =>
      intro s t hs
      exact hs
  | child path hrun hhole hweight children mv hchild ih =>
      intro s t hs
      have hne : s ≠ readSlot c := by
        intro he
        subst s
        rw [hhole] at hs
        contradiction
      exact ih s t (by simpa [refine, hne] using hs)

/-- Every completion of a frontier node is either within the weighted bound
    or belongs to one of its explicit open leaves. The halt branch is
    charged exactly, including the final halting query and incoming zero
    prefix; ordinary branches are exhaustive over Move. -/
theorem RootedFrontier.sound {B : Nat} {p : PartialMachine}
    (f : RootedFrontier B p) :
    ∀ m, compatible p m →
      WeightedBound B m ∨
        ∃ address q, OpenLeaf f address q ∧ compatible q m := by
  induction f with
  | open path =>
      intro m hm
      exact Or.inr ⟨[], p, OpenLeaf.here path, hm⟩
  | closed path cert =>
      intro m hm
      exact Or.inl (cert.sound m hm)
  | expand path hrun hhole hweight children ih =>
      intro m hm
      cases hstep : m (readSlot c) with
      | none =>
          have hcomp : compatible (refine p (readSlot c) none) m := by
            intro s t h
            by_cases he : s = readSlot c
            · subst s
              have ht : t = none := by simpa [refine] using h
              simpa [ht] using hstep
            · exact hm s t (by simpa [refine, he] using h)
          exact Or.inl (first_hole_weighted_halt B p n c
            (RawRootPath.rootRow path) hrun hhole hweight m hcomp)
      | some mv =>
          have hcomp : compatible (refine p (readSlot c) (some mv)) m := by
            intro s t h
            by_cases he : s = readSlot c
            · subst s
              have ht : t = some mv := by simpa [refine] using h
              simpa [ht] using hstep
            · exact hm s t (by simpa [refine, he] using h)
          rcases ih mv m hcomp with hgood | ⟨address, q, hopen, hq⟩
          · exact Or.inl hgood
          · exact Or.inr ⟨mv :: address, q,
              OpenLeaf.child path hrun hhole hweight children mv hopen, hq⟩

/-- Distinct open leaves are incompatible. At the first differing edge they
    assign different instructions to the same first-hole slot. -/
theorem RootedFrontier.openLeaves_disjoint {B : Nat} {p : PartialMachine}
    (f : RootedFrontier B p) :
    ∀ address1 q1 address2 q2,
      OpenLeaf f address1 q1 →
      OpenLeaf f address2 q2 →
      (address1, q1) ≠ (address2, q2) →
      ∀ m, ¬ (compatible q1 m ∧ compatible q2 m) := by
  induction f with
  | open path =>
      intro address1 q1 address2 q2 h1 h2 hne m hcomp
      cases h1
      cases h2
      exact hne rfl
  | closed path cert =>
      intro address1 q1 address2 q2 h1
      cases h1
  | expand path hrun hhole hweight children ih =>
      intro address1 q1 address2 q2 h1 h2 hne m hcomp
      cases h1 with
      | child path hrun hhole hweight children mv1 hchild1 =>
        cases h2 with
        | child path hrun hhole hweight children mv2 hchild2 =>
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

/-- Add the exact incoming-delay check to every edge of the existing
    nine-step authentic first-hole path. -/
def pathOK84 (p : PartialMachine) (cut : Nat) : List PathEntry → Bool
  | [] => true
  | (n, s, mv) :: xs =>
      decide (p s = none) &&
      decide ((knownRun p n).map readSlot = some s) &&
      decide (s.1.val < cut) &&
      decide (mv.next.val ≤ cut) &&
      weightOK p s n 84 &&
      pathOK84 (refine p s (some mv)) (advanceCut cut mv) xs

theorem pathOK84_root : pathOK84 root 2 path = true := by decide

/-- Turn a validated first-hole path into a complete prefix tree: at each
    path node the selected edge continues, while all 23 other ordinary
    instructions are retained as explicit open siblings. -/
def buildFrontier (p : PartialMachine) (cut : Nat) (hp : RawRootPath p) :
    (xs : List PathEntry) →
    pathOK84 p cut xs = true →
    WeightedTNFCertificate 84 (pathEnd p cut xs).1 6 →
    RootedFrontier 84 p
  | [], _, cert => .closed hp cert
  | (n, s, mv) :: xs, h, cert => by
      simp only [pathOK84, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨hhole, hread, hslot, hmove, hweight, htail⟩
      cases hr : knownRun p n with
      | none => simp [hr] at hread
      | some c =>
          have hs : readSlot c = s := by simpa [hr] using hread
          subst s
          have hw : ∀ d ∈ possibleDelays (refine p (readSlot c) none) 0,
              d + n + 1 ≤ 84 :=
            weightOK_sound p (readSlot c) n 84 hweight
          exact .expand hp hr hhole hw (fun actual =>
            if heq : actual = mv then
              by
                subst actual
                exact buildFrontier (refine p (readSlot c) (some mv))
                  (advanceCut cut mv) (RawRootPath.step hp hr hhole mv) xs htail cert
            else
              .open (RawRootPath.step hp hr hhole actual))

/-- The nine-edge Agent 50 pilot, now with every ancestor sibling retained. -/
def rootFrontier : RootedFrontier 84 root :=
  buildFrontier root 2 RawRootPath.root path pathOK84_root certificate

theorem rootFrontier_sound :
    ∀ m, compatible root m →
      WeightedBound 84 m ∨
        ∃ entry ∈ residuals rootFrontier, compatible entry.2 m := by
  intro m hm
  rcases RootedFrontier.sound rootFrontier m hm with hgood | ⟨address, q, hopen, hq⟩
  · exact Or.inl hgood
  · exact Or.inr ⟨(address, q), OpenLeaf.mem hopen, hq⟩

theorem rootFrontier_residual_count :
    (residuals rootFrontier).length = 207 := by decide

theorem rootFrontier_openLeaves_disjoint :
    ∀ address1 q1 address2 q2,
      OpenLeaf rootFrontier address1 q1 →
      OpenLeaf rootFrontier address2 q2 →
      (address1, q1) ≠ (address2, q2) →
      ∀ m, ¬ (compatible q1 m ∧ compatible q2 m) :=
  RootedFrontier.openLeaves_disjoint rootFrontier

theorem rootFrontier_openLeaves_reachable {address q}
    (h : OpenLeaf rootFrontier address q) : RawRootPath q := by
  induction h with
  | here hp => exact hp
  | child path hrun hhole hweight children mv hchild ih => exact ih

/-- Machine-readable transition encoding: ? is unassigned, H is an
    assigned halt, and an ordinary transition is e.g. 1RB. -/
def encodeMove (mv : Move) : String :=
  (if mv.write then "1" else "0") ++
  (if mv.right then "R" else "L") ++ toString mv.next.val

def encodeTransition : Option (Option Move) → String
  | none => "?"
  | some none => "H"
  | some (some mv) => encodeMove mv

def encodeTable (p : PartialMachine) : String :=
  String.intercalate "_" ((List.finRange 6).flatMap fun q =>
    [false, true].map fun b => encodeTransition (p (q, b)))

def encodeAddress (address : List Move) : String :=
  String.intercalate "/" (address.map encodeMove)

/-- Deterministic export of every residual branch address and all twelve
    slots of its exact partial table. -/
def residualManifest : List (String × String) :=
  (residuals rootFrontier).map fun (address, p) =>
    (encodeAddress address, encodeTable p)

theorem residualManifest_length : residualManifest.length = 207 := by decide

#print axioms RootedFrontier.sound
#print axioms RootedFrontier.openLeaves_disjoint
#print axioms rootFrontier_sound
#print axioms rootFrontier_residual_count
#print axioms residualManifest_length

end BB6.Agent50RootFrontier
