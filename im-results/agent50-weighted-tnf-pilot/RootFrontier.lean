import TNFPilot
import SideCycle
import AlternatingResidualSweep
import AlternatingVariants

set_option maxRecDepth 24000
set_option maxHeartbeats 0

namespace BB6.Agent50RootFrontier
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath BB6.Agent50TNFPilot
open BB6Coverage.Agent50SideCycle

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
  | @step p n c mv parent hrun hhole ih =>
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
  unfold allMoves
  apply List.mem_flatMap.mpr
  refine ⟨q, hq, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨w, hw, ?_⟩
  apply List.mem_map.mpr
  exact ⟨r, hr, rfl⟩

theorem allMoves_length : allMoves.length = 24 := by decide

/-- A rooted frontier has three kinds of leaves:
    * open: an explicit residual cylinder, with its blank-root path;
    * closed: a previously checked weighted certificate;
    * expand: all 24 ordinary instructions are retained, while the
      first-hole halt child is discharged by its exact incoming-delay bound.

    There is no fresh-state quotient in this structure: concrete labels are
    retained, so its residual manifest can be compared slot-for-slot. -/
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

/-- A leaf address records the exact ordinary instructions taken from the
    root to an open residual cylinder. -/
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

/-- Flatten a frontier to exact path-address/table pairs. The recursive
    order is deterministic and follows allMoves. -/
def residuals {B : Nat} {p : PartialMachine} :
    RootedFrontier B p → List (List Move × PartialMachine)
  | .residual _ => [([], p)]
  | .closed _ _ => []
  | .expand _ _ _ _ children =>
      allMoves.flatMap fun mv =>
        (residuals (children mv)).map fun (address, q) => (mv :: address, q)

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
      have hchild : (refine p (readSlot c) (some mv)) s = some t := by
        simp [refine, hne, hs]
      exact ih s t hchild

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
              have ht : t = none := by simpa [refine] using h.symm
              simpa [ht] using hstep
            · exact hm s t (by simpa [refine, he] using h)
          exact Or.inl (first_hole_weighted_halt B p n c
            (RawRootPath.rootRow path) hrun hhole hweight m hcomp)
      | some mv =>
          have hcomp : compatible (refine p (readSlot c) (some mv)) m := by
            intro s t h
            by_cases he : s = readSlot c
            · subst s
              have ht : t = some mv := by simpa [refine] using h.symm
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

def extractRunConfig {p : PartialMachine} {n : Nat} {s : Slot}
    (h : (knownRun p n).map readSlot = some s) :
    {c // knownRun p n = some c} :=
  match hr : knownRun p n with
  | none => False.elim (by simp [hr] at h)
  | some c => ⟨c, rfl⟩

theorem pathOK84_cons {p : PartialMachine} {cut n : Nat} {s : Slot}
    {mv : Move} {xs : List PathEntry}
    (h : pathOK84 p cut ((n, s, mv) :: xs) = true) :
    p s = none ∧
    (knownRun p n).map readSlot = some s ∧
    s.1.val < cut ∧ mv.next.val ≤ cut ∧
    weightOK p s n 84 = true ∧
    pathOK84 (refine p s (some mv)) (advanceCut cut mv) xs = true := by
  simpa only [pathOK84, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

theorem pathOK84_root : pathOK84 root 2 path = true := by decide

/-- Build the authenticated path and retain every off-path ordinary sibling. -/
def buildFrontier (p : PartialMachine) (cut : Nat) (hp : RawRootPath p) :
    (xs : List PathEntry) →
    pathOK84 p cut xs = true →
    WeightedTNFCertificate 84 (pathEnd p cut xs).1 6 →
    RootedFrontier 84 p
  | [], _, cert => .closed hp cert
  | (n, s, mv) :: xs, h, cert => by
      have hfields := pathOK84_cons h
      rcases hfields with ⟨hhole, hread, hslot, hmove, hweight, htail⟩
      let c := (extractRunConfig hread).val
      have hr : knownRun p n = some c := (extractRunConfig hread).property
      have hs : readSlot c = s := by
        have h' : (some c).map readSlot = some s := by simpa [hr] using hread
        simpa using h'
      have hhole' : p (readSlot c) = none := by
        simpa [hs] using hhole
      have hw : ∀ d ∈ possibleDelays (refine p (readSlot c) none) 0,
          d + n + 1 ≤ 84 := by
        simpa [hs.symm] using (weightOK_sound p s n 84 hweight)
      have htail' : pathOK84 (refine p (readSlot c) (some mv))
          (advanceCut cut mv) xs = true := by
        simpa [hs.symm] using htail
      have cert' : WeightedTNFCertificate 84
          (pathEnd (refine p (readSlot c) (some mv)) (advanceCut cut mv) xs).1 6 := by
        simpa [pathEnd, hs.symm] using cert
      exact .expand hp hr hhole' hw (fun actual =>
        if heq : actual = mv then
          by
            simpa [heq] using
              (buildFrontier (refine p (readSlot c) (some mv))
                (advanceCut cut mv) (RawRootPath.step (mv := mv) hp hr hhole') xs htail' cert')
        else
          .residual (RawRootPath.step (mv := actual) hp hr hhole'))

/-- The nine-edge Agent 50 pilot, now with every ancestor sibling retained. -/
def rootFrontier : RootedFrontier 84 root :=
  buildFrontier root 2 RawRootPath.root path pathOK84_root certificate

theorem rootFrontier_sound :
    ∀ m, compatible root m →
      WeightedBound 84 m ∨
        ∃ address q, OpenLeaf rootFrontier address q ∧ compatible q m :=
  RootedFrontier.sound rootFrontier

def pathResidualCount : List PathEntry → Nat
  | [] => 0
  | _ :: xs => 23 + pathResidualCount xs

theorem rootFrontier_residual_count : pathResidualCount path = 207 := by decide

theorem rootFrontier_openLeaves_disjoint :
    ∀ address1 q1 address2 q2,
      OpenLeaf rootFrontier address1 q1 →
      OpenLeaf rootFrontier address2 q2 →
      (address1, q1) ≠ (address2, q2) →
      ∀ m, ¬ (compatible q1 m ∧ compatible q2 m) :=
  RootedFrontier.openLeaves_disjoint rootFrontier

theorem OpenLeaf.reachable {B : Nat} {p : PartialMachine}
    {f : RootedFrontier B p} {address : List Move} {q : PartialMachine}
    (h : OpenLeaf f address q) : RawRootPath q := by
  induction h with
  | here hp => exact hp
  | child path hrun hhole hweight children mv hchild ih => exact ih

/-- The executable residual list contains every semantic open leaf. -/
theorem OpenLeaf.mem_residuals {B : Nat} {p : PartialMachine}
    {f : RootedFrontier B p} {address : List Move} {q : PartialMachine}
    (h : OpenLeaf f address q) : (address, q) ∈ residuals f := by
  induction h with
  | here path => simp [residuals]
  | child path hrun hhole hweight children mv hchild ih =>
      apply List.mem_flatMap.mpr
      refine ⟨mv, allMoves_complete mv, ?_⟩
      exact List.mem_map.mpr ⟨_, ih, rfl⟩

/-- Conversely no extraneous table/address occurs in the exported list. -/
theorem mem_residuals_openLeaf {B : Nat} {p : PartialMachine}
    (f : RootedFrontier B p) (address : List Move) (q : PartialMachine)
    (h : (address, q) ∈ residuals f) : OpenLeaf f address q := by
  induction f generalizing address q with
  | @residual p path =>
      have he : (address, q) = ([], p) := by simpa [residuals] using h
      cases he
      exact OpenLeaf.here path
  | closed path cert => simp [residuals] at h
  | @expand p n c path hrun hhole hweight children ih =>
      rcases List.mem_flatMap.mp h with ⟨mv, _, hm⟩
      rcases List.mem_map.mp hm with ⟨⟨a, t⟩, ha, he⟩
      have hchild := OpenLeaf.child path hrun hhole hweight children mv (ih mv a t ha)
      cases he
      exact hchild

theorem mem_residuals_iff {B : Nat} {p : PartialMachine}
    (f : RootedFrontier B p) (address : List Move) (q : PartialMachine) :
    (address, q) ∈ residuals f ↔ OpenLeaf f address q :=
  ⟨mem_residuals_openLeaf f address q, OpenLeaf.mem_residuals⟩

/-- A finite list of residual proofs suffices to close the entire frontier.
    This is the exact proof obligation for an enumerated residual manifest. -/
theorem RootedFrontier.sound_of_residuals {B : Nat} {p : PartialMachine}
    (f : RootedFrontier B p)
    (hres : ∀ address q, (address, q) ∈ residuals f →
      ∀ m, compatible q m → WeightedBound B m) :
    ∀ m, compatible p m → WeightedBound B m := by
  intro m hm
  rcases f.sound m hm with h | ⟨address, q, hopen, hq⟩
  · exact h
  · exact hres address q hopen.mem_residuals m hq

/-- Lossless finite table payload; None means an unassigned row, while
    some none is a fixed halt. The two must never be conflated in a manifest. -/
abbrev PackedTable := List (Option (Option Move))

def packTable (p : PartialMachine) : PackedTable :=
  [p (0,false), p (0,true), p (1,false), p (1,true),
   p (2,false), p (2,true), p (3,false), p (3,true),
   p (4,false), p (4,true), p (5,false), p (5,true)]

def unpackTable (rows : PackedTable) : PartialMachine := fun s =>
  (rows[2*s.1.val + (if s.2 then 1 else 0)]?).getD none

theorem unpack_packTable (p : PartialMachine) : unpackTable (packTable p) = p := by
  funext s
  rcases s with ⟨⟨n, hn⟩, b⟩
  have h : n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 := by omega
  rcases h with h | h | h | h | h | h <;> subst n <;> cases b <;> rfl

theorem packTable_injective {p q : PartialMachine} (h : packTable p = packTable q) : p = q := by
  have he := congrArg unpackTable h
  simpa only [unpack_packTable] using he

theorem packTable_length (p : PartialMachine) : (packTable p).length = 12 := rfl

abbrev PackedResidual := List Move × PackedTable

def packResiduals (xs : List (List Move × PartialMachine)) : List PackedResidual :=
  xs.map fun (a,p) => (a,packTable p)

theorem mem_packResiduals_iff (xs : List (List Move × PartialMachine))
    (a : List Move) (p : PartialMachine) :
    (a,packTable p) ∈ packResiduals xs ↔ (a,p) ∈ xs := by
  constructor
  · intro h
    rcases List.mem_map.mp h with ⟨⟨a',p'⟩,hm,he⟩
    have ha : a' = a := congrArg Prod.fst he
    have hp : p' = p := packTable_injective (congrArg Prod.snd he)
    subst a'
    subst p'
    exact hm
  · intro h
    exact List.mem_map.mpr ⟨(a,p),h,rfl⟩

/-- Exact finite-data equality suffices to consume independently exported
    residual certificates. No string parsing or hash equality is trusted. -/
theorem RootedFrontier.sound_of_packed_residuals {B : Nat} {p : PartialMachine}
    (f : RootedFrontier B p) (roster : List PackedResidual)
    (hexact : packResiduals (residuals f) = roster)
    (hres : ∀ e ∈ roster, ∀ m, compatible (unpackTable e.2) m → WeightedBound B m) :
    ∀ m, compatible p m → WeightedBound B m := by
  apply f.sound_of_residuals
  intro a q hq m hm
  have hp : (a,packTable q) ∈ roster := by
    rw [← hexact]
    exact (mem_packResiduals_iff (residuals f) a q).mpr hq
  exact hres (a,packTable q) hp m (by simpa only [unpack_packTable] using hm)

/-- Machine-readable transition encoding: ? is unassigned, H is an
    assigned halt, and an ordinary transition is e.g. 1RB. -/
def encodeState (q : Fin 6) : String :=
  match q.val with
  | 0 => "A"
  | 1 => "B"
  | 2 => "C"
  | 3 => "D"
  | 4 => "E"
  | _ => "F"

def encodeMove (mv : Move) : String :=
  (if mv.write then "1" else "0") ++
  (if mv.right then "R" else "L") ++ encodeState mv.next

def encodeTransition : Option (Option Move) → String
  | none => "---"
  | some none => "HALT"
  | some (some mv) => encodeMove mv

def encodeTable (p : PartialMachine) : String :=
  String.intercalate "_" ((List.finRange 6).map fun q =>
    encodeTransition (p (q, false)) ++ encodeTransition (p (q, true)))

def encodeAddress (address : List Move) : String :=
  String.intercalate "/" (address.map encodeMove)

/-- Deterministic export of every residual branch address and all twelve
    slots of its exact partial table. -/
def residualManifest : List (String × String) :=
  (residuals rootFrontier).map fun (address, p) =>
    (encodeAddress address, encodeTable p)



#print axioms RootedFrontier.sound
#print axioms RootedFrontier.openLeaves_disjoint
#print axioms rootFrontier_sound
#print axioms rootFrontier_residual_count
#print axioms mem_residuals_iff
#print axioms RootedFrontier.sound_of_residuals
#print axioms unpack_packTable
#print axioms packTable_injective
#print axioms mem_packResiduals_iff
#print axioms RootedFrontier.sound_of_packed_residuals

/-- A proof-free enumeration of the off-path residuals. The selected branch
    continues recursively; all other ordinary moves are retained. -/
def pathResiduals (p : PartialMachine) : List PathEntry → List (List Move × PartialMachine)
  | [] => []
  | (_,s,mv)::xs =>
      allMoves.flatMap fun actual =>
        if actual = mv then
          (pathResiduals (refine p s (some mv)) xs).map fun (a,q) => (actual::a,q)
        else [([actual], refine p s (some actual))]

/-- Every completion is either bounded or contained in a table from the
    executable off-path roster. No evaluation of proof constructors is used. -/
theorem pathResiduals_sound (p : PartialMachine) (cut : Nat) (xs : List PathEntry)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (hpath : pathOK84 p cut xs = true)
    (hend : ∀ m, compatible (pathEnd p cut xs).1 m → WeightedBound 84 m) :
    ∀ m, compatible p m → WeightedBound 84 m ∨
      ∃ a q, (a,q) ∈ pathResiduals p xs ∧ compatible q m := by
  induction xs generalizing p cut with
  | nil => intro m hm; exact Or.inl (hend m hm)
  | cons x xs ih =>
    rcases x with ⟨n,s,mv⟩
    obtain ⟨hhole,hread,_,_,hw,htail⟩ := pathOK84_cons hpath
    intro m hm
    have href (v : Option Move) (hv : m s = v) : compatible (refine p s v) m := by
      intro t u hu
      by_cases he : t = s
      · subst t
        have h : u = v := by simpa [refine] using hu.symm
        simpa [h] using hv
      · exact hm t u (by simpa [refine,he] using hu)
    cases ha : m s with
    | none =>
      cases hr : knownRun p n with
      | none => simp [hr] at hread
      | some c =>
        have hs : readSlot c = s := by simpa [hr] using hread
        exact Or.inl (first_hole_weighted_halt 84 p n c hroot hr
          (by simpa [hs] using hhole)
          (by simpa [hs] using weightOK_sound p s n 84 hw)
          m (by simpa [hs] using href none ha))
    | some actual =>
      by_cases he : actual = mv
      · subst actual
        have hroot' := refine_preserves_firstOne p s (some mv) hhole hroot
        rcases ih _ _ hroot' htail hend m (href (some mv) ha) with hb | ⟨a,q,hmem,hcomp⟩
        · exact Or.inl hb
        · apply Or.inr
          refine ⟨mv::a,q,?_,hcomp⟩
          apply List.mem_flatMap.mpr
          refine ⟨mv,allMoves_complete mv,?_⟩
          simp only [if_pos rfl]
          exact List.mem_map.mpr ⟨(a,q),hmem,rfl⟩
      · apply Or.inr
        refine ⟨[actual],refine p s (some actual),?_,href (some actual) ha⟩
        apply List.mem_flatMap.mpr
        refine ⟨actual,allMoves_complete actual,?_⟩
        simp [he]

def executableRootRoster : List PackedResidual :=
  packResiduals (pathResiduals root path)

theorem executableRootRoster_count : executableRootRoster.length = 207 := by decide

theorem executableRootRoster_sound :
    ∀ m, compatible root m → WeightedBound 84 m ∨
      ∃ e ∈ executableRootRoster, compatible (unpackTable e.2) m := by
  intro m hm
  rcases pathResiduals_sound root 2 path rfl pathOK84_root
      all_completions_weighted m hm with h | ⟨a,q,hmem,hcomp⟩
  · exact Or.inl h
  · apply Or.inr
    refine ⟨(a,packTable q),?_,?_⟩
    · exact (mem_packResiduals_iff _ _ _).mpr hmem
    · simpa only [unpack_packTable] using hcomp

#print axioms pathResiduals_sound
#print axioms executableRootRoster_count
#print axioms executableRootRoster_sound

/-- Finite nonhalting witnesses for off-path cylinders. The lookup indices
    are only candidate data: every chosen sparse table is checked again. -/
inductive ResidualNonhaltWitness where
  | ray (n : Nat) (right : Bool) (mask : Nat)
  | lasso (n : Nat)
  | side (entry period : Nat) (right : Bool) (boundary : Int)
  | alternating (w : Bool)

def residualMask (mask : Nat) (q : Fin 6) : Bool := mask.testBit q.val

def residualWitnessOK (p : PartialMachine) : ResidualNonhaltWitness → Bool
  | .ray n right mask => finiteRayCheck p n right (residualMask mask)
  | .lasso n => finiteLassoCheck p n
  | .side entry period right boundary =>
      decide (0 < period) && finiteSideCycleCheck p entry period right boundary
  | .alternating w => decide (packTable p = packTable (BB6Coverage.Agent50AlternatingSweep.table w))

theorem residualWitnessOK_sound (p : PartialMachine) (w : ResidualNonhaltWitness)
    (h : residualWitnessOK p w = true) :
    ∀ m, compatible p m → NeverHalts m := by
  cases w with
  | ray n right mask =>
    exact zeroCover_never (finiteRayCheck_sound p n right (residualMask mask) 0 h)
  | lasso n =>
    exact zeroCover_never (finiteLassoCheck_sound p n 0 h)
  | side entry period right boundary =>
    have hc : 0 < period ∧ finiteSideCycleCheck p entry period right boundary = true := by
      simpa only [residualWitnessOK, Bool.and_eq_true, decide_eq_true_eq] using h
    exact finiteSideCycleCheck_sound p entry period right boundary hc.1 hc.2
  | alternating w =>
    have hc : packTable p = packTable (BB6Coverage.Agent50AlternatingSweep.table w) := by
      simpa only [residualWitnessOK,decide_eq_true_eq] using h
    rw [packTable_injective hc]
    exact BB6Coverage.Agent50AlternatingSweep.never w

def residualWitnessIndices : List (Nat × ResidualNonhaltWitness) :=
  [(1,.ray 0 true 3), (3,.ray 0 true 3), (5,.ray 0 true 3), (7,.ray 0 true 3),
   (12,.ray 0 true 7), (14,.ray 0 true 7), (16,.ray 0 true 7), (18,.ray 0 true 7),
   (20,.ray 0 true 7), (22,.ray 0 true 7), (25,.ray 0 true 15), (27,.ray 0 true 15),
   (29,.ray 0 true 15), (31,.ray 0 true 15), (32,.lasso 4), (33,.ray 0 true 15),
   (35,.ray 0 true 15), (37,.ray 0 true 15), (50,.ray 7 false 8), (51,.ray 17 false 8),
   (52,.ray 7 false 8), (74,.ray 13 false 8), (75,.ray 11 false 8), (76,.lasso 8),
   (93,.lasso 22), (113,.ray 15 false 8), (135,.lasso 9), (136,.ray 10 false 8),
   (140,.ray 9 false 8), (142,.ray 9 false 8), (162,.lasso 7), (176,.ray 0 true 15),
   (24,.side 0 4 true (0)),
   (28,.side 1 3 true (1)),
   (53,.side 6 3 true (2)),
   (62,.side 0 10 true (0)),
   (64,.side 0 10 true (0)),
   (65,.side 8 7 false (1)),
   (84,.side 0 18 true (-1)),
   (87,.side 7 5 false (1)),
   (94,.side 22 7 false (2)),
   (96,.side 10 13 true (0)),
   (97,.side 11 11 true (1)),
   (98,.side 34 5 false (0)),
   (99,.side 11 11 true (1)),
   (104,.side 1 38 true (-1)),
   (105,.side 20 17 false (4)),
   (111,.side 7 5 false (1)),
   (118,.side 3 9 false (3)),
   (119,.side 5 7 false (2)),
   (130,.side 7 3 false (1)), (92,.alternating false), (102,.alternating true)]

def residualWitnessRoster : List (PackedTable × ResidualNonhaltWitness) :=
  residualWitnessIndices.filterMap fun (i,w) =>
    executableRootRoster[i]?.map fun e => (e.2,w)

theorem residualWitnessRoster_count : residualWitnessRoster.length = 53 := by decide

theorem residualWitnessRoster_checked :
    residualWitnessRoster.all (fun (t,w) => residualWitnessOK (unpackTable t) w) = true := by
  decide

def residualHasWitness (t : PackedTable) : Bool :=
  residualWitnessRoster.any fun e => decide (e.1 = t)

theorem residualHasWitness_sound (t : PackedTable) (h : residualHasWitness t = true) :
    ∀ m, compatible (unpackTable t) m → WeightedBound 84 m := by
  obtain ⟨⟨u,w⟩,hmem,heq⟩ := List.any_eq_true.mp h
  have he : u = t := of_decide_eq_true heq
  subst u
  have hc := List.all_eq_true.mp residualWitnessRoster_checked (t,w) hmem
  intro m hm
  exact weighted_never 84 m (residualWitnessOK_sound (unpackTable t) w hc m hm)

def remainingRootRoster : List PackedResidual :=
  executableRootRoster.filter fun e => !residualHasWitness e.2

theorem remainingRootRoster_count : remainingRootRoster.length = 154 := by decide

/-- The executable residual count decreases from 207 to 154 only by
    removing cylinders proved nonhalting for every compatible completion. -/
theorem remainingRootRoster_sound :
    ∀ m, compatible root m → WeightedBound 84 m ∨
      ∃ e ∈ remainingRootRoster, compatible (unpackTable e.2) m := by
  intro m hm
  rcases executableRootRoster_sound m hm with hb | ⟨e,hmem,hcomp⟩
  · exact Or.inl hb
  · cases he : residualHasWitness e.2 with
    | true => exact Or.inl (residualHasWitness_sound e.2 he m hcomp)
    | false =>
      exact Or.inr ⟨e,List.mem_filter.mpr ⟨hmem,by simp [he]⟩,hcomp⟩

#print axioms residualWitnessRoster_checked
#print axioms residualWitnessRoster_count
#print axioms remainingRootRoster_count
#print axioms remainingRootRoster_sound

/-- Last-hole or directional-cycle certificates for the ordinary children
    of a two-hole residual. All 24 moves are checked, and the halt sibling
    is charged separately. -/
def lastCert92 (p : PartialMachine) (n : Nat) (hole : Slot)
    (hf : p initialSlot = some (some ⟨true,true,1⟩))
    (hread : (knownRun p n).map readSlot = some hole)
    (hh : p hole = none) (hrest : restOK p hole = true)
    (hw : weightOK p hole n 92 = true) :
    WeightedTNFCertificate 92 p 6 := by
  cases hr : knownRun p n with
  | none => simp [hr] at hread
  | some c =>
    have hs : readSlot c = hole := by simpa [hr] using hread
    exact .lastHole hf (support6 p) (by decide) hr
      (by simpa [hs] using hh)
      (by simpa [hs] using restOK_sound p hole hrest)
      (by simpa [hs] using weightOK_sound p hole n 92 hw)

inductive DeepChildWitness where
  | last (n : Nat) (s : Slot)
  | side (entry period : Nat) (right : Bool) (boundary : Int)
  | alternating (i : Fin 17)

def deepChildOK (p : PartialMachine) : DeepChildWitness → Bool
  | .last n s =>
      decide ((knownRun p n).map readSlot = some s) &&
      (decide (p s = none) && (restOK p s && weightOK p s n 92))
  | .side entry period right boundary =>
      decide (0 < period) && finiteSideCycleCheck p entry period right boundary
  | .alternating i => decide (packTable p = packTable (BB6Coverage.Agent50AlternatingVariants.vt i))

theorem deepChildOK_sound (p : PartialMachine) (w : DeepChildWitness)
    (hroot : p initialSlot = some (some ⟨true,true,1⟩))
    (h : deepChildOK p w = true) : ∀ m, compatible p m → WeightedBound 92 m := by
  cases w with
  | last n s =>
    have hh : (knownRun p n).map readSlot = some s ∧ p s = none ∧
        restOK p s = true ∧ weightOK p s n 92 = true := by
      simpa only [deepChildOK, Bool.and_eq_true, decide_eq_true_eq] using h
    exact (lastCert92 p n s hroot hh.1 hh.2.1 hh.2.2.1 hh.2.2.2).sound
  | side entry period right boundary =>
    have hh : 0 < period ∧ finiteSideCycleCheck p entry period right boundary = true := by
      simpa only [deepChildOK, Bool.and_eq_true, decide_eq_true_eq] using h
    intro m hm
    exact weighted_never 92 m (finiteSideCycleCheck_sound p entry period right boundary hh.1 hh.2 m hm)
  | alternating i =>
    have he : packTable p = packTable (BB6Coverage.Agent50AlternatingVariants.vt i) := by
      simpa only [deepChildOK, decide_eq_true_eq] using h
    have hp := packTable_injective he
    subst p
    intro m hm
    exact weighted_never 92 m (BB6Coverage.Agent50AlternatingVariants.never i m hm)

structure DeepSiblingWitness where
  n : Nat
  slot : Slot
  children : List DeepChildWitness

def deepSiblingOK (p : PartialMachine) (w : DeepSiblingWitness) : Bool :=
  decide (p initialSlot = some (some ⟨true,true,1⟩)) &&
  (decide ((knownRun p w.n).map readSlot = some w.slot) &&
  (decide (p w.slot = none) && (weightOK p w.slot w.n 92 &&
   allMoves.all fun mv => (allMoves.zip w.children).any fun e =>
     decide (e.1 = mv) && deepChildOK (refine p w.slot (some e.1)) e.2)))

theorem deepSiblingOK_sound (p : PartialMachine) (w : DeepSiblingWitness)
    (h : deepSiblingOK p w = true) : ∀ m, compatible p m → WeightedBound 92 m := by
  have hh : p initialSlot = some (some ⟨true,true,1⟩) ∧
      (knownRun p w.n).map readSlot = some w.slot ∧ p w.slot = none ∧
      weightOK p w.slot w.n 92 = true ∧
      (allMoves.all fun mv => (allMoves.zip w.children).any fun e =>
        decide (e.1 = mv) && deepChildOK (refine p w.slot (some e.1)) e.2) = true := by
    simpa only [deepSiblingOK, Bool.and_eq_true, decide_eq_true_eq] using h
  obtain ⟨hroot,hread,hhole,hw,hchildren⟩ := hh
  intro m hm
  have href (v : Option Move) (hv : m w.slot = v) : compatible (refine p w.slot v) m := by
    intro t u hu
    by_cases he : t = w.slot
    · subst t
      have h : u = v := by simpa [refine] using hu.symm
      simpa [h] using hv
    · exact hm t u (by simpa [refine,he] using hu)
  cases ha : m w.slot with
  | none =>
    cases hr : knownRun p w.n with
    | none => simp [hr] at hread
    | some c =>
      have hs : readSlot c = w.slot := by simpa [hr] using hread
      exact first_hole_weighted_halt 92 p w.n c hroot hr
        (by simpa [hs] using hhole)
        (by simpa [hs] using weightOK_sound p w.slot w.n 92 hw)
        m (by simpa [hs] using href none ha)
  | some mv =>
    obtain ⟨⟨v,cw⟩,_,hc⟩ := List.any_eq_true.mp
      (List.all_eq_true.mp hchildren mv (allMoves_complete mv))
    have hpair : v = mv ∧ deepChildOK (refine p w.slot (some v)) cw = true := by
      simpa only [Bool.and_eq_true,decide_eq_true_eq] using hc
    obtain ⟨he,hcheck⟩ := hpair
    subst v
    exact deepChildOK_sound (refine p w.slot (some mv)) cw
      (refine_preserves_firstOne p w.slot (some mv) hhole hroot) hcheck m (href (some mv) ha)

def deepSiblingIndices : List (Nat × DeepSiblingWitness) := [
  (101,⟨23,(4,false),[
    .last 24 (0,true),
    .last 24 (0,true),
    .last 24 (0,true),
    .last 24 (0,true),
    .side 20 4 true (3),
    .side 14 14 true (3),
    .side 18 8 true (3),
    .last 26 (0,true),
    .side 11 13 true (1),
    .side 13 11 true (3),
    .side 29 5 true (4),
    .side 13 11 true (3),
    .side 22 2 true (4),
    .side 16 10 true (3),
    .side 18 6 true (3),
    .last 31 (0,true),
    .side 1 42 true (-1),
    .side 1 24 true (-1),
    .side 31 5 true (4),
    .side 12 16 true (2),
    .last 40 (0,true),
    .last 34 (0,true),
    .side 12 22 true (2),
    .last 25 (0,true)]⟩),
  (103,⟨23,(4,false),[
    .last 24 (0,true),
    .last 24 (0,true),
    .last 24 (0,true),
    .last 24 (0,true),
    .last 26 (0,true),
    .side 14 14 true (3),
    .last 26 (0,true),
    .last 26 (0,true),
    .side 11 13 true (1),
    .side 13 11 true (3),
    .last 31 (0,true),
    .side 13 11 true (3),
    .side 22 2 true (4),
    .side 16 10 true (3),
    .last 28 (0,true),
    .last 31 (0,true),
    .side 1 34 true (-1),
    .last 33 (0,true),
    .side 6 30 true (-1),
    .last 27 (0,true),
    .last 25 (0,true),
    .last 34 (0,true),
    .last 25 (0,true),
    .last 25 (0,true)]⟩),
  (106,⟨31,(4,false),[
    .last 32 (0,true),
    .side 0 32 true (-1),
    .last 32 (0,true),
    .last 41 (0,true),
    .last 51 (0,true),
    .side 14 18 true (1),
    .side 6 28 true (-1),
    .last 40 (0,true),
    .last 61 (0,true),
    .last 69 (0,true),
    .last 55 (0,true),
    .side 2 30 true (-1),
    .side 30 2 true (6),
    .side 16 16 true (1),
    .last 53 (0,true),
    .last 51 (0,true),
    .side 1 32 true (-1),
    .side 31 1 true (7),
    .side 28 5 true (4),
    .side 31 1 true (7),
    .last 42 (0,true),
    .side 31 2 true (7),
    .last 47 (0,true),
    .side 31 2 true (7)]⟩),
  (107,⟨27,(4,false),[
    .last 28 (0,true),
    .last 28 (0,true),
    .last 28 (0,true),
    .last 28 (0,true),
    .last 31 (0,true),
    .side 14 22 true (1),
    .last 31 (0,true),
    .last 30 (0,true),
    .side 11 17 true (1),
    .last 48 (0,true),
    .last 33 (0,true),
    .last 38 (0,true),
    .side 26 2 true (4),
    .side 16 14 true (1),
    .last 33 (0,true),
    .last 35 (0,true),
    .last 37 (0,true),
    .side 1 28 true (-1),
    .last 36 (0,true),
    .last 43 (0,true),
    .last 44 (0,true),
    .last 38 (0,true),
    .last 35 (0,true),
    .last 29 (0,true)]⟩),
  (108,⟨27,(4,false),[
    .last 28 (0,true),
    .side 0 28 true (-1),
    .last 28 (0,true),
    .last 37 (0,true),
    .last 40 (0,true),
    .side 14 14 true (3),
    .side 12 20 true (2),
    .last 36 (0,true),
    .side 13 15 true (3),
    .last 54 (0,true),
    .side 0 32 true (-1),
    .side 2 26 true (-1),
    .side 26 2 true (6),
    .side 16 12 true (3),
    .last 42 (0,true),
    .side 12 22 true (2),
    .last 37 (0,true),
    .side 27 1 true (7),
    .side 24 5 true (4),
    .side 27 1 true (7),
    .last 38 (0,true),
    .side 28 1 true (8),
    .side 12 18 true (2),
    .side 28 1 true (8)]⟩),
  (109,⟨29,(0,true),[
    .side 20 64 false (4),
    .side 22 10 true (1),
    .side 20 30 false (4),
    .side 28 4 true (1),
    .side 18 19 false (5),
    .side 20 12 true (1),
    .side 54 1 false (-4),
    .side 24 6 true (1),
    .side 61 1 false (-1),
    .side 42 1 false (0),
    .last 43 (4,false),
    .side 40 13 false (2),
    .last 31 (4,false),
    .side 20 21 false (4),
    .side 18 21 false (5),
    .side 40 1 false (-2),
    .side 32 1 false (-2),
    .last 30 (4,false),
    .side 32 1 false (-2),
    .last 30 (4,false),
    .side 32 1 false (-2),
    .side 34 1 false (0),
    .side 32 1 false (-2),
    .side 33 9 false (1)]⟩),
  (88,⟨22,(0,true),[
    .last 27 (4,false),
    .side 7 17 true (-1),
    .side 26 10 false (0),
    .side 22 4 true (2),
    .side 20 25 false (4),
    .side 10 13 true (0),
    .side 10 15 true (0),
    .side 10 13 true (0),
    .alternating 0,
    .last 25 (4,false),
    .last 25 (4,false),
    .last 25 (4,false),
    .last 41 (4,false),
    .side 20 15 false (4),
    .alternating 1,
    .alternating 2,
    .last 23 (4,false),
    .last 23 (4,false),
    .last 23 (4,false),
    .last 23 (4,false),
    .last 43 (4,false),
    .side 9 15 true (-1),
    .alternating 3,
    .side 21 2 true (2)]⟩),
  (89,⟨22,(0,true),[
    .last 27 (4,false),
    .side 12 15 true (2),
    .side 26 14 false (2),
    .side 22 4 true (4),
    .side 1 38 true (-1),
    .side 12 11 true (2),
    .side 10 13 true (0),
    .side 12 11 true (2),
    .alternating 4,
    .last 25 (4,false),
    .last 25 (4,false),
    .last 25 (4,false),
    .side 23 17 false (3),
    .side 23 29 false (5),
    .alternating 5,
    .side 17 6 true (3),
    .last 23 (4,false),
    .last 23 (4,false),
    .last 23 (4,false),
    .last 23 (4,false),
    .side 12 13 true (2),
    .side 0 26 true (-1),
    .side 21 2 true (3),
    .side 0 26 true (-1)]⟩),
  (90,⟨22,(0,true),[
    .side 20 64 false (4),
    .side 12 17 true (2),
    .side 26 10 false (0),
    .side 24 4 true (4),
    .side 20 17 false (4),
    .side 42 14 false (2),
    .side 28 11 false (1),
    .side 26 8 true (1),
    .side 20 15 false (4),
    .side 54 21 false (2),
    .side 26 12 false (2),
    .side 20 4 true (2),
    .side 18 15 false (5),
    .side 33 18 false (0),
    .side 20 13 false (4),
    .last 33 (4,false),
    .last 23 (4,false),
    .last 27 (4,false),
    .last 23 (4,false),
    .alternating 6,
    .last 30 (4,false),
    .side 8 15 true (-1),
    .side 23 7 false (1),
    .side 21 4 true (2)]⟩),
  (91,⟨22,(0,true),[
    .side 20 30 false (4),
    .side 12 15 true (2),
    .side 28 12 false (0),
    .side 22 4 true (4),
    .last 31 (4,false),
    .side 12 11 true (2),
    .side 62 3 false (-2),
    .side 12 11 true (2),
    .last 27 (4,false),
    .last 25 (4,false),
    .side 20 4 true (3),
    .last 25 (4,false),
    .last 24 (4,false),
    .side 3 34 true (-1),
    .last 33 (4,false),
    .alternating 7,
    .side 23 15 false (3),
    .last 23 (4,false),
    .alternating 8,
    .last 23 (4,false),
    .last 91 (4,false),
    .side 21 15 true (3),
    .alternating 9,
    .side 21 15 true (3)]⟩),
  (95,⟨24,(0,true),[
    .last 29 (4,false),
    .side 7 19 true (-1),
    .side 26 12 false (2),
    .side 22 4 true (2),
    .side 20 29 false (4),
    .side 10 15 true (0),
    .side 10 17 true (0),
    .side 10 15 true (0),
    .alternating 10,
    .last 27 (4,false),
    .last 27 (4,false),
    .last 27 (4,false),
    .last 45 (4,false),
    .side 20 17 false (4),
    .alternating 11,
    .alternating 12,
    .last 25 (4,false),
    .last 25 (4,false),
    .last 25 (4,false),
    .last 25 (4,false),
    .last 29 (4,false),
    .side 7 19 true (-1),
    .alternating 13,
    .side 21 4 true (2)]⟩),
  (100,⟨23,(4,false),[
    .last 24 (0,true),
    .last 24 (0,true),
    .last 24 (0,true),
    .last 24 (0,true),
    .alternating 14,
    .side 20 4 true (2),
    .side 24 9 false (2),
    .last 26 (0,true),
    .side 10 15 true (0),
    .side 11 13 true (1),
    .side 18 19 false (5),
    .side 11 13 true (1),
    .side 22 2 true (2),
    .side 16 12 true (2),
    .alternating 15,
    .last 33 (0,true),
    .last 33 (0,true),
    .side 1 42 true (-1),
    .side 20 21 false (4),
    .side 33 1 true (7),
    .last 46 (0,true),
    .last 48 (0,true),
    .last 33 (0,true),
    .last 25 (0,true)]⟩),
  (110,⟨23,(0,true),[
    .side 20 30 false (4),
    .side 12 13 true (2),
    .side 28 12 false (0),
    .side 12 13 true (2),
    .side 24 15 false (3),
    .last 27 (4,false),
    .side 24 9 false (2),
    .last 27 (4,false),
    .side 98 1 false (-2),
    .side 25 35 false (5),
    .last 31 (4,false),
    .side 2 38 true (-1),
    .last 25 (4,false),
    .alternating 16,
    .side 24 17 false (3),
    .last 35 (4,false),
    .last 34 (4,false),
    .last 24 (4,false),
    .last 28 (4,false),
    .last 24 (4,false),
    .side 20 30 false (4),
    .side 28 1 true (6),
    .last 31 (4,false),
    .side 28 1 true (6)]⟩)]

def deepSiblingRoster : List (PackedTable × DeepSiblingWitness) :=
  deepSiblingIndices.filterMap fun (i,w) =>
    executableRootRoster[i]?.map fun e => (e.2,w)

theorem deepSiblingRoster_count : deepSiblingRoster.length = 13 := by decide

theorem deepSiblingRoster_checked :
    deepSiblingRoster.all (fun (t,w) => deepSiblingOK (unpackTable t) w) = true := by
  decide

def deepSiblingHasWitness (t : PackedTable) : Bool :=
  deepSiblingRoster.any fun e => decide (e.1 = t)

theorem deepSiblingHasWitness_sound (t : PackedTable) (h : deepSiblingHasWitness t = true) :
    ∀ m, compatible (unpackTable t) m → WeightedBound 92 m := by
  obtain ⟨⟨u,w⟩,hmem,heq⟩ := List.any_eq_true.mp h
  have he : u = t := of_decide_eq_true heq
  subst u
  exact deepSiblingOK_sound (unpackTable t) w
    (List.all_eq_true.mp deepSiblingRoster_checked (t,w) hmem)

def reducedRootRoster : List PackedResidual :=
  remainingRootRoster.filter fun e => !deepSiblingHasWitness e.2

theorem reducedRootRoster_count : reducedRootRoster.length = 141 := by decide

theorem reducedRootRoster_sound :
    ∀ m, compatible root m → WeightedBound 92 m ∨
      ∃ e ∈ reducedRootRoster, compatible (unpackTable e.2) m := by
  intro m hm
  rcases remainingRootRoster_sound m hm with hb | ⟨e,hmem,hcomp⟩
  · exact Or.inl (fun k d hk hd => Nat.le_trans (hb k d hk hd) (by decide))
  · cases he : deepSiblingHasWitness e.2 with
    | true => exact Or.inl (deepSiblingHasWitness_sound e.2 he m hcomp)
    | false => exact Or.inr ⟨e,List.mem_filter.mpr ⟨hmem,by simp [he]⟩,hcomp⟩

#print axioms deepChildOK_sound
#print axioms deepSiblingOK_sound
#print axioms deepSiblingRoster_checked
#print axioms reducedRootRoster_count
#print axioms reducedRootRoster_sound

end BB6.Agent50RootFrontier
