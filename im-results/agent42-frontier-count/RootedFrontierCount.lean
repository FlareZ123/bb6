import FourHoleRootFrontier

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42FrontierCount

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleFrontier
open BB6.Agent50TNFPilot
open BB6.Agent8TNFPath

abbrev Entry := List Move × PartialMachine

/-- Pure projection of the off-path ordinary children of a checked path.
    The terminal certificate is deliberately absent: residual table data
    depends only on the path and the 24 ordinary instructions. -/
def pureResiduals (p : PartialMachine) :
    List PathEntry → List Entry
  | [] => []
  | (n,s,mv) :: xs =>
      allMoves.flatMap fun actual =>
        if actual = mv then
          (pureResiduals (refine p s (some mv)) xs).map
            (fun (address,q) => (actual :: address,q))
        else
          [([actual], refine p s (some actual))]

@[simp] theorem residuals_cast {B : Nat} {p q : PartialMachine}
    (h : p = q) (f : RootedFrontier B p) :
    residuals (h ▸ f) = residuals f := by
  cases h
  rfl

theorem flatMap_congr {α β : Type} (xs : List α)
    (f g : α → List β)
    (h : ∀ x, x ∈ xs → f x = g x) :
    xs.flatMap f = xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := h x (by simp)
      have htail : ∀ y, y ∈ xs → f y = g y := by
        intro y hy
        exact h y (by simp [hy])
      simp [hx, ih htail]

/-- Reconstruct the exact residual list from buildFrontierB without
    reducing its dependent proof-carrying frontier. -/
theorem residuals_buildFrontierB (B : Nat) :
    ∀ (p : PartialMachine) (cut : Nat) (hp : RawRootPath p)
      (xs : List PathEntry)
      (h : pathOKB B p cut xs = true)
      (cert : WeightedTNFCertificate B (pathEnd p cut xs).1 6),
      residuals (buildFrontierB B p cut hp xs h cert) = pureResiduals p xs := by
  intro p cut hp xs
  induction xs generalizing p cut hp with
  | nil =>
      intro h cert
      simp [buildFrontierB, residuals, pureResiduals]
  | cons entry xs ih =>
      rcases entry with ⟨n,s,mv⟩
      intro h cert
      have hfields := pathOKB_cons h
      rcases hfields with ⟨hhole,hread,hslot,hmove,hweight,htail⟩
      let c := (extractRunConfig hread).val
      have hr : knownRun p n = some c :=
        (extractRunConfig hread).property
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
          (pathEnd (refine p (readSlot c) (some mv))
            (advanceCut cut mv) xs).1 6 := by
        simpa [pathEnd, hs.symm] using cert
      have ih' := ih
        (refine p (readSlot c) (some mv))
        (advanceCut cut mv)
        (RawRootPath.step hp hr hhole') htail' cert'
      simp only [buildFrontierB, residuals, pureResiduals]
      apply flatMap_congr
      intro actual hmem
      by_cases heq : actual = mv
      · subst actual
        simp [ih', hs, residuals_cast]
      · simp [heq, hs, residuals]

/-- Every path edge has 23 off-path ordinary children: the selected move
    is the unique one among the 24 ordinary moves that continues the path. -/
theorem allMoves_nodup : allMoves.Nodup := by
  decide

theorem flatMap_length_all_one {α β : Type} (xs : List α)
    (f : α → List β)
    (h : ∀ x, x ∈ xs → (f x).length = 1) :
    (xs.flatMap f).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      have hx := h x (by simp)
      have htail : ∀ y, y ∈ xs → (f y).length = 1 := by
        intro y hy
        exact h y (by simp [hy])
      rw [List.flatMap_cons, List.length_append, hx, ih htail]
      simp [Nat.add_comm]

theorem flatMap_length_single_exception {α β : Type}
    (xs : List α) (f : α → List β) (a : α)
    (ha : a ∈ xs) (hn : xs.Nodup)
    (hother : ∀ x, x ∈ xs → x ≠ a → (f x).length = 1) :
    (xs.flatMap f).length = (f a).length + xs.length - 1 := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
      rcases List.nodup_cons.mp hn with ⟨hnot,hNodup⟩
      have hmem : a = x ∨ a ∈ xs := by simpa using ha
      by_cases hxa : x = a
      · subst x
        have hotherTail : ∀ y, y ∈ xs → (f y).length = 1 := by
          intro y hy
          have hya : y ≠ a := by
            intro heq
            subst y
            exact hnot hy
          exact hother y (by simp [hy]) hya
        have hlen := flatMap_length_all_one xs f hotherTail
        rw [List.flatMap_cons, List.length_append, hlen]
        simp [Nat.add_comm]
      · have hmemTail : a ∈ xs := by
          rcases hmem with hhead | htail
          · exact False.elim (hxa hhead.symm)
          · exact htail
        have hx : (f x).length = 1 := hother x (by simp) hxa
        have hotherTail : ∀ y, y ∈ xs → y ≠ a → (f y).length = 1 := by
          intro y hy hya
          exact hother y (by simp [hy]) hya
        have ih' := ih hmemTail hNodup hotherTail
        have hlen : 0 < xs.length := by
          cases xs with
          | nil => simp at hmemTail
          | cons y ys => simp
        rw [List.flatMap_cons, List.length_append, hx, ih']
        simp
        omega

/-- The pure residual projection has a path-length-only cardinality.
    This avoids evaluating a large dependent proof object with decide. -/
theorem pureResiduals_length (p : PartialMachine) :
    ∀ xs, (pureResiduals p xs).length = 23 * xs.length := by
  intro xs
  induction xs generalizing p with
  | nil => simp [pureResiduals]
  | cons entry xs ih =>
      rcases entry with ⟨n,s,mv⟩
      let f : Move → List Entry := fun actual =>
        if actual = mv then
          (pureResiduals (refine p s (some mv)) xs).map
            (fun (address,q) => (actual :: address,q))
        else
          [([actual], refine p s (some actual))]
      have hlen := flatMap_length_single_exception
        allMoves f mv (allMoves_complete mv) allMoves_nodup
        (by
          intro actual hmem hne
          simp [f,hne])
      have hspecial :
          (f mv).length =
            (pureResiduals (refine p s (some mv)) xs).length := by
        simp [f]
      change (allMoves.flatMap f).length = 23 * (xs.length + 1)
      rw [hlen, allMoves_length, hspecial,
        ih (refine p s (some mv))]
      omega

/-- Structural cardinality of the exact residual list of a rooted path. -/
theorem residuals_length_buildFrontierB (B : Nat)
    (p : PartialMachine) (cut : Nat) (hp : RawRootPath p)
    (xs : List PathEntry)
    (h : pathOKB B p cut xs = true)
    (cert : WeightedTNFCertificate B (pathEnd p cut xs).1 6) :
    (residuals (buildFrontierB B p cut hp xs h cert)).length =
      23 * xs.length := by
  rw [residuals_buildFrontierB B p cut hp xs h cert]
  exact pureResiduals_length p xs

/-- Every semantic open leaf is present in the exact executable residual
    projection, for any bound and any rooted frontier. -/
theorem OpenLeaf_mem_residuals {B : Nat} {p : PartialMachine}
    {f : RootedFrontier B p} {address : List Move} {q : PartialMachine}
    (h : OpenLeaf f address q) :
    (address,q) ∈ residuals f := by
  induction h with
  | here path =>
      simp [residuals]
  | @child p n c path hrun hhole hweight children mv address q hchild ih =>
      apply List.mem_flatMap.mpr
      refine ⟨mv, allMoves_complete mv, ?_⟩
      apply List.mem_map.mpr
      exact ⟨(address,q), ih, rfl⟩

/-- Convert a checked TNF path into the ancestry witness required by the
    sibling-preserving frontier builder. -/
theorem rawRootPath_of_pathOK
    (p : PartialMachine) (cut : Nat) (xs : List PathEntry)
    (hp : RawRootPath p)
    (h : BB6.Agent50TNFPilot.pathOK p cut xs = true) :
    RawRootPath (BB6.Agent50TNFPilot.pathEnd p cut xs).1 := by
  induction xs generalizing p cut with
  | nil =>
      simpa [BB6.Agent50TNFPilot.pathEnd] using hp
  | cons entry xs ih =>
      rcases entry with ⟨n,s,mv⟩
      simp only [BB6.Agent50TNFPilot.pathOK, Bool.and_eq_true,
        decide_eq_true_eq] at h
      rcases h with ⟨hhole,hrest⟩
      rcases hrest with ⟨hread,hrest⟩
      rcases hrest with ⟨_hslot,hrest⟩
      rcases hrest with ⟨_hmove,htail⟩
      cases hr : knownRun p n with
      | none => simp [hr] at hread
      | some c =>
          have hs : readSlot c = s := by simpa [hr] using hread
          subst s
          have hpath : RawRootPath (refine p (readSlot c) (some mv)) :=
            RawRootPath.step hp hr hhole
          simpa [BB6.Agent50TNFPilot.pathEnd] using
            ih (refine p (readSlot c) (some mv))
              (BB6.Agent8TNFPath.advanceCut cut mv) hpath htail

#print axioms residuals_buildFrontierB
#print axioms pureResiduals_length
#print axioms residuals_length_buildFrontierB
#print axioms OpenLeaf_mem_residuals
#print axioms rawRootPath_of_pathOK

end BB6.Agent42FrontierCount
