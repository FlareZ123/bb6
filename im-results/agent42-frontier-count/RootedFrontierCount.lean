import FourHoleRootFrontier
import CanonicalRosterRefinement

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent42FrontierCount

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleFrontier
open BB6.Agent50TNFPilot
open BB6.Agent31FourHoleRoster
open BB6.Agent47CanonicalRefinement

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
      have htail' : pathOKB B (refine p (readSlot c) (some mv))
          (advanceCut cut mv) xs = true := by
        simpa [hs.symm] using htail
      have cert' : WeightedTNFCertificate B
          (pathEnd (refine p (readSlot c) (some mv)) (advanceCut cut mv) xs).1 6 := by
        simpa [pathEnd, hs.symm] using cert
      have ih' := ih
        (refine p (readSlot c) (some mv))
        (advanceCut cut mv)
        (RawRootPath.step hp hr hhole') htail' cert'
      simp [buildFrontierB, residuals, pureResiduals,
        c, hr, hs, hhole', htail', cert', ih', residuals_cast]

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
      simp [List.flatMap, hx, ih htail]

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
        simp [List.flatMap, hlen]
        omega
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
        simp [List.flatMap, hx, ih']
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
      rw [pureResiduals, hlen, allMoves_length, hspecial,
        ih (refine p s (some mv))]
      omega

/-- Structural cardinality of the exact residual list of a rooted path. -/
theorem residuals_length_buildFrontierB (B : Nat)
    (p : PartialMachine) (cut : Nat) (hp : RawRootPath p)
    (xs : List PathEntry)
    (h : pathOKB B p cut = true)
    (cert : WeightedTNFCertificate B (pathEnd p cut xs).1 6) :
    (residuals (buildFrontierB B p cut hp xs h cert)).length =
      23 * xs.length := by
  rw [residuals_buildFrontierB B p cut hp xs h cert]
  exact pureResiduals_length p xs

/-- Exact list-length accounting for a roster graft. Each matched parent is
    replaced by the supplied child list; every nonmatched entry remains one. -/
theorem graftRoster_length (p : PartialMachine) (replacement roster : List Entry) :
    (graftRoster p replacement roster).length =
      roster.length -
        (roster.filter (fun e => sameTable e.2 p)).length +
        (roster.filter (fun e => sameTable e.2 p)).length *
          replacement.length := by
  induction roster with
  | nil => simp [graftRoster]
  | cons e es ih =>
      by_cases h : sameTable e.2 p = true
      · simp [graftRoster,graftEntry,h,ih]
        omega
      · simp [graftRoster,graftEntry,h,ih]
        omega

theorem graftRoster_length_of_one (p : PartialMachine)
    (replacement roster : List Entry)
    (hcount : (roster.filter (fun e => sameTable e.2 p)).length = 1) :
    (graftRoster p replacement roster).length =
      roster.length - 1 + replacement.length := by
  rw [graftRoster_length, hcount]
  omega

#print axioms residuals_buildFrontierB
#print axioms pureResiduals_length
#print axioms residuals_length_buildFrontierB
#print axioms graftRoster_length
#print axioms graftRoster_length_of_one

end BB6.Agent42FrontierCount
