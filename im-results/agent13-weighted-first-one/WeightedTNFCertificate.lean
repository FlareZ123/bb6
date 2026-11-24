import WeightedTNF

set_option maxHeartbeats 1000000

namespace BB6.Agent13BlankDelay
open BB6Coverage

/-- Upstream TNF nodes contain only ordinary assigned instructions. A
    missing entry is an unexpanded first hole, never an assigned halt. -/
def weightedTNFNoAssignedHalt (p : PartialMachine) : Prop :=
  ∀ s, p s ≠ some (none : Transition)

/-- The sparse execution is defined at every finite time. This is the
    source-independent form of a nonhalting decider leaf. -/
def weightedTNFKnownRunForever (p : PartialMachine) : Prop :=
  ∀ n, ∃ c, knownRun p n = some c

/-- Ordinary TNF expansion preserves the no-assigned-halt invariant. -/
theorem weightedTNFNoAssignedHalt_refine (p : PartialMachine) (slot : Slot)
    (mv : Move) (h : weightedTNFNoAssignedHalt p) :
    weightedTNFNoAssignedHalt (refine p slot (some mv)) := by
  intro s
  by_cases hs : s = slot
  · subst s
    simp [refine]
  · simpa [refine, hs] using h s

theorem weightedTNFKnownRunForever_sound (p : PartialMachine)
    (h : weightedTNFKnownRunForever p) (m : Machine) (hm : compatible p m) :
    NeverHalts m := by
  intro n
  obtain ⟨c, hc⟩ := h n
  have hr := knownRun_sound p m hm n c hc
  simp [hr]

/-- Complete a sparse table by interpreting every unassigned row as
    an immediate halt. This is the canonical partial-machine semantics used
    by the upstream TNF NonHalt result. -/
def weightedTNFDefaultCompletion (p : PartialMachine) : Machine :=
  fun s => (p s).getD none

theorem weightedTNFDefaultCompletion_compatible (p : PartialMachine) :
    compatible p (weightedTNFDefaultCompletion p) := by
  intro s t hs
  simp [weightedTNFDefaultCompletion, hs]

theorem weightedTNFKnownRun_eq_defaultRun (p : PartialMachine) (n : Nat) :
    knownRun p n = run (weightedTNFDefaultCompletion p) n blank := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp [knownRun, run, knownStep, rawStep, weightedTNFDefaultCompletion, ih]

/-- A partial node is nonhalting exactly when every total completion is
    nonhalting. The reverse direction uses the completion that halts at every
    still-unassigned row; if its run is infinite, no hole is ever reached. -/
theorem weightedTNFKnownRunForever_iff (p : PartialMachine) :
    weightedTNFKnownRunForever p ↔
      ∀ m, compatible p m → NeverHalts m := by
  constructor
  · intro h m hm
    exact weightedTNFKnownRunForever_sound p h m hm
  · intro h n
    have hn : (run (weightedTNFDefaultCompletion p) n blank).isSome = true :=
      h (weightedTNFDefaultCompletion p)
        (weightedTNFDefaultCompletion_compatible p) n
    have hn' : (knownRun p n).isSome = true := by
      rw [← weightedTNFKnownRun_eq_defaultRun p n]
      exact hn
    cases hrun : knownRun p n with
    | none => simp [hrun] at hn'
    | some c => exact ⟨c, hrun⟩

/-- A proof-carrying, recursively normalized TNF search tree.

    * nonhalt closes a node whose known sparse run is infinite.
    * lastHole is exactly the upstream expand' optimization: with only
      one undefined row, every ordinary completion is total and hence
      nonhalting; only the explicit halt completion needs a score bound.
    * expand branches over every existing successor label and one fresh
      canonical label. The fresh-label child represents every unused state
      by a root-fixing permutation, as proved by tnf_branch_sound.

    The tree is data in Type; all semantic leaves carry Lean proofs. -/
inductive WeightedTNFCertificate (B : Nat) : PartialMachine → Nat → Type where
  | nonhalt {p cut}
      (hroot : p initialSlot = some (some ⟨true, true, 1⟩))
      (hsupport : TNFSupport p cut)
      (hnohalt : weightedTNFNoAssignedHalt p)
      (hnever : ∀ m, compatible p m → NeverHalts m) :
      WeightedTNFCertificate B p cut
  | lastHole {p cut n c}
      (hroot : p initialSlot = some (some ⟨true, true, 1⟩))
      (hsupport : TNFSupport p cut)
      (hcut : 0 < cut)
      (hrun : knownRun p n = some c)
      (hhole : p (readSlot c) = none)
      (hrest : ∀ slot, slot ≠ readSlot c →
        ∃ mv, p slot = some (some mv))
      (hweight : ∀ d ∈ possibleDelays (refine p (readSlot c) none) 0,
        d + n + 1 ≤ B) :
      WeightedTNFCertificate B p cut
  | expand {p cut n c}
      (hroot : p initialSlot = some (some ⟨true, true, 1⟩))
      (hsupport : TNFSupport p cut)
      (hcut : 0 < cut)
      (hnohalt : weightedTNFNoAssignedHalt p)
      (hrun : knownRun p n = some c)
      (hhole : p (readSlot c) = none)
      (hweight : ∀ d ∈ possibleDelays (refine p (readSlot c) none) 0,
        d + n + 1 ≤ B)
      (hold : ∀ mv : Move, mv.next.val < cut →
        WeightedTNFCertificate B (refine p (readSlot c) (some mv)) cut)
      (hnew : ∀ q : Fin 6, q.val = cut → ∀ w r : Bool,
        WeightedTNFCertificate B
          (refine p (readSlot c) (some ⟨w, r, q⟩)) (cut + 1)) :
      WeightedTNFCertificate B p cut

/-- Every normalized TNF certificate closes all compatible total tables. -/
theorem WeightedTNFCertificate.sound {B : Nat} {p : PartialMachine} {cut : Nat}
    (cert : WeightedTNFCertificate B p cut) :
    ∀ m, compatible p m → WeightedBound B m := by
  induction cert with
  | nonhalt hroot hsupport hnohalt hnever =>
      intro m hm
      exact weighted_never B m (hnever m hm)
  | lastHole hroot hsupport hcut hrun hhole hrest hweight =>
      intro m hm
      exact last_hole_sound B _ _ _ hroot hrun hhole hrest hweight m hm
  | expand hroot hsupport hcut hnohalt hrun hhole hweight hold hnew ihHold ihNew =>
      intro m hm
      have hbranch := tnf_branch_sound B _ _ _ hcut hsupport hhole
        (knownRun_support _ _ hcut hsupport _ _ hrun) hroot
        (first_hole_weighted_halt B _ _ _ hroot hrun hhole hweight)
        (by
          intro mv hlt m' hm'
          exact ihHold mv hlt m' hm')
        (by
          intro q hq w r m' hm'
          exact ihNew q hq w r m' hm')
      exact hbranch m hm

/-- Convert the compressed TNF tree into the repository's ordinary
    proof-carrying sparse Cover object. -/
theorem WeightedTNFCertificate.toCover {B : Nat} {p : PartialMachine} {cut : Nat}
    (cert : WeightedTNFCertificate B p cut) :
    Cover (WeightedBound B) p :=
  .leaf p cert.sound

#print axioms weightedTNFKnownRunForever_sound
#print axioms WeightedTNFCertificate.sound
#print axioms WeightedTNFCertificate.toCover
end BB6.Agent13BlankDelay
