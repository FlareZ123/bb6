import RootFrontier
import FourHoleData

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent31FourHoleFrontier

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50TNFPilot BB6.Agent50RootFrontier BB6.Agent31FourHole

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

/-- Extend the accepted rooted-frontier constructor to any weighted bound.
    The path is checked edge-by-edge, every off-path ordinary instruction
    remains an explicit residual, and the terminal certificate closes the
    selected descendant. -/
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
theorem wideCertificate_root :
    WeightedTNFCertificate 395 (pathEnd root 2 (path.take 7)).1 6 := by
  simpa [wideParent] using certificate

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

def expandedNodes {B : Nat} {p : PartialMachine} :
    RootedFrontier B p → Nat
  | .residual _ => 0
  | .closed _ _ => 0
  | .expand _ _ _ _ children =>
      1 + (allMoves.map fun mv => expandedNodes (children mv)).sum

def closedLeaves {B : Nat} {p : PartialMachine} :
    RootedFrontier B p → Nat
  | .residual _ => 0
  | .closed _ _ => 1
  | .expand _ _ _ _ children =>
      (allMoves.map fun mv => closedLeaves (children mv)).sum

theorem rootFrontier_sound :
    ∀ m, compatible root m →
      WeightedBound 395 m ∨
        ∃ address q, OpenLeaf rootFrontier address q ∧ compatible q m :=
  RootedFrontier.sound rootFrontier

theorem rootFrontier_openLeaves_disjoint :
    ∀ address1 q1 address2 q2,
      OpenLeaf rootFrontier address1 q1 →
      OpenLeaf rootFrontier address2 q2 →
      (address1, q1) ≠ (address2, q2) →
      ∀ m, ¬ (compatible q1 m ∧ compatible q2 m) :=
  RootedFrontier.openLeaves_disjoint rootFrontier

theorem rootFrontier_expanded_nodes :
    expandedNodes rootFrontier = 7 := by decide

theorem rootFrontier_closed_leaves :
    closedLeaves rootFrontier = 1 := by decide

theorem rootFrontier_residual_count :
    (residuals rootFrontier).length = 161 := by decide

#print axioms rootFrontier_sound
#print axioms rootFrontier_openLeaves_disjoint
#print axioms rootFrontier_expanded_nodes
#print axioms rootFrontier_closed_leaves
#print axioms rootFrontier_residual_count

end BB6.Agent31FourHoleFrontier
