import RootFrontier
import R1Graft
import R4Graft

set_option maxRecDepth 40000
set_option maxHeartbeats 0

namespace BB6.Agent47RootedTNF

open BB6Coverage BB6.Agent13BlankDelay BB6.Agent8TNFPath
open BB6.Agent50RootFrontier BB6.Agent50TNFPilot
open BB6.Agent47R1Parent BB6.Agent47R1Graft
open BB6.Agent47R4Parent BB6.Agent47R4Graft

/-- Monotonicity of the weighted score bound. -/
theorem weightedBound_mono {B C : Nat} (hBC : B ≤ C) {m : Machine}
    (h : WeightedBound B m) : WeightedBound C m := by
  intro k d hk hd
  exact Nat.le_trans (h k d hk hd) hBC

/-- Lift a checked TNF certificate to any weaker (larger) score bound. -/
def liftCert {B C : Nat} (hBC : B ≤ C) {p : PartialMachine} {cut : Nat}
    (cert : WeightedTNFCertificate B p cut) :
    WeightedTNFCertificate C p cut := by
  induction cert with
  | nonhalt hroot hsupport hnohalt hnever =>
      exact .nonhalt hroot hsupport hnohalt hnever
  | weightedLeaf hroot hsupport hnohalt hweighted =>
      exact .weightedLeaf hroot hsupport hnohalt
        (fun m hm => weightedBound_mono hBC (hweighted m hm))
  | lastHole hroot hsupport hcut hrun hhole hrest hweight =>
      exact .lastHole hroot hsupport hcut hrun hhole hrest
        (fun d hd => Nat.le_trans (hweight d hd) hBC)
  | expand hroot hsupport hcut hnohalt hrun hhole hweight hold hnew ihHold ihNew =>
      exact .expand hroot hsupport hcut hnohalt hrun hhole
        (fun d hd => Nat.le_trans (hweight d hd) hBC)
        (fun mv hlt => ihHold mv hlt)
        (fun q hq w r => ihNew q hq w r)

/-- The same first-hole path check as Agent 50's pilot, parameterized by the
    requested weighted bound so independently proved parent certificates can
    be assembled at a common root bound. -/
def pathOKB (B : Nat) (p : PartialMachine) (cut : Nat) :
    List PathEntry → Bool
  | [] => true
  | (n,s,mv)::xs =>
      decide (p s = none) &&
      decide ((knownRun p n).map readSlot = some s) &&
      decide (s.1.val < cut) &&
      decide (mv.next.val ≤ cut) &&
      weightOK p s n B &&
      pathOKB B (refine p s (some mv)) (advanceCut cut mv) xs

theorem pathOKB_cons {B : Nat} {p : PartialMachine} {cut n : Nat}
    {s : Slot} {mv : Move} {xs : List PathEntry}
    (h : pathOKB B p cut ((n,s,mv)::xs) = true) :
    p s = none ∧
    (knownRun p n).map readSlot = some s ∧
    s.1.val < cut ∧ mv.next.val ≤ cut ∧
    weightOK p s n B = true ∧
    pathOKB B (refine p s (some mv)) (advanceCut cut mv) xs = true := by
  simpa only [pathOKB, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using h

/-- Build a complete prefix tree along one validated first-hole path, leaving
    every off-path ordinary instruction as an explicit residual leaf. -/
def buildFrontierB (B : Nat) (p : PartialMachine) (cut : Nat)
    (hp : RawRootPath p) :
    (xs : List PathEntry) →
    pathOKB B p cut xs = true →
    WeightedTNFCertificate B (pathEnd p cut xs).1 6 →
    RootedFrontier B p
  | [], _, cert => .closed hp cert
  | (n,s,mv)::xs, h, cert => by
      have hfields := pathOKB_cons h
      rcases hfields with ⟨hhole,hread,_,_,hweight,htail⟩
      let c := (extractRunConfig hread).val
      have hr : knownRun p n = some c := (extractRunConfig hread).property
      have hs : readSlot c = s := by
        have h' : (some c).map readSlot = some s := by
          simpa [hr] using hread
        simpa using h'
      have hhole' : p (readSlot c) = none := by simpa [hs] using hhole
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
                (advanceCut cut mv) (RawRootPath.step hp hr hhole' mv)
                xs htail' cert')
        else
          .residual (RawRootPath.step hp hr hhole' actual))

/-- A one-edge endpoint equation for the path fold. -/
theorem pathEnd_cons (p : PartialMachine) (cut n : Nat) (s : Slot)
    (mv : Move) (xs : List PathEntry) :
    pathEnd p cut ((n,s,mv)::xs) =
      pathEnd (refine p s (some mv)) (advanceCut cut mv) xs := rfl

def r1First : Move := ⟨true,false,2⟩
def pilotFirst : Move := ⟨true,true,2⟩
def pilotSecond : Move := ⟨false,true,3⟩
def r4Second : Move := ⟨false,false,3⟩

def r1Start : PartialMachine := refine root (1,false) (some r1First)
def pilotStart : PartialMachine := refine root (1,false) (some pilotFirst)
def r1Cut : Nat := advanceCut 2 r1First
def pilotCut : Nat := advanceCut 2 pilotFirst
def pilotAfterSecond : PartialMachine :=
  refine pilotStart (2,false) (some pilotSecond)
def r4AfterSecond : PartialMachine :=
  refine pilotStart (2,false) (some r4Second)
def afterSecondCut : Nat := advanceCut pilotCut pilotSecond
def r4AfterSecondCut : Nat := advanceCut pilotCut r4Second

theorem r1_path_cons :
    r1.path = (1,(1,false),r1First) :: r1.path.tail := by decide

theorem pilot_path_cons :
    path = (1,(1,false),pilotFirst) :: path.tail := by decide

theorem r4_path_cons :
    r4.path = (1,(1,false),pilotFirst) :: r4.path.tail := by decide

theorem pilot_tail_cons :
    path.tail = (2,(2,false),pilotSecond) :: path.tail.tail := by decide

theorem r4_tail_cons :
    r4.path.tail = (2,(2,false),r4Second) :: r4.path.tail.tail := by decide

theorem r1_pathEnd_tail :
    pathEnd root 2 r1.path = pathEnd r1Start r1Cut r1.path.tail := by
  rw [r1_path_cons]
  rfl

theorem pilot_pathEnd_tail2 :
    pathEnd root 2 path =
      pathEnd pilotAfterSecond afterSecondCut path.tail.tail := by
  rw [pilot_path_cons, pilot_tail_cons]
  rfl

theorem r4_pathEnd_tail2 :
    pathEnd root 2 r4.path =
      pathEnd r4AfterSecond r4AfterSecondCut r4.path.tail.tail := by
  rw [r4_path_cons, r4_tail_cons]
  rfl

theorem pilotPathOK : pathOKB 7014 root 2 path = true := by decide
theorem r1PathOK : pathOKB 7014 root 2 r1.path = true := by decide
theorem r4PathOK : pathOKB 7014 root 2 r4.path = true := by decide

def pilotCert : WeightedTNFCertificate 7014 (pathEnd root 2 path).1 6 := by
  have h := liftCert (B:=84) (C:=7014) (by decide) certificate
  simpa [parent] using h

def r1Cert : WeightedTNFCertificate 7014 (pathEnd root 2 r1.path).1 6 := by
  simpa [r1.bound, r1.parent] using r1_certificate

def r4Cert : WeightedTNFCertificate 7014 (pathEnd root 2 r4.path).1 6 := by
  have h := liftCert (B:=42) (C:=7014) (by decide) r4_certificate
  simpa [r4.bound, r4.parent] using h

/-- The r1 path occupies the B0=1LC child of the root's first hole. -/
def r1Subtree : RootedFrontier 7014 r1Start := by
  have h := pathOKB_cons r1PathOK
  rcases h with ⟨hhole,hread,_,_,_,htail⟩
  let c := (extractRunConfig hread).val
  have hr : knownRun root 1 = some c := (extractRunConfig hread).property
  have hs : readSlot c = (1,false) := by
    have h' : (some c).map readSlot = some (1,false) := by
      simpa [hr] using hread
    simpa using h'
  have hhole' : root (readSlot c) = none := by simpa [hs] using hhole
  have hp : RawRootPath r1Start := by
    simpa [r1Start, r1First, r1Cut, hs] using
      (RawRootPath.step RawRootPath.root hr hhole' r1First)
  have htail' : pathOKB 7014 r1Start r1Cut r1.path.tail = true := by
    simpa [r1Start, r1First, r1Cut, hs] using htail
  have hcert : WeightedTNFCertificate 7014
      (pathEnd r1Start r1Cut r1.path.tail).1 6 := by
    rw [← r1_pathEnd_tail]
    exact r1Cert
  exact buildFrontierB 7014 r1Start r1Cut hp r1.path.tail htail' hcert

/-- The pilot and r4 paths share the B0=1RC edge and split at the next
    first hole C0: 0RD continues the pilot, while 0LD enters r4. -/
def pilotR4Subtree : RootedFrontier 7014 pilotStart := by
  have hp := pathOKB_cons pilotPathOK
  rcases hp with ⟨hhole1,hread1,_,_,_,htail1⟩
  let c1 := (extractRunConfig hread1).val
  have hr1 : knownRun root 1 = some c1 := (extractRunConfig hread1).property
  have hs1 : readSlot c1 = (1,false) := by
    have h' : (some c1).map readSlot = some (1,false) := by
      simpa [hr1] using hread1
    simpa using h'
  have hhole1' : root (readSlot c1) = none := by simpa [hs1] using hhole1
  have raw1 : RawRootPath pilotStart := by
    simpa [pilotStart, pilotFirst, hs1] using
      (RawRootPath.step RawRootPath.root hr1 hhole1' pilotFirst)
  have tail1' : pathOKB 7014 pilotStart pilotCut path.tail = true := by
    simpa [pilotStart, pilotFirst, pilotCut, hs1] using htail1

  have hp2 := pathOKB_cons tail1'
  rcases hp2 with ⟨hhole2,hread2,_,_,hweight2,htail2⟩
  let c2 := (extractRunConfig hread2).val
  have hr2 : knownRun pilotStart 2 = some c2 := (extractRunConfig hread2).property
  have hs2 : readSlot c2 = (2,false) := by
    have h' : (some c2).map readSlot = some (2,false) := by
      simpa [hr2] using hread2
    simpa using h'
  have hhole2' : pilotStart (readSlot c2) = none := by
    simpa [hs2] using hhole2
  have hw2 : ∀ d ∈ possibleDelays (refine pilotStart (readSlot c2) none) 0,
      d + 2 + 1 ≤ 7014 := by
    simpa [hs2.symm] using (weightOK_sound pilotStart (2,false) 2 7014 hweight2)
  have rawPilot2 : RawRootPath pilotAfterSecond := by
    simpa [pilotAfterSecond, pilotSecond, hs2] using
      (RawRootPath.step raw1 hr2 hhole2' pilotSecond)
  have rawR4Second : RawRootPath r4AfterSecond := by
    simpa [r4AfterSecond, r4Second, hs2] using
      (RawRootPath.step raw1 hr2 hhole2' r4Second)
  have pilotTail2 : pathOKB 7014 pilotAfterSecond afterSecondCut path.tail.tail = true := by
    simpa [pilotAfterSecond, pilotSecond, afterSecondCut, hs2] using htail2
  have pilotCertTail : WeightedTNFCertificate 7014
      (pathEnd pilotAfterSecond afterSecondCut path.tail.tail).1 6 := by
    rw [← pilot_pathEnd_tail2]
    exact pilotCert

  have hr4 := pathOKB_cons r4PathOK
  rcases hr4 with ⟨_,hreadR1,_,_,_,htailR1⟩
  let cR1 := (extractRunConfig hreadR1).val
  have hrR1 : knownRun root 1 = some cR1 := (extractRunConfig hreadR1).property
  have hsR1 : readSlot cR1 = (1,false) := by
    have h' : (some cR1).map readSlot = some (1,false) := by
      simpa [hrR1] using hreadR1
    simpa using h'
  have r4Tail1 : pathOKB 7014 pilotStart pilotCut r4.path.tail = true := by
    simpa [pilotStart, pilotFirst, pilotCut, hsR1] using htailR1

  have hr4second := pathOKB_cons r4Tail1
  rcases hr4second with ⟨_,hreadR2,_,_,_,htailR2⟩
  let cR2 := (extractRunConfig hreadR2).val
  have hrR2 : knownRun pilotStart 2 = some cR2 := (extractRunConfig hreadR2).property
  have hsR2 : readSlot cR2 = (2,false) := by
    have h' : (some cR2).map readSlot = some (2,false) := by
      simpa [hrR2] using hreadR2
    simpa using h'
  have r4Tail2 : pathOKB 7014 r4AfterSecond r4AfterSecondCut r4.path.tail.tail = true := by
    simpa [r4AfterSecond, r4Second, pilotStart, pilotFirst, r4AfterSecondCut,
      hsR1, hsR2] using htailR2
  have r4CertTail : WeightedTNFCertificate 7014
      (pathEnd r4AfterSecond r4AfterSecondCut r4.path.tail.tail).1 6 := by
    rw [← r4_pathEnd_tail2]
    exact r4Cert

  refine .expand raw1 hr2 hhole2' hw2 ?children
  intro mv
  by_cases hpMove : mv = pilotSecond
  · subst mv
    exact buildFrontierB 7014 pilotAfterSecond afterSecondCut rawPilot2
      path.tail.tail pilotTail2 pilotCertTail
  by_cases r4Move : mv = r4Second
  · subst mv
    exact buildFrontierB 7014 r4AfterSecond r4AfterSecondCut rawR4Second
      r4.path.tail.tail r4Tail2 r4CertTail
  · exact .residual (RawRootPath.step raw1 hr2 hhole2' mv)

/-- A rooted three-parent shard: the Agent 50 84-bound pilot, Agent 47's
    r1 parent (7014), and Agent 47's r4 parent (42). Every unselected ordinary
    instruction remains an explicit residual leaf. -/
def rootFrontierR1R4 : RootedFrontier 7014 root := by
  have h := pathOKB_cons pilotPathOK
  rcases h with ⟨hhole,hread,_,_,hweight,_⟩
  let c := (extractRunConfig hread).val
  have hr : knownRun root 1 = some c := (extractRunConfig hread).property
  have hs : readSlot c = (1,false) := by
    have h' : (some c).map readSlot = some (1,false) := by
      simpa [hr] using hread
    simpa using h'
  have hhole' : root (readSlot c) = none := by simpa [hs] using hhole
  have hw : ∀ d ∈ possibleDelays (refine root (readSlot c) none) 0,
      d + 1 + 1 ≤ 7014 := by
    simpa [hs.symm] using (weightOK_sound root (1,false) 1 7014 hweight)
  refine .expand RawRootPath.root hr hhole' hw ?children
  intro mv
  by_cases hR1 : mv = r1First
  · subst mv
    simpa [r1Start, r1First, hs] using r1Subtree
  by_cases hPilot : mv = pilotFirst
  · subst mv
    simpa [pilotStart, pilotFirst, hs] using pilotR4Subtree
  · exact .residual (RawRootPath.step RawRootPath.root hr hhole' mv)

/-- Count explicit first-hole expansions in a rooted frontier. -/
def expandedNodes {B : Nat} {p : PartialMachine} :
    RootedFrontier B p → Nat
  | .residual _ => 0
  | .closed _ _ => 0
  | .expand _ _ _ _ children =>
      1 + (allMoves.map fun mv => expandedNodes (children mv)).sum

/-- Count closed terminal weighted certificates. -/
def closedLeaves {B : Nat} {p : PartialMachine} :
    RootedFrontier B p → Nat
  | .residual _ => 0
  | .closed _ _ => 1
  | .expand _ _ _ _ children =>
      (allMoves.map fun mv => closedLeaves (children mv)).sum

theorem rootFrontierR1R4_sound :
    ∀ m, compatible root m →
      WeightedBound 7014 m ∨
        ∃ address q, OpenLeaf rootFrontierR1R4 address q ∧ compatible q m :=
  RootedFrontier.sound rootFrontierR1R4

theorem rootFrontierR1R4_openLeaves_disjoint :
    ∀ address1 q1 address2 q2,
      OpenLeaf rootFrontierR1R4 address1 q1 →
      OpenLeaf rootFrontierR1R4 address2 q2 →
      (address1, q1) ≠ (address2, q2) →
      ∀ m, ¬ (compatible q1 m ∧ compatible q2 m) :=
  RootedFrontier.openLeaves_disjoint rootFrontierR1R4

theorem rootFrontierR1R4_expanded_nodes :
    expandedNodes rootFrontierR1R4 = 24 := by decide

theorem rootFrontierR1R4_closed_leaves :
    closedLeaves rootFrontierR1R4 = 3 := by decide

theorem rootFrontierR1R4_residual_count :
    (residuals rootFrontierR1R4).length = 550 := by decide

#print axioms rootFrontierR1R4_sound
#print axioms rootFrontierR1R4_openLeaves_disjoint
#print axioms rootFrontierR1R4_expanded_nodes
#print axioms rootFrontierR1R4_closed_leaves
#print axioms rootFrontierR1R4_residual_count

end BB6.Agent47RootedTNF
