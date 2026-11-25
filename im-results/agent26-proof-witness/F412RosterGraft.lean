import Combined109Roster
import MixedBound109Composition
import FourHoleResidualRoster
import WeightedTNFCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Graft
open BB6Coverage BB6.Agent13BlankDelay BB6.Agent31FourHoleFrontier
open BB6.Agent31FourHoleRoster BB6.Agent50TNFPilot BB6.Agent47Combined109
open BB6.Agent13MixedBound109

/-- Canonical raw-10 residual: A0=1RB, B0=1LC. -/
def fResidual : PartialMachine := refine root (1, false) (some ⟨true,false,2⟩)

def fP1 : PartialMachine := refine fResidual (2, true) (some ⟨false, false, 3⟩)
def fP2 : PartialMachine := refine fP1 (3, false) (some ⟨false, true, 4⟩)
def fP3 : PartialMachine := refine fP2 (4, false) (some ⟨true, true, 2⟩)
def fP4 : PartialMachine := refine fP3 (3, true) (some ⟨true, false, 1⟩)
def fP5 : PartialMachine := refine fP4 (2, false) (some ⟨true, true, 5⟩)
def fP6 : PartialMachine := refine fP5 (5, true) (some ⟨false, true, 0⟩)
def fP7 : PartialMachine := refine fP6 (0, true) (some ⟨true, true, 2⟩)
def fP8 : PartialMachine := refine fP7 (5, false) (some ⟨true, false, 3⟩)
def fP9 : PartialMachine := refine fP8 (1, true) (some ⟨false, false, 5⟩)

def fParent (i : Fin 9) : PartialMachine :=
  match i.val with
  | 0 => fResidual
  | 1 => fP1
  | 2 => fP2
  | 3 => fP3
  | 4 => fP4
  | 5 => fP5
  | 6 => fP6
  | 7 => fP7
  | _ => fP8

def fNextParent (i : Fin 9) : PartialMachine :=
  match i.val with
  | 0 => fP1
  | 1 => fP2
  | 2 => fP3
  | 3 => fP4
  | 4 => fP5
  | 5 => fP6
  | 6 => fP7
  | 7 => fP8
  | _ => fP9

def fHole (i : Fin 9) : Slot :=
  match i.val with
  | 0 => (2, true)
  | 1 => (3, false)
  | 2 => (4, false)
  | 3 => (3, true)
  | 4 => (2, false)
  | 5 => (5, true)
  | 6 => (0, true)
  | 7 => (5, false)
  | _ => (1, true)

def fNextMove (i : Fin 9) : Move :=
  match i.val with
  | 0 => ⟨false, false, 3⟩
  | 1 => ⟨false, true, 4⟩
  | 2 => ⟨true, true, 2⟩
  | 3 => ⟨true, false, 1⟩
  | 4 => ⟨true, true, 5⟩
  | 5 => ⟨false, true, 0⟩
  | 6 => ⟨true, true, 2⟩
  | 7 => ⟨true, false, 3⟩
  | _ => ⟨false, false, 5⟩

def fRunLength (i : Fin 9) : Nat :=
  match i.val with
  | 0 => 2
  | 1 => 3
  | 2 => 4
  | 3 => 6
  | 4 => 8
  | 5 => 9
  | 6 => 10
  | 7 => 12
  | _ => 14
def fConfig (i : Fin 8) : Config :=
  (knownRun (fParent i) (fRunLength i)).getD blank

theorem fRunKnown (i : Fin 8) :
    knownRun (fParent i) (fRunLength i) = some (fConfig i) := by
  have hsome :
      (knownRun (fParent i) (fRunLength i)).isSome = true := by
    fin_cases i <;> decide
  unfold fConfig
  cases h : knownRun (fParent i) (fRunLength i) with
  | none => simp [h] at hsome
  | some c => simp [h]

theorem fReadSlot (i : Fin 8) :
    readSlot (fConfig i) = fHole i := by
  fin_cases i <;> decide

theorem fHoleProof (i : Fin 8) :
    fParent i (fHole i) = none := by
  fin_cases i <;> decide


/-- The full literal table; E1 is the only absent transition. -/
def fLiteral : Machine := weightedTNFDefaultCompletion fP9

def fMoves : Nat := 9217091204829760959746640857348768637582782

theorem fFinalNoAssignedHalt : weightedTNFNoAssignedHalt fP9 := by
  intro s
  fin_cases s.1 <;> cases s.2 <;> decide

theorem fFinalUniqueHole {s : Slot} (h : fP9 s = none) : s = (4, true) := by
  fin_cases s.1 <;> cases s.2 <;>
    simp [fP9,fP8,fP7,fP6,fP5,fP4,fP3,fP2,fP1,fResidual,refine,root] at h ⊢

theorem fFinalOtherSlots (s : Slot) (h : s ≠ (4,true)) :
    ∃ mv, fP9 s = some (some mv) := by
  fin_cases s.1 <;> cases s.2 <;>
    simp [fP9,fP8,fP7,fP6,fP5,fP4,fP3,fP2,fP1,fResidual,refine,root] at h ⊢

theorem fFinalDelays : possibleDelays (refine fP9 (4,true) none) 0 = [0] := by decide

/-- All 25 final completions: 24 total ordinary tables and the unique halter.
    Only the exact original-source clock remains an input. -/
theorem fFinalSound (B : Nat) (hB : fMoves+1 ≤ B)
    (hclock : HaltsAfter fLiteral fMoves) :
    ∀ m, compatible fP9 m → WeightedBound B m := by
  obtain ⟨c,hr,hu⟩ :=
    (weightedTNF_halt_iff_firstHole fP9 fFinalNoAssignedHalt fMoves).mp hclock
  have hs := fFinalUniqueHole hu
  apply last_hole_sound B fP9 fMoves c (by decide) hr hu
  · intro s hn
    apply fFinalOtherSlots s
    intro he
    exact hn (he.trans hs.symm)
  · intro d hd
    rw [hs,fFinalDelays] at hd
    simp at hd
    subst d
    simpa using hB

def fChild (i : Fin 9) (mv : Move) : PartialMachine :=
  refine (fParent i) (fHole i) (some mv)

structure FWitness where
  depth : Fin 9
  child : Move
  witness : ResidualNonhaltWitness

/-- Candidate certificates; accepted only if the existing source checker
    replays every one. All are positive-period half-line translation cycles. -/
def fWitnesses : List FWitness := [
  { depth := 0, child := ⟨false, false, 0⟩, witness := .side 0 3 false (1 : Int) },
  { depth := 1, child := ⟨false, false, 0⟩, witness := .side 0 4 false (1 : Int) },
  { depth := 1, child := ⟨true, true, 1⟩, witness := .side 1 3 false (1 : Int) },
  { depth := 1, child := ⟨false, false, 3⟩, witness := .side 3 1 false (-1 : Int) },
  { depth := 1, child := ⟨true, false, 3⟩, witness := .side 3 1 false (-1 : Int) },
  { depth := 2, child := ⟨false, false, 0⟩, witness := .side 0 5 false (1 : Int) },
  { depth := 2, child := ⟨false, false, 3⟩, witness := .side 3 2 true (-1 : Int) },
  { depth := 2, child := ⟨false, false, 4⟩, witness := .side 4 1 false (0 : Int) },
  { depth := 2, child := ⟨true, false, 4⟩, witness := .side 4 1 false (0 : Int) },
  { depth := 3, child := ⟨false, false, 0⟩, witness := .side 0 7 false (1 : Int) },
  { depth := 3, child := ⟨false, true, 0⟩, witness := .side 0 7 true (-1 : Int) },
  { depth := 3, child := ⟨true, true, 1⟩, witness := .side 1 6 true (-1 : Int) },
  { depth := 3, child := ⟨true, false, 4⟩, witness := .side 4 3 false (1 : Int) },
  { depth := 4, child := ⟨false, false, 0⟩, witness := .side 0 9 false (1 : Int) },
  { depth := 4, child := ⟨false, false, 1⟩, witness := .side 7 2 false (-1 : Int) },
  { depth := 4, child := ⟨true, false, 1⟩, witness := .side 7 2 false (-1 : Int) },
  { depth := 4, child := ⟨false, false, 2⟩, witness := .side 8 1 false (-2 : Int) },
  { depth := 4, child := ⟨false, true, 2⟩, witness := .side 2 7 false (1 : Int) },
  { depth := 4, child := ⟨true, false, 2⟩, witness := .side 8 1 false (-2 : Int) },
  { depth := 4, child := ⟨true, true, 2⟩, witness := .side 5 4 false (1 : Int) },
  { depth := 4, child := ⟨false, false, 3⟩, witness := .side 3 6 false (1 : Int) },
  { depth := 4, child := ⟨false, true, 3⟩, witness := .side 6 3 false (0 : Int) },
  { depth := 4, child := ⟨true, false, 4⟩, witness := .side 4 5 false (1 : Int) },
  { depth := 5, child := ⟨false, false, 2⟩, witness := .side 5 10 false (1 : Int) },
  { depth := 5, child := ⟨true, false, 2⟩, witness := .side 2 8 false (1 : Int) },
  { depth := 5, child := ⟨false, false, 3⟩, witness := .side 6 4 false (0 : Int) },
  { depth := 5, child := ⟨false, true, 3⟩, witness := .side 1 10 false (1 : Int) },
  { depth := 5, child := ⟨true, false, 3⟩, witness := .side 6 4 false (0 : Int) },
  { depth := 6, child := ⟨false, false, 0⟩, witness := .side 5 8 false (1 : Int) },
  { depth := 6, child := ⟨false, true, 0⟩, witness := .side 0 11 true (-2 : Int) },
  { depth := 6, child := ⟨false, false, 1⟩, witness := .side 1 10 false (1 : Int) },
  { depth := 6, child := ⟨true, false, 1⟩, witness := .side 1 10 false (1 : Int) },
  { depth := 6, child := ⟨true, true, 1⟩, witness := .side 1 16 false (1 : Int) },
  { depth := 7, child := ⟨false, false, 0⟩, witness := .side 10 3 true (0 : Int) },
  { depth := 7, child := ⟨false, true, 2⟩, witness := .side 11 2 true (1 : Int) },
  { depth := 7, child := ⟨true, true, 2⟩, witness := .side 11 2 true (1 : Int) },
  { depth := 7, child := ⟨false, true, 3⟩, witness := .side 11 4 true (1 : Int) },
  { depth := 7, child := ⟨true, true, 3⟩, witness := .side 11 4 true (1 : Int) },
  { depth := 7, child := ⟨false, true, 4⟩, witness := .side 11 3 true (1 : Int) },
  { depth := 7, child := ⟨true, true, 4⟩, witness := .side 11 3 true (1 : Int) },
  { depth := 7, child := ⟨false, true, 5⟩, witness := .side 12 1 true (2 : Int) },
  { depth := 7, child := ⟨true, false, 5⟩, witness := .side 9 4 true (-1 : Int) },
  { depth := 7, child := ⟨true, true, 5⟩, witness := .side 12 1 true (2 : Int) },
  { depth := 8, child := ⟨false, true, 0⟩, witness := .side 5 11 true (-2 : Int) },
  { depth := 8, child := ⟨true, false, 0⟩, witness := .side 24 20 false (1 : Int) },
  { depth := 8, child := ⟨true, true, 0⟩, witness := .side 10 9 true (0 : Int) },
  { depth := 8, child := ⟨false, false, 1⟩, witness := .side 1 14 false (2 : Int) },
  { depth := 8, child := ⟨true, false, 1⟩, witness := .side 30 18 false (0 : Int) },
  { depth := 8, child := ⟨true, true, 1⟩, witness := .side 22 26 false (4 : Int) },
  { depth := 8, child := ⟨false, true, 2⟩, witness := .side 2 13 true (-2 : Int) },
  { depth := 8, child := ⟨true, false, 2⟩, witness := .side 24 19 true (-4 : Int) },
  { depth := 8, child := ⟨true, true, 2⟩, witness := .side 34 22 false (3 : Int) },
  { depth := 8, child := ⟨false, false, 3⟩, witness := .side 17 18 false (2 : Int) },
  { depth := 8, child := ⟨false, true, 3⟩, witness := .side 24 23 true (-4 : Int) },
  { depth := 8, child := ⟨true, true, 3⟩, witness := .side 13 2 true (0 : Int) },
  { depth := 8, child := ⟨false, false, 4⟩, witness := .side 8 8 true (-2 : Int) },
  { depth := 8, child := ⟨false, true, 5⟩, witness := .side 9 6 true (-1 : Int) },
  { depth := 8, child := ⟨true, false, 5⟩, witness := .side 67 72 false (0 : Int) },
  { depth := 8, child := ⟨true, true, 5⟩, witness := .side 9 6 true (-1 : Int) }
]

theorem fWitnessesOK : fWitnesses.all
    (fun w => residualWitnessOK (fChild w.depth w.child) w.witness) = true := by decide

def fClosed (i : Fin 9) (mv : Move) : Bool :=
  fWitnesses.any fun w => decide (w.depth = i ∧ w.child = mv)

theorem fClosed_sound (i : Fin 9) (mv : Move) (h : fClosed i mv = true) :
    ∀ m, compatible (fChild i mv) m → NeverHalts m := by
  unfold fClosed at h
  rcases List.any_eq_true.mp h with ⟨w, hw, hpair⟩
  have hOK := (List.all_eq_true.mp fWitnessesOK) w hw
  have hpair' : w.depth = i ∧ w.child = mv := of_decide_eq_true hpair
  rcases hpair' with ⟨rfl,rfl⟩
  exact residualWitnessOK_sound (fChild i mv) w.witness hOK

/-- Explicit complement independent of the unresolved large clock proof. -/
def fRemaining : List (Fin 9 × Move) :=
  (List.finRange 9).flatMap fun i =>
    (allMoves.filter fun mv => decide (mv ≠ fNextMove i) && !(fClosed i mv)).map
      fun mv => (i,mv)

theorem fRemainingCount : fRemaining.length = 148 := by decide

def FDisposition (B : Nat) (m : Machine) : Prop :=
  WeightedBound B m ∨ ∃ e ∈ fRemaining, compatible (fChild e.1 e.2) m

/-- One full partition step: early halt, continuation, checked nonhalter,
    or explicitly retained ordinary sibling. -/
theorem fStep (B : Nat) (hB : 20 ≤ B) (i : Fin 9)
    (hnext : ∀ m, compatible (fNextParent i) m → FDisposition B m) :
    ∀ m, compatible (fParent i) m → FDisposition B m := by
  intro m hm
  have hu : fParent i (readSlot (fConfig i)) = none := by
    rw [fReadSlot i]
    exact fHoleProof i
  have hf : fParent i initialSlot = some (some ⟨true,true,1⟩) := by
    fin_cases i <;> decide
  have href := compatible_refine (fParent i) m (fHole i) hm
  cases ht : m (fHole i) with
  | none =>
    left
    apply first_hole_weighted_halt B (fParent i) (fRunLength i)
      (fConfig i) hf (fRunKnown i) hu
    · intro d hd
      have hd6 : d < 6 := by
        unfold possibleDelays at hd
        exact List.mem_range.mp (List.mem_filter.mp hd).1
      have hn : fRunLength i ≤ 14 := by fin_cases i <;> decide
      omega
    · rw [fReadSlot i]
      simpa [ht] using href
  | some mv =>
    have hc : compatible (fChild i mv) m := by
      simpa [fChild,ht] using href
    by_cases hn : mv = fNextMove i
    · subst mv
      have he : fChild i (fNextMove i) = fNextParent i := by
        fin_cases i <;> rfl
      exact hnext m (he ▸ hc)
    · by_cases hs : fClosed i mv = true
      · exact Or.inl (weighted_never B m (fClosed_sound i mv hs m hc))
      · right
        refine ⟨(i,mv), ?_, hc⟩
        apply List.mem_flatMap.mpr
        refine ⟨i, List.mem_finRange i, ?_⟩
        apply List.mem_map.mpr
        refine ⟨mv, List.mem_filter.mpr ⟨allMoves_complete mv, ?_⟩, rfl⟩
        simp [hn,hs]

theorem fResidualSound (B : Nat) (hB : fMoves+1 ≤ B)
    (hclock : HaltsAfter fLiteral fMoves) :
    ∀ m, compatible fResidual m → FDisposition B m := by
  have h20 : 20 ≤ B := by unfold fMoves at hB; omega
  exact fStep B h20 0 (fStep B h20 1 (fStep B h20 2 (fStep B h20 3 (fStep B h20 4 (fStep B h20 5 (fStep B h20 6 (fStep B h20 7 (fStep B h20 8 (fun m hm =>
    Or.inl (fFinalSound B hB hclock m hm))))))))))

theorem fResidualRetained : reducedRoster.any (fun e => sameTable e.2 fResidual) = true := by decide

theorem fResidualUnique :
    (reducedRoster.filter fun e => sameTable e.2 fResidual).length = 1 := by decide

/-- Consume the refined parent at the attained champion score.
    Every one of the other 108 roster obligations is preserved; each of the
    148 unresolved siblings is a separate explicit premise. -/
theorem exactOfF412Graft
    (hclock : HaltsAfter fLiteral fMoves) (hB : fMoves+1 ≤ championScore)
    (hOther : ∀ e ∈ reducedRoster, sameTable e.2 fResidual = false →
      Cover (WeightedBound championScore) e.2)
    (hLeaves : ∀ e ∈ fRemaining,
      Cover (WeightedBound championScore) (fChild e.1 e.2)) :
    BB6.Coverage.ExactBB6 championScore := by
  apply exact_from_reduced_roster_at_champion_score
  intro e he
  cases hs : sameTable e.2 fResidual with
  | false => exact hOther e he hs
  | true =>
    have hEq := sameTable_sound hs
    rw [hEq]
    apply Cover.leaf
    intro m hm
    rcases fResidualSound championScore hB hclock m hm with hb | ⟨r,hr,hc⟩
    · exact hb
    · exact (hLeaves r hr).sound m hc

#print axioms fWitnessesOK
#print axioms fRemainingCount
#print axioms fFinalSound
#print axioms fResidualSound
#print axioms fResidualRetained
#print axioms exactOfF412Graft

end BB6.Agent26F412Graft
