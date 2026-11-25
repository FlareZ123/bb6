import WeightedTNFCertificate
import SideCycle

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent26F412Graft
open BB6Coverage BB6.Agent13BlankDelay BB6Coverage.Agent50SideCycle

/-- Canonical raw-10 residual: A0=1RB, B0=1LC. -/
def fRoot : PartialMachine := refine emptyTable initialSlot (some ⟨true,true,1⟩)

def fResidual : PartialMachine := refine fRoot (1, false) (some ⟨true,false,2⟩)

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
def fConfig (i : Fin 9) : Config :=
  (knownRun (fParent i) (fRunLength i)).getD blank

theorem fRunKnown (i : Fin 9) :
    knownRun (fParent i) (fRunLength i) = some (fConfig i) := by
  have hsome :
      (knownRun (fParent i) (fRunLength i)).isSome = true := by
    revert i; decide
  unfold fConfig
  cases h : knownRun (fParent i) (fRunLength i) with
  | none => simp [h] at hsome
  | some c => simp [h]

theorem fReadSlot (i : Fin 9) :
    readSlot (fConfig i) = fHole i := by
  revert i; decide

theorem fHoleProof (i : Fin 9) :
    fParent i (fHole i) = none := by
  revert i; decide


/-- The full literal table; E1 is the only absent transition. -/
def fLiteral : Machine := weightedTNFDefaultCompletion fP9

def fMoves : Nat := 9217091204829760959746640857348768637582782

theorem fFinalNoAssignedHalt : weightedTNFNoAssignedHalt fP9 := by
  intro s
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;> decide

theorem fFinalUniqueHole {s : Slot} (h : fP9 s = none) : s = (4, true) := by
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;>
    simp [fP9,fP8,fP7,fP6,fP5,fP4,fP3,fP2,fP1,fResidual,fRoot,refine,emptyTable] at h ⊢

theorem fFinalOtherSlots (s : Slot) (h : s ≠ (4,true)) :
    ∃ mv, fP9 s = some (some mv) := by
  rcases s with ⟨q,b⟩
  have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by omega
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;> cases b <;>
    simp [fP9,fP8,fP7,fP6,fP5,fP4,fP3,fP2,fP1,fResidual,fRoot,refine,emptyTable] at h ⊢

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
  entry : Nat
  period : Nat
  right : Bool
  boundary : Int

/-- Candidate certificates; accepted only if the existing source checker
    replays every one. All are positive-period half-line translation cycles. -/
def fWitnesses : List FWitness := [
  { depth := 0, child := ⟨false, false, 0⟩, entry := 0, period := 3, right := false, boundary := (1 : Int) },
  { depth := 1, child := ⟨false, false, 0⟩, entry := 0, period := 4, right := false, boundary := (1 : Int) },
  { depth := 1, child := ⟨true, true, 1⟩, entry := 1, period := 3, right := false, boundary := (1 : Int) },
  { depth := 1, child := ⟨false, false, 3⟩, entry := 3, period := 1, right := false, boundary := (-1 : Int) },
  { depth := 1, child := ⟨true, false, 3⟩, entry := 3, period := 1, right := false, boundary := (-1 : Int) },
  { depth := 2, child := ⟨false, false, 0⟩, entry := 0, period := 5, right := false, boundary := (1 : Int) },
  { depth := 2, child := ⟨false, false, 3⟩, entry := 3, period := 2, right := true, boundary := (-1 : Int) },
  { depth := 2, child := ⟨false, false, 4⟩, entry := 4, period := 1, right := false, boundary := (0 : Int) },
  { depth := 2, child := ⟨true, false, 4⟩, entry := 4, period := 1, right := false, boundary := (0 : Int) },
  { depth := 3, child := ⟨false, false, 0⟩, entry := 0, period := 7, right := false, boundary := (1 : Int) },
  { depth := 3, child := ⟨false, true, 0⟩, entry := 0, period := 7, right := true, boundary := (-1 : Int) },
  { depth := 3, child := ⟨true, true, 1⟩, entry := 1, period := 6, right := true, boundary := (-1 : Int) },
  { depth := 3, child := ⟨true, false, 4⟩, entry := 4, period := 3, right := false, boundary := (1 : Int) },
  { depth := 4, child := ⟨false, false, 0⟩, entry := 0, period := 9, right := false, boundary := (1 : Int) },
  { depth := 4, child := ⟨false, false, 1⟩, entry := 7, period := 2, right := false, boundary := (-1 : Int) },
  { depth := 4, child := ⟨true, false, 1⟩, entry := 7, period := 2, right := false, boundary := (-1 : Int) },
  { depth := 4, child := ⟨false, false, 2⟩, entry := 8, period := 1, right := false, boundary := (-2 : Int) },
  { depth := 4, child := ⟨false, true, 2⟩, entry := 2, period := 7, right := false, boundary := (1 : Int) },
  { depth := 4, child := ⟨true, false, 2⟩, entry := 8, period := 1, right := false, boundary := (-2 : Int) },
  { depth := 4, child := ⟨true, true, 2⟩, entry := 5, period := 4, right := false, boundary := (1 : Int) },
  { depth := 4, child := ⟨false, false, 3⟩, entry := 3, period := 6, right := false, boundary := (1 : Int) },
  { depth := 4, child := ⟨false, true, 3⟩, entry := 6, period := 3, right := false, boundary := (0 : Int) },
  { depth := 4, child := ⟨true, false, 4⟩, entry := 4, period := 5, right := false, boundary := (1 : Int) },
  { depth := 5, child := ⟨false, false, 2⟩, entry := 5, period := 10, right := false, boundary := (1 : Int) },
  { depth := 5, child := ⟨true, false, 2⟩, entry := 2, period := 8, right := false, boundary := (1 : Int) },
  { depth := 5, child := ⟨false, false, 3⟩, entry := 6, period := 4, right := false, boundary := (0 : Int) },
  { depth := 5, child := ⟨false, true, 3⟩, entry := 1, period := 10, right := false, boundary := (1 : Int) },
  { depth := 5, child := ⟨true, false, 3⟩, entry := 6, period := 4, right := false, boundary := (0 : Int) },
  { depth := 6, child := ⟨false, false, 0⟩, entry := 5, period := 8, right := false, boundary := (1 : Int) },
  { depth := 6, child := ⟨false, true, 0⟩, entry := 0, period := 11, right := true, boundary := (-2 : Int) },
  { depth := 6, child := ⟨false, false, 1⟩, entry := 1, period := 10, right := false, boundary := (1 : Int) },
  { depth := 6, child := ⟨true, false, 1⟩, entry := 1, period := 10, right := false, boundary := (1 : Int) },
  { depth := 6, child := ⟨true, true, 1⟩, entry := 1, period := 16, right := false, boundary := (1 : Int) },
  { depth := 7, child := ⟨false, false, 0⟩, entry := 10, period := 3, right := true, boundary := (0 : Int) },
  { depth := 7, child := ⟨false, true, 2⟩, entry := 11, period := 2, right := true, boundary := (1 : Int) },
  { depth := 7, child := ⟨true, true, 2⟩, entry := 11, period := 2, right := true, boundary := (1 : Int) },
  { depth := 7, child := ⟨false, true, 3⟩, entry := 11, period := 4, right := true, boundary := (1 : Int) },
  { depth := 7, child := ⟨true, true, 3⟩, entry := 11, period := 4, right := true, boundary := (1 : Int) },
  { depth := 7, child := ⟨false, true, 4⟩, entry := 11, period := 3, right := true, boundary := (1 : Int) },
  { depth := 7, child := ⟨true, true, 4⟩, entry := 11, period := 3, right := true, boundary := (1 : Int) },
  { depth := 7, child := ⟨false, true, 5⟩, entry := 12, period := 1, right := true, boundary := (2 : Int) },
  { depth := 7, child := ⟨true, false, 5⟩, entry := 9, period := 4, right := true, boundary := (-1 : Int) },
  { depth := 7, child := ⟨true, true, 5⟩, entry := 12, period := 1, right := true, boundary := (2 : Int) },
  { depth := 8, child := ⟨false, true, 0⟩, entry := 5, period := 11, right := true, boundary := (-2 : Int) },
  { depth := 8, child := ⟨true, false, 0⟩, entry := 24, period := 20, right := false, boundary := (1 : Int) },
  { depth := 8, child := ⟨true, true, 0⟩, entry := 10, period := 9, right := true, boundary := (0 : Int) },
  { depth := 8, child := ⟨false, false, 1⟩, entry := 1, period := 14, right := false, boundary := (2 : Int) },
  { depth := 8, child := ⟨true, false, 1⟩, entry := 30, period := 18, right := false, boundary := (0 : Int) },
  { depth := 8, child := ⟨true, true, 1⟩, entry := 22, period := 26, right := false, boundary := (4 : Int) },
  { depth := 8, child := ⟨false, true, 2⟩, entry := 2, period := 13, right := true, boundary := (-2 : Int) },
  { depth := 8, child := ⟨true, false, 2⟩, entry := 24, period := 19, right := true, boundary := (-4 : Int) },
  { depth := 8, child := ⟨true, true, 2⟩, entry := 34, period := 22, right := false, boundary := (3 : Int) },
  { depth := 8, child := ⟨false, false, 3⟩, entry := 17, period := 18, right := false, boundary := (2 : Int) },
  { depth := 8, child := ⟨false, true, 3⟩, entry := 24, period := 23, right := true, boundary := (-4 : Int) },
  { depth := 8, child := ⟨true, true, 3⟩, entry := 13, period := 2, right := true, boundary := (0 : Int) },
  { depth := 8, child := ⟨false, false, 4⟩, entry := 8, period := 8, right := true, boundary := (-2 : Int) },
  { depth := 8, child := ⟨false, true, 5⟩, entry := 9, period := 6, right := true, boundary := (-1 : Int) },
  { depth := 8, child := ⟨true, false, 5⟩, entry := 67, period := 72, right := false, boundary := (0 : Int) },
  { depth := 8, child := ⟨true, true, 5⟩, entry := 9, period := 6, right := true, boundary := (-1 : Int) }
]

theorem fWitnessesOK : fWitnesses.all
    (fun w => decide (0 < w.period) && finiteSideCycleCheck
      (fChild w.depth w.child) w.entry w.period w.right w.boundary) = true := by decide

def fClosed (i : Fin 9) (mv : Move) : Bool :=
  fWitnesses.any fun w => decide (w.depth = i ∧ w.child = mv)

theorem fClosed_sound (i : Fin 9) (mv : Move) (h : fClosed i mv = true) :
    ∀ m, compatible (fChild i mv) m → NeverHalts m := by
  unfold fClosed at h
  rcases List.any_eq_true.mp h with ⟨w, hw, hpair⟩
  have hOK := (List.all_eq_true.mp fWitnessesOK) w hw
  have hpair' : w.depth = i ∧ w.child = mv := of_decide_eq_true hpair
  rcases hpair' with ⟨rfl,rfl⟩
  have hh := Bool.and_eq_true_iff.mp hOK
  exact finiteSideCycleCheck_sound (fChild i mv) w.entry w.period w.right w.boundary
    (of_decide_eq_true hh.1) hh.2

def fAllMoves : List Move := choices.filterMap id

theorem fAllMoves_complete (mv : Move) : mv ∈ fAllMoves := by
  apply List.mem_filterMap.mpr
  exact ⟨some mv, choices_complete (some mv), rfl⟩

/-- Explicit complement independent of the unresolved large clock proof. -/
def fRemaining : List (Fin 9 × Move) :=
  (List.finRange 9).flatMap fun i =>
    (fAllMoves.filter fun mv => decide (mv ≠ fNextMove i) && !(fClosed i mv)).map
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
    revert i; decide
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
      have hn : fRunLength i ≤ 14 := by revert i; decide
      omega
    · rw [fReadSlot i]
      simpa [ht] using href
  | some mv =>
    have hc : compatible (fChild i mv) m := by
      simpa [fChild,ht] using href
    by_cases hn : mv = fNextMove i
    · subst mv
      have he : fChild i (fNextMove i) = fNextParent i := by
        have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 := by omega
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      exact hnext m (he ▸ hc)
    · by_cases hs : fClosed i mv = true
      · exact Or.inl (weighted_never B m (fClosed_sound i mv hs m hc))
      · right
        refine ⟨(i,mv), ?_, hc⟩
        apply List.mem_flatMap.mpr
        refine ⟨i, List.mem_finRange i, ?_⟩
        apply List.mem_map.mpr
        refine ⟨mv, List.mem_filter.mpr ⟨fAllMoves_complete mv, ?_⟩, rfl⟩
        simp [hn,hs]

theorem fResidualSound (B : Nat) (hB : fMoves+1 ≤ B)
    (hclock : HaltsAfter fLiteral fMoves) :
    ∀ m, compatible fResidual m → FDisposition B m := by
  have h20 : 20 ≤ B := by unfold fMoves at hB; omega
  exact fStep B h20 0 (fStep B h20 1 (fStep B h20 2 (fStep B h20 3 (fStep B h20 4 (fStep B h20 5 (fStep B h20 6 (fStep B h20 7 (fStep B h20 8 (fun m hm =>
    Or.inl (fFinalSound B hB hclock m hm))))))))))


#print axioms fWitnessesOK
#print axioms fRemainingCount
#print axioms fFinalSound
#print axioms fResidualSound

end BB6.Agent26F412Graft
