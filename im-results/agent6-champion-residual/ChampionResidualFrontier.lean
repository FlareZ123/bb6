import Combined109Roster
import MixedBound109Composition
import FourHoleResidualRoster
import WeightedTNFCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace BB6.Agent6ChampionResidual

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent31FourHoleFrontier
open BB6.Agent31FourHoleRoster
open BB6.Agent50TNFPilot
open BB6.Agent47Combined109
open BB6.Agent13MixedBound109
open BB6Coverage.Agent48Champion
open BB6Coverage.Agent48DirectRoot

/-- The champion-compatible canonical residual: A/0=1RB, B/0=1RC,
    C/0=1LD, with the other nine transitions still undefined. -/
def championRootAfterB : PartialMachine :=
  refine root (1, false) (some ⟨true, true, 2⟩)

def championResidual : PartialMachine :=
  refine championRootAfterB (2, false) (some ⟨true, false, 3⟩)

def rootConfig : Config := (knownRun root 1).getD blank

theorem rootRun : knownRun root 1 = some rootConfig := by
  have hsome : (knownRun root 1).isSome = true := by decide
  cases h : knownRun root 1 with
  | none => simp [h] at hsome
  | some c => simp [rootConfig, h]

theorem rootReadSlot : readSlot rootConfig = (1, false) := by decide

theorem rootHole : root (readSlot rootConfig) = none := by
  rw [rootReadSlot]
  decide

def championRootAfterBConfig : Config :=
  (knownRun championRootAfterB 2).getD blank

theorem championRootAfterBRun :
    knownRun championRootAfterB 2 = some championRootAfterBConfig := by
  have hsome : (knownRun championRootAfterB 2).isSome = true := by decide
  cases h : knownRun championRootAfterB 2 with
  | none => simp [h] at hsome
  | some c => simp [championRootAfterBConfig, h]

theorem championRootAfterBReadSlot :
    readSlot championRootAfterBConfig = (2, false) := by decide

theorem championRootAfterBHole :
    championRootAfterB (readSlot championRootAfterBConfig) = none := by
  rw [championRootAfterBReadSlot]
  decide

theorem championResidualPath : RawRootPath championResidual := by
  have hB : RawRootPath championRootAfterB := by
    have h := RawRootPath.step RawRootPath.root rootRun rootHole
      (⟨true, true, 2⟩ : Move)
    simpa [championRootAfterB, rootReadSlot] using h
  have h := RawRootPath.step hB championRootAfterBRun championRootAfterBHole
    (⟨true, false, 3⟩ : Move)
  simpa [championResidual, championRootAfterBReadSlot] using h

/-- The eight successive first-hole refinements along the champion's run. -/
def championP1 : PartialMachine :=
  refine championResidual (3, true) (some ⟨false, false, 4⟩)

def championP2 : PartialMachine :=
  refine championP1 (4, true) (some ⟨true, true, 2⟩)

def championP3 : PartialMachine :=
  refine championP2 (4, false) (some ⟨false, false, 3⟩)

def championP4 : PartialMachine :=
  refine championP3 (3, false) (some ⟨true, true, 0⟩)

def championP5 : PartialMachine :=
  refine championP4 (2, true) (some ⟨false, true, 5⟩)

def championP6 : PartialMachine :=
  refine championP5 (5, true) (some ⟨false, true, 4⟩)

def championP7 : PartialMachine :=
  refine championP6 (5, false) (some ⟨true, true, 0⟩)

def championP8 : PartialMachine :=
  refine championP7 (0, true) (some ⟨true, true, 0⟩)

def championParent (i : Fin 8) : PartialMachine :=
  match i.val with
  | 0 => championResidual
  | 1 => championP1
  | 2 => championP2
  | 3 => championP3
  | 4 => championP4
  | 5 => championP5
  | 6 => championP6
  | _ => championP7

def championNextParent (i : Fin 8) : PartialMachine :=
  match i.val with
  | 0 => championP1
  | 1 => championP2
  | 2 => championP3
  | 3 => championP4
  | 4 => championP5
  | 5 => championP6
  | 6 => championP7
  | _ => championP8

def championHole (i : Fin 8) : Slot :=
  match i.val with
  | 0 => (3, true)   -- D/1
  | 1 => (4, true)   -- E/1
  | 2 => (4, false)  -- E/0
  | 3 => (3, false)  -- D/0
  | 4 => (2, true)   -- C/1
  | 5 => (5, true)   -- F/1
  | 6 => (5, false)  -- F/0
  | _ => (0, true)   -- A/1

def championNextMove (i : Fin 8) : Move :=
  match i.val with
  | 0 => ⟨false, false, 4⟩ -- 0LE
  | 1 => ⟨true, true, 2⟩   -- 1RC
  | 2 => ⟨false, false, 3⟩ -- 0LD
  | 3 => ⟨true, true, 0⟩   -- 1RA
  | 4 => ⟨false, true, 5⟩  -- 0RF
  | 5 => ⟨false, true, 4⟩  -- 0RE
  | 6 => ⟨true, true, 0⟩   -- 1RA
  | _ => ⟨true, true, 0⟩   -- 1RA

def championRunLength (i : Fin 8) : Nat :=
  match i.val with
  | 0 => 3
  | 1 => 4
  | 2 => 7
  | 3 => 8
  | 4 => 11
  | 5 => 12
  | 6 => 53
  | _ => 213

def championConfig (i : Fin 8) : Config :=
  (knownRun (championParent i) (championRunLength i)).getD blank

theorem championRunKnown (i : Fin 8) :
    knownRun (championParent i) (championRunLength i) = some (championConfig i) := by
  have hsome :
      (knownRun (championParent i) (championRunLength i)).isSome = true := by
    fin_cases i <;> decide
  unfold championConfig
  cases h : knownRun (championParent i) (championRunLength i) with
  | none => simp [h] at hsome
  | some c => simp [h]

theorem championReadSlot (i : Fin 8) :
    readSlot (championConfig i) = championHole i := by
  fin_cases i <;> decide

theorem championHoleProof (i : Fin 8) :
    championParent i (championHole i) = none := by
  fin_cases i <;> decide

def championP1Path : RawRootPath championP1 := by
  have hh : championResidual (readSlot (championConfig 0)) = none := by
    rw [championReadSlot 0]
    exact championHoleProof 0
  have h := RawRootPath.step championResidualPath (championRunKnown 0) hh
    (championNextMove 0)
  rw [championReadSlot 0] at h
  simpa [championP1, championNextMove] using h

def championP2Path : RawRootPath championP2 := by
  have hh : championP1 (readSlot (championConfig 1)) = none := by
    rw [championReadSlot 1]
    exact championHoleProof 1
  have h := RawRootPath.step championP1Path (championRunKnown 1) hh
    (championNextMove 1)
  rw [championReadSlot 1] at h
  simpa [championP2, championNextMove] using h

def championP3Path : RawRootPath championP3 := by
  have hh : championP2 (readSlot (championConfig 2)) = none := by
    rw [championReadSlot 2]
    exact championHoleProof 2
  have h := RawRootPath.step championP2Path (championRunKnown 2) hh
    (championNextMove 2)
  rw [championReadSlot 2] at h
  simpa [championP3, championNextMove] using h

def championP4Path : RawRootPath championP4 := by
  have hh : championP3 (readSlot (championConfig 3)) = none := by
    rw [championReadSlot 3]
    exact championHoleProof 3
  have h := RawRootPath.step championP3Path (championRunKnown 3) hh
    (championNextMove 3)
  rw [championReadSlot 3] at h
  simpa [championP4, championNextMove] using h

def championP5Path : RawRootPath championP5 := by
  have hh : championP4 (readSlot (championConfig 4)) = none := by
    rw [championReadSlot 4]
    exact championHoleProof 4
  have h := RawRootPath.step championP4Path (championRunKnown 4) hh
    (championNextMove 4)
  rw [championReadSlot 4] at h
  simpa [championP5, championNextMove] using h

def championP6Path : RawRootPath championP6 := by
  have hh : championP5 (readSlot (championConfig 5)) = none := by
    rw [championReadSlot 5]
    exact championHoleProof 5
  have h := RawRootPath.step championP5Path (championRunKnown 5) hh
    (championNextMove 5)
  rw [championReadSlot 5] at h
  simpa [championP6, championNextMove] using h

def championP7Path : RawRootPath championP7 := by
  have hh : championP6 (readSlot (championConfig 6)) = none := by
    rw [championReadSlot 6]
    exact championHoleProof 6
  have h := RawRootPath.step championP6Path (championRunKnown 6) hh
    (championNextMove 6)
  rw [championReadSlot 6] at h
  simpa [championP7, championNextMove] using h

def championP8Path : RawRootPath championP8 := by
  have hh : championP7 (readSlot (championConfig 7)) = none := by
    rw [championReadSlot 7]
    exact championHoleProof 7
  have h := RawRootPath.step championP7Path (championRunKnown 7) hh
    (championNextMove 7)
  rw [championReadSlot 7] at h
  simpa [championP8, championNextMove] using h

theorem championPath (i : Fin 8) : RawRootPath (championParent i) := by
  fin_cases i
  · exact championResidualPath
  · exact championP1Path
  · exact championP2Path
  · exact championP3Path
  · exact championP4Path
  · exact championP5Path
  · exact championP6Path
  · exact championP7Path

theorem rawRootPathNoAssignedHalt {p : PartialMachine}
    (path : RawRootPath p) : weightedTNFNoAssignedHalt p := by
  induction path with
  | root => decide
  | @step p n c mv parent hrun hhole ih =>
      exact weightedTNFNoAssignedHalt_refine p (readSlot c) mv ih

def championChild (i : Fin 8) (mv : Move) : PartialMachine :=
  refine (championParent i) (championHole i) (some mv)

def championChildPath (i : Fin 8) (mv : Move) :
    RawRootPath (championChild i mv) := by
  have hh : championParent i (readSlot (championConfig i)) = none := by
    rw [championReadSlot i]
    exact championHoleProof i
  have h := RawRootPath.step (championPath i) (championRunKnown i) hh mv
  rw [championReadSlot i] at h
  simpa [championChild] using h

structure ChampionWitness where
  depth : Fin 8
  child : Move
  witness : ResidualNonhaltWitness

/-- Candidate side-cycle/lasso witnesses found by bounded search.
    Every item is replayed by championWitnessesOK; the list is not trusted
    merely because the search found it. -/
def championWitnesses : List ChampionWitness :=
[
  { depth := 1, child := ⟨false, false, 0⟩, witness := .side 0 5 false (2 : Int) },

  { depth := 2, child := ⟨false, false, 0⟩, witness := .side 0 8 false (2 : Int) },
  { depth := 2, child := ⟨false, false, 1⟩, witness := .side 5 4 false (1 : Int) },
  { depth := 2, child := ⟨true, true, 2⟩, witness := .side 5 3 false (1 : Int) },

  { depth := 3, child := ⟨false, false, 0⟩, witness := .side 0 9 false (2 : Int) },
  { depth := 3, child := ⟨false, false, 1⟩, witness := .side 5 5 false (1 : Int) },
  { depth := 3, child := ⟨false, true, 1⟩, witness := .side 5 5 false (1 : Int) },
  { depth := 3, child := ⟨true, true, 1⟩, witness := .side 1 8 false (2 : Int) },
  { depth := 3, child := ⟨true, true, 2⟩, witness := .side 5 4 false (1 : Int) },
  { depth := 3, child := ⟨true, true, 3⟩, witness := .side 2 14 false (2 : Int) },
  { depth := 3, child := ⟨false, true, 4⟩, witness := .lasso 9 },
  { depth := 3, child := ⟨true, true, 4⟩, witness := .side 6 4 false (0 : Int) },

  { depth := 4, child := ⟨false, false, 3⟩, witness := .side 2 12 false (2 : Int) },
  { depth := 4, child := ⟨false, true, 3⟩, witness := .side 2 14 false (2 : Int) },
  { depth := 4, child := ⟨true, false, 3⟩, witness := .side 2 12 false (2 : Int) },
  { depth := 4, child := ⟨true, true, 3⟩, witness := .side 2 18 false (2 : Int) },
  { depth := 4, child := ⟨false, false, 4⟩, witness := .side 2 14 false (2 : Int) },
  { depth := 4, child := ⟨false, true, 4⟩, witness := .side 2 16 false (3 : Int) },
  { depth := 4, child := ⟨true, false, 4⟩, witness := .lasso 13 },

  { depth := 5, child := ⟨false, true, 0⟩, witness := .side 0 13 true (-2 : Int) },
  { depth := 5, child := ⟨false, false, 1⟩, witness := .side 2 18 false (2 : Int) },
  { depth := 5, child := ⟨true, true, 1⟩, witness := .side 2 20 false (4 : Int) },
  { depth := 5, child := ⟨false, false, 2⟩, witness := .side 2 14 false (2 : Int) },
  { depth := 5, child := ⟨true, false, 2⟩, witness := .side 2 14 false (2 : Int) },
  { depth := 5, child := ⟨true, true, 2⟩, witness := .side 2 16 false (3 : Int) },
  { depth := 5, child := ⟨false, false, 4⟩, witness := .side 2 14 false (2 : Int) },
  { depth := 5, child := ⟨true, false, 4⟩, witness := .side 2 14 false (2 : Int) },
  { depth := 5, child := ⟨true, true, 4⟩, witness := .side 2 16 false (3 : Int) }
]

theorem championWitnessesOK :
    championWitnesses.all
      (fun w => residualWitnessOK (championChild w.depth w.child) w.witness) = true := by
  decide

def championClosed (i : Fin 8) (mv : Move) : Bool :=
  championWitnesses.any fun w => decide (w.depth = i ∧ w.child = mv)

theorem championClosed_sound (i : Fin 8) (mv : Move)
    (h : championClosed i mv = true) :
    ∀ m, compatible (championChild i mv) m → NeverHalts m := by
  unfold championClosed at h
  rcases List.any_eq_true.mp h with ⟨w, hw, hpair⟩
  have hOK := (List.all_eq_true.mp championWitnessesOK) w hw
  have hpair' : w.depth = i ∧ w.child = mv := of_decide_eq_true hpair
  rcases hpair' with ⟨rfl, rfl⟩
  exact residualWitnessOK_sound (championChild i mv) w.witness hOK

def championChildCertificate (i : Fin 8) (mv : Move)
    (h : championClosed i mv = true) :
    WeightedTNFCertificate championScore (championChild i mv) 6 :=
  WeightedTNFCertificate.nonhalt
    (RawRootPath.rootRow (championChildPath i mv))
    (BB6.Agent50TNFPilot.support6 _)
    (rawRootPathNoAssignedHalt (championChildPath i mv))
    (championClosed_sound i mv h)

def championStep (i : Fin 8)
    (nextFrontier : RootedFrontier championScore (championNextParent i)) :
    RootedFrontier championScore (championParent i) := by
  let c := championConfig i
  have hrun : knownRun (championParent i) (championRunLength i) = some c := by
    simpa [c] using championRunKnown i
  have hhole : championParent i (readSlot c) = none := by
    rw [championReadSlot i]
    exact championHoleProof i
  have hweight :
      ∀ d ∈ possibleDelays
        (refine (championParent i) (readSlot c) none) 0,
          d + championRunLength i + 1 ≤ championScore := by
    intro d hd
    have hd6 : d < 6 := by
      unfold possibleDelays at hd
      exact List.mem_range.mp (List.mem_filter.mp hd).1
    have hroom : championRunLength i + 6 ≤ championScore := by
      fin_cases i <;> decide
    omega
  have hnext :
      refine (championParent i) (readSlot c) (some (championNextMove i)) =
        championNextParent i := by
    rw [championReadSlot i]
    fin_cases i <;> rfl
  refine RootedFrontier.expand (championPath i) hrun hhole hweight ?_
  intro mv
  by_cases hn : mv = championNextMove i
  · subst mv
    simpa [hnext] using nextFrontier
  · by_cases hc : championClosed i mv = true
    · have hp : RawRootPath
          (refine (championParent i) (readSlot c) (some mv)) := by
        simpa [championChild, championReadSlot i] using championChildPath i mv
      have hcert : WeightedTNFCertificate championScore
          (refine (championParent i) (readSlot c) (some mv)) 6 := by
        simpa [championChild, championReadSlot i] using
          championChildCertificate i mv hc
      exact RootedFrontier.closed hp hcert
    · exact RootedFrontier.residual (by
        simpa [championChild, championReadSlot i] using championChildPath i mv)

/-- The champion-compatible residual after the eight ordinary path refinements
    has exactly one missing row, B/1. Its default completion is the named
    champion, so the terminal halt is charged at the full champion score. -/
theorem championP8DefaultCompletion :
    weightedTNFDefaultCompletion championP8 = championTable := by
  funext s
  fin_cases s.1 <;> cases s.2 <;> decide

theorem championP8FirstHole :
    ∃ c, knownRun championP8 (proposedTM63Moves + 6) = some c ∧
      championP8 (readSlot c) = none := by
  apply (weightedTNF_halt_iff_firstHole championP8
    (rawRootPathNoAssignedHalt championP8Path)
    (proposedTM63Moves + 6)).mp
  rw [championP8DefaultCompletion]
  exact champion_halts_exact

noncomputable def championP8Config : Config :=
  Classical.choose championP8FirstHole

theorem championP8Run :
    knownRun championP8 (proposedTM63Moves + 6) = some championP8Config :=
  (Classical.choose_spec championP8FirstHole).1

theorem championP8Hole :
    championP8 (readSlot championP8Config) = none :=
  (Classical.choose_spec championP8FirstHole).2

theorem championP8UniqueHole {s : Slot}
    (h : championP8 s = none) : s = (1, true) := by
  fin_cases s.1 <;> cases s.2 <;>
    simp [championP8, championP7, championP6, championP5, championP4,
      championP3, championP2, championP1, championResidual,
      championRootAfterB, refine, root] at h ⊢

theorem championP8HoleSlot :
    readSlot championP8Config = (1, true) :=
  championP8UniqueHole championP8Hole

theorem championP8OtherSlots (s : Slot) (h : s ≠ (1, true)) :
    ∃ mv, championP8 s = some (some mv) := by
  fin_cases s.1 <;> cases s.2 <;>
    simp [championP8, championP7, championP6, championP5, championP4,
      championP3, championP2, championP1, championResidual,
      championRootAfterB, refine, root] at h ⊢

theorem championP8HRest :
    ∀ s, s ≠ readSlot championP8Config →
      ∃ mv, championP8 s = some (some mv) := by
  intro s hs
  have hneq : s ≠ (1, true) := by
    intro he
    subst s
    exact hs championP8HoleSlot.symm
  exact championP8OtherSlots s hneq

theorem championP8PossibleDelays :
    possibleDelays (refine championP8 (1, true) none) 0 = [0] := by
  have hfull :
      refine championP8 (1, true) none =
        (fun s => some (championTable s)) := by
    funext s
    fin_cases s.1 <;> cases s.2 <;> decide
  rw [hfull]
  decide

theorem championP8HWeight :
    ∀ d ∈ possibleDelays
      (refine championP8 (readSlot championP8Config) none) 0,
        d + (proposedTM63Moves + 6) + 1 ≤ championScore := by
  intro d hd
  rw [championP8HoleSlot, championP8PossibleDelays] at hd
  simp at hd
  subst d
  rfl

noncomputable def championP8Certificate :
    WeightedTNFCertificate championScore championP8 6 :=
  WeightedTNFCertificate.lastHole
    (RawRootPath.rootRow championP8Path)
    (BB6.Agent50TNFPilot.support6 _)
    (by decide)
    (rawRootPathNoAssignedHalt championP8Path)
    championP8Run
    championP8Hole
    championP8HRest
    championP8HWeight

/-- Eight source-replayed first-hole splits, with the exact champion terminal
    cylinder closed by lastHole at the attained score. -/
noncomputable def championFrontier : RootedFrontier championScore championResidual :=
  championStep 0
    (championStep 1
      (championStep 2
        (championStep 3
          (championStep 4
            (championStep 5
              (championStep 6
                (championStep 7
                  (RootedFrontier.closed championP8Path championP8Certificate))))))))

def championResidualResiduals :
    List (List Move × PartialMachine) :=
  RootedFrontier.residuals championFrontier

theorem championResidualResidualsCount :
    championResidualResiduals.length = 156 := by decide

theorem championResidualFrontierSound (m : Machine)
    (hm : compatible championResidual m) :
    WeightedBound championScore m ∨
      ∃ e ∈ championResidualResiduals, compatible e.2 m := by
  rcases RootedFrontier.sound championFrontier m hm with hB | ⟨address, q, hopen, hq⟩
  · exact Or.inl hB
  · exact Or.inr ⟨(address, q), OpenLeaf.mem_residuals hopen, hq⟩

/-- The 9-hole champion cylinder is one of the 109 retained root residuals. -/
def championResidualRetained : Bool :=
  reducedRoster.any fun e => sameTable e.2 championResidual

theorem championResidualRetainedTrue :
    championResidualRetained = true := by decide

theorem championResidualMemReducedRoster :
    ∃ e ∈ reducedRoster, e.2 = championResidual := by
  rcases List.any_eq_true.mp championResidualRetainedTrue with ⟨e, he, hs⟩
  exact ⟨e, he, sameTable_sound hs⟩

theorem championResidualUniqueInReducedRoster :
    (reducedRoster.filter fun e => sameTable e.2 championResidual).length = 1 := by
  decide

/-- Replace the champion-compatible 9-hole cylinder by its explicit
    source-checked frontier. The roster now has 108 untouched obligations
    and 156 smaller residual cylinders. -/
def championResidualRefinedRoster :
    List (List Move × PartialMachine) :=
  (reducedRoster.filter fun e => !(sameTable e.2 championResidual)) ++
    championResidualResiduals

theorem championResidualRefinedRosterCount :
    championResidualRefinedRoster.length = 264 := by decide

theorem championResidualRefinedRosterSound (m : Machine)
    (hm : compatible BB6.Agent50TNFPilot.root m) :
    WeightedBound championScore m ∨
      ∃ e ∈ championResidualRefinedRoster, compatible e.2 m := by
  rcases reduced_sound m hm with hB | ⟨e, he, hcomp⟩
  · exact Or.inl (by
      intro k d hk hd
      exact Nat.le_trans (hB k d hk hd) (Nat.le_of_lt champion_score_gt_7014))
  · by_cases hs : sameTable e.2 championResidual = true
    · have heq : e.2 = championResidual := sameTable_sound hs
      have hcomp' : compatible championResidual m := by
        simpa [heq] using hcomp
      rcases championResidualFrontierSound m hcomp' with hB' | ⟨residual, hresidual, hcompat⟩
      · exact Or.inl hB'
      · exact Or.inr ⟨residual,
          List.mem_append_right _ (OpenLeaf.mem_residuals hresidual), hcompat⟩
    · exact Or.inr ⟨e,
        List.mem_append_left _ (List.mem_filter.mpr ⟨he, by simp [hs]⟩),
        hcomp⟩

/-- Conditional exact BB(6) after replacing the champion-containing 109th
    cylinder by its checked first-hole frontier. -/
theorem exactBB6OfChampionResidualRoster
    (hLeaves : ∀ e ∈ championResidualRefinedRoster,
      Cover (WeightedBound championScore) e.2) :
    BB6.Coverage.ExactBB6 championScore :=
  BB6.Agent13RosterComposition.exact_from_roster_dichotomy_mixed
    (by decide)
    (Nat.le_of_lt champion_score_gt_7014)
    championResidualRefinedRosterSound
    hLeaves
    champion_raw_witness

#print axioms championWitnessesOK
#print axioms championP8Certificate
#print axioms championResidualFrontierSound
#print axioms championResidualRetainedTrue
#print axioms championResidualRefinedRosterSound
#print axioms exactBB6OfChampionResidualRoster

end BB6.Agent6ChampionResidual
