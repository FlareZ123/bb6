import Raw139LocalCore
import ChampionScoreLowerBound
import ChampionParentExact
import ChampionRemainingCover
import Raw139C1Batch
import F0Counter0LE
import F0SiblingLong
import F0Counter1RD
import F0SiblingA
import F0Sibling1RB
import Champion0RACover
import Agent14OneLDCover
import Agent14OneRFCover
import Raw139D0LFCover
import Raw139D0LBCover
import Raw139D0LACover
import Raw139SiblingSources
import Raw139D0OneLFCover
import Raw139D0ZeroRCCover
import Raw139D0OneRFCover
import Raw139D0ZeroRACover
import Raw139D0ZeroRFCover
import Agent41F1ZeroLFCover
import Agent41F1ZeroRCCover
import ChampionF1ZeroRFCover
import ChampionF1ZeroRD
import ChampionF1OneLACover
import ChampionF1OneLFCover

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace BB6.Agent14Raw139NormalizedLocalAccepted

open BB6Coverage
open BB6.Agent13BlankDelay
open BB6.Agent14Raw139Core
open BB6.Agent38ChampionThreshold
open BB6ChampionArithmetic

/-- The attained champion score, kept as a local name so this module does not
    import any historical canonical roster. -/
abbrev localScore : Nat := proposedTM63Moves + 7

theorem localScore_ge_6766859 : 6766859 ≤ localScore :=
  champion_score_ge_6766859

/-- Lift any already source-proved finite weighted cylinder bound below the
    accepted champion floor to the attained score. -/
theorem liftWeighted {b : Nat} {p : PartialMachine}
    (hb : b ≤ 6766859)
    (h : ∀ m, compatible p m → WeightedBound b m) :
    Cover (WeightedBound localScore) p := by
  refine Cover.leaf p ?_
  intro m hm k d hk hd
  exact Nat.le_trans
    (h m hm k d hk hd)
    (Nat.le_trans hb localScore_ge_6766859)

/-- Thirteen direct D0/F1 source parents used by the old 43-sibling join.
    This inventory contains only physical partial tables. -/
def sourceParents13 : List PartialMachine := [
  BB6.Agent14Raw139D0LF.parent,
  BB6.Agent14Raw139D0LB.parent,
  BB6.Agent14Raw139D0LA.parent,
  BB6.Agent14F1OneLD.parent,
  BB6.Agent14F1OneRF.parent,
  BB6.Agent41F1ZeroRB.parent,
  BB6.Agent14F1OneLA.parent,
  BB6.Agent14F1OneLB.parent,
  BB6.Agent14F1OneRD.parent,
  BB6.Agent14Raw139D0OneLF.parent,
  BB6.Agent14Raw139D0ZeroRC.parent,
  BB6.Agent14Raw139D0OneRF.parent,
  BB6.Agent14Raw139D0ZeroRA.parent]

theorem sourceParents13_cover (p : PartialMachine) (hp : p ∈ sourceParents13) :
    Cover (WeightedBound localScore) p := by
  simp only [sourceParents13, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
  · exact liftWeighted (by decide : 352 ≤ 6766859)
      BB6.Agent14Raw139D0LF.all_completions_weighted
  · exact liftWeighted (by decide : 7252 ≤ 6766859)
      BB6.Agent14Raw139D0LB.all_completions_weighted
  · exact liftWeighted (by decide : 1361 ≤ 6766859)
      BB6.Agent14Raw139D0LA.all_completions_weighted
  · exact liftWeighted (by decide : 264 ≤ 6766859)
      BB6.Agent14F1OneLD.all_completions_weighted
  · exact liftWeighted (by decide : 5423 ≤ 6766859)
      BB6.Agent14F1OneRF.all_completions_weighted
  · exact liftWeighted (by decide : 290 ≤ 6766859)
      BB6.Agent41F1ZeroRB.all_completions_weighted
  · exact liftWeighted (by decide : 553 ≤ 6766859)
      BB6.Agent14F1OneLA.all_completions_weighted
  · exact liftWeighted (by decide : 172 ≤ 6766859)
      BB6.Agent14F1OneLB.all_completions_weighted
  · exact liftWeighted (by decide : 489 ≤ 6766859)
      BB6.Agent14F1OneRD.all_completions_weighted
  · exact liftWeighted (by decide : 42038 ≤ 6766859)
      BB6.Agent14Raw139D0OneLF.all_completions_weighted
  · exact liftWeighted (by decide : 775 ≤ 6766859)
      BB6.Agent14Raw139D0ZeroRC.all_completions_weighted
  · exact liftWeighted (by decide : 6250 ≤ 6766859)
      BB6.Agent14Raw139D0OneRF.all_completions_weighted
  · exact liftWeighted (by decide : 8840 ≤ 6766859)
      BB6.Agent14Raw139D0ZeroRA.all_completions_weighted

/-- The ten original F0 parents plus the accepted F0=0RA parent. -/
def f0Parents11 : List PartialMachine := [
  BB6.Agent6F0.parent ⟨true,false,0⟩,
  BB6.Agent6F0.parent ⟨true,false,4⟩,
  BB6.Agent6F0.parent ⟨false,false,1⟩,
  BB6.Agent6F0.parent ⟨true,false,2⟩,
  BB6.Agent6F0.parent ⟨false,false,2⟩,
  BB6.Agent6F0.parent ⟨true,true,2⟩,
  BB6.Agent6F0.parent ⟨false,false,4⟩,
  BB6.Agent6F0.parent ⟨true,true,3⟩,
  BB6.Agent6F0.parent ⟨true,false,3⟩,
  BB6.Agent6F0.parent ⟨true,true,1⟩,
  BB6.Agent6F0.parent ⟨false,true,0⟩]

theorem f0Parents11_cover (p : PartialMachine) (hp : p ∈ f0Parents11) :
    Cover (WeightedBound localScore) p := by
  have hfloor : 49394 ≤ localScore := by
    have h := localScore_ge_6766859
    omega
  simp only [f0Parents11, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl
  · exact BB6.Agent6F0.cover_oneLA localScore (by omega)
  · exact BB6.Agent6F0.cover_oneLE localScore (by omega)
  · exact BB6.Agent6F0.cover_zeroLB localScore
  · exact BB6.Agent6F0.cover_oneLC localScore
  · exact BB6.Agent6F0.Counter0LC.cover_zeroLC localScore
  · exact BB6.Agent6F0.Long.cover_oneRC localScore hfloor
  · exact BB6.Agent6F0.Counter0LE.cover_zeroLE localScore
  · exact BB6.Agent6F0.Counter1RD.cover_oneRD localScore
  · exact BB6.Agent6F0.AFirst.cover_oneLD localScore (by omega)
  · exact BB6.Agent6F0.Sibling1RB.cover_oneRB localScore (by omega)
  · exact BB6.Agent48RA.cover_zeroRA localScore (by omega)

/-- Six further direct F1 parents used by the normalized accepted-row audit. -/
def f1Parents6 : List PartialMachine := [
  BB6.Agent41F1ZeroLF.parent,
  BB6.Agent41F1ZeroRC.parent,
  BB6.Agent48F1ZeroRF.parent,
  BB6.Agent48F1ZeroRD.ctr,
  BB6.Agent48F1OneLA.parent,
  BB6.Agent48F1OneLF.parent]

theorem f1Parents6_cover (p : PartialMachine) (hp : p ∈ f1Parents6) :
    Cover (WeightedBound localScore) p := by
  simp only [f1Parents6, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl
  · exact liftWeighted (by decide : 1603 ≤ 6766859)
      BB6.Agent41F1ZeroLF.all_completions_weighted
  · exact liftWeighted (by decide : 3807 ≤ 6766859)
      BB6.Agent41F1ZeroRC.all_completions_weighted
  · exact liftWeighted (by decide : 211 ≤ 6766859)
      BB6.Agent48F1ZeroRF.all_completions_weighted
  · exact BB6.Agent48F1ZeroRD.cover localScore
  · exact liftWeighted (by decide : 290 ≤ 6766859)
      BB6.Agent48F1OneLA.all_completions_weighted
  · exact liftWeighted (by decide : 126 ≤ 6766859)
      BB6.Agent48F1OneLF.all_completions_weighted

def matchesAny (p : PartialMachine) (ps : List PartialMachine) : Bool :=
  ps.any (fun q => sameTable p q)

/-- Roster-independent exact source-parent membership for the same 43
    normalized accepted addresses as the historical global join. -/
def acceptedCoverHit (p : PartialMachine) : Bool :=
  matchesAny p sourceParents13 ||
  matchesAny p BB6.Agent48Raw139C1Batch.parents ||
  matchesAny p f0Parents11 ||
  sameTable p BB6.Agent14Raw139D0ZeroRF.parent ||
  matchesAny p f1Parents6

theorem acceptedRowsCovered :
    ∀ r ∈ acceptedRows, acceptedCoverHit (child r.1 r.2) = true := by
  decide

theorem matchesAny_witness {p : PartialMachine} {ps : List PartialMachine}
    (h : matchesAny p ps = true) :
    ∃ q ∈ ps, sameTable p q = true := by
  simpa [matchesAny] using List.any_eq_true.mp h

theorem acceptedRowCover (r : Fin 7 × Move) (hr : r ∈ acceptedRows) :
    Cover (WeightedBound localScore) (child r.1 r.2) := by
  have h := acceptedRowsCovered r hr
  simp [acceptedCoverHit] at h
  rcases h with hSource | hC1 | hF0 | hD0ZeroRF | hF1
  · rcases matchesAny_witness hSource with ⟨p, hp, hSame⟩
    rw [sameTable_sound hSame]
    exact sourceParents13_cover p hp
  · rcases matchesAny_witness hC1 with ⟨p, hp, hSame⟩
    rw [sameTable_sound hSame]
    exact BB6.Agent48Raw139C1Batch.cover_at
      (by have hfloor := localScore_ge_6766859; omega) p hp
  · rcases matchesAny_witness hF0 with ⟨p, hp, hSame⟩
    rw [sameTable_sound hSame]
    exact f0Parents11_cover p hp
  · rw [sameTable_sound hD0ZeroRF]
    exact liftWeighted (by decide : 9110 ≤ 6766859)
      BB6.Agent14Raw139D0ZeroRF.all_completions_weighted
  · rcases matchesAny_witness hF1 with ⟨p, hp, hSame⟩
    rw [sameTable_sound hSame]
    exact f1Parents6_cover p hp

theorem acceptedRowsCover :
    ∀ r ∈ acceptedRows,
      Cover (WeightedBound localScore) (child r.1 r.2) := by
  intro r hr
  exact acceptedRowCover r hr

/-- The two normalized exceptional continuations use only their direct
    source-level continuation contracts. -/
theorem rowRC_lift
    (h : Cover (WeightedBound localScore) (leaf rowRC)) :
    Cover (WeightedBound localScore) (child rowRC.1 rowRC.2) := by
  have hEq :
      sameTable (leaf rowRC)
        (BB6.Agent6F0.AFirst.childA ⟨false, true, 2⟩ ⟨false, true, 3⟩) = true := by
    decide
  rw [sameTable_sound hEq] at h
  have hParentEq :
      sameTable (child rowRC.1 rowRC.2)
        (BB6.Agent6F0.parent ⟨false, true, 2⟩) = true := by
    decide
  have hParent :
      Cover (WeightedBound localScore)
        (BB6.Agent6F0.parent ⟨false, true, 2⟩) :=
    BB6.Agent48Remaining.cover_zeroRC_of_RD localScore
      (by have hfloor := localScore_ge_6766859; omega) h
  rw [sameTable_sound hParentEq]
  exact hParent

theorem rowRE_lift
    (h : Cover (WeightedBound localScore) (leaf rowRE)) :
    Cover (WeightedBound localScore) (child rowRE.1 rowRE.2) := by
  have hEq :
      sameTable (leaf rowRE)
        (BB6.Agent6F0.child ⟨true, true, 4⟩ ⟨false, true, 3⟩) = true := by
    decide
  rw [sameTable_sound hEq] at h
  have hParentEq :
      sameTable (child rowRE.1 rowRE.2)
        (BB6.Agent6F0.parent ⟨true, true, 4⟩) = true := by
    decide
  have hParent :
      Cover (WeightedBound localScore)
        (BB6.Agent6F0.parent ⟨true, true, 4⟩) :=
    BB6.Agent48Remaining.cover_oneRE_of_RD localScore
      (by have hfloor := localScore_ge_6766859; omega) h
  rw [sameTable_sound hParentEq]
  exact hParent

/-- The normalized terminal p7 table is exactly the independently accepted
    two-hole champion parent. No global canonical roster is involved. -/
theorem p7_eq_championParent :
    sameTable p7 BB6.Agent48Parent.parent = true := by
  decide

theorem p7_cover : Cover (WeightedBound localScore) p7 := by
  rw [sameTable_sound p7_eq_championParent]
  exact BB6.Agent48ChampionCylinder.champion_parent_exact_cover

/-- Roster-independent Raw139 refinement: Covers for the 67 normalized
    unresolved tables imply a Cover of the normalized Raw139 root p0 at the
    attained champion score. -/
theorem raw139_cover_after_accepted_local
    (hLeaves : ∀ p ∈ remainingTables,
      Cover (WeightedBound localScore) p) :
    Cover (WeightedBound localScore) p0 :=
  raw139_cover localScore
    (by have hfloor := localScore_ge_6766859; omega)
    acceptedRowsCover hLeaves rowRC_lift rowRE_lift p7_cover

#print axioms localScore_ge_6766859
#print axioms liftWeighted
#print axioms sourceParents13_cover
#print axioms f0Parents11_cover
#print axioms f1Parents6_cover
#print axioms acceptedRowsCovered
#print axioms acceptedRowCover
#print axioms acceptedRowsCover
#print axioms rowRC_lift
#print axioms rowRE_lift
#print axioms p7_eq_championParent
#print axioms p7_cover
#print axioms raw139_cover_after_accepted_local

end BB6.Agent14Raw139NormalizedLocalAccepted
