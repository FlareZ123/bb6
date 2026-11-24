import TM63DirectRootAttainment
import SparseBlankDelay
import TwoCylinder

namespace BB6Coverage.Agent48DirectRoot
open BB6Coverage
open BB6Coverage.Agent48Champion
open BB6ChampionArithmetic
open BB6.CoverageAdapter
open BB6.Agent13BlankDelay

private theorem transfer_halts {m : Machine} {n : Nat} (h : HaltsAfter m n) :
    BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw (toAgent13Raw m)) (n+1) := by
  have hnormalize (m : Machine) :
      BB6.Coverage.normalize (toAgent13Raw m) = toAgent13Machine m := by
    funext q b
    simp [BB6.Coverage.normalize, toAgent13Raw, BB6.Coverage.normalize_liftInstruction]
  change BB6.Coverage.HaltsAt
    (BB6.Coverage.tick (BB6.Coverage.normalize (toAgent13Raw m))) (n+1)
  rw [hnormalize]
  apply (halts_agree (toAgent13Machine m) n).mpr
  simpa only [toAgent8_toAgent13] using h

private theorem transfer_plus_seven {m : Machine} {n : Nat} (h : HaltsAfter m (n+6)) :
    BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw (toAgent13Raw m)) (n+7) := by
  simpa only [Nat.add_assoc] using transfer_halts h

/-- The literal named champion's score in the raw 28-choice semantics. -/
theorem champion_raw_halts_exact :
    BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw (toAgent13Raw championTable))
      (proposedTM63Moves+7) :=
  transfer_plus_seven champion_halts_exact

theorem champion_raw_witness : ∃ m : BB6.Coverage.RawMachine,
    BB6.Coverage.HaltsAt (BB6.Coverage.tickRaw m) (proposedTM63Moves+7) :=
  ⟨toAgent13Raw championTable, champion_raw_halts_exact⟩

private theorem rootSteps_le_score (rootSteps L n a b : Nat) :
    rootSteps ≤ threeSectionMoves rootSteps L n a b + 7 := by
  simp only [threeSectionMoves]
  omega

theorem champion_score_ge_six : 6 ≤ proposedTM63Moves+7 :=
  Eq.mp (congrArg (fun n : Nat => 6 ≤ n) threeSectionScore_root)
    (Nat.le_trans (by decide : 6 ≤ 27959) (rootSteps_le_score 27959 3 7 6 63))

/-- No extra blank delay can lead into the champion's initial state. -/
theorem champion_delays_exact : delays (zeroNext championTable) 0 = [0] := by decide

/-- The exact singleton champion is already decided even with blank-delay weights. -/
private theorem weighted_of_exact {n : Nat} (hh : HaltsAfter championTable (n+6)) :
    WeightedBound (n+7) championTable := by
  intro k d hk hd
  rw [champion_delays_exact] at hd
  have hd0 : d = 0 := by simpa using hd
  have htime : k = n+6 := halting_time_unique _ _ _ hk hh
  subst d
  rw [htime, Nat.zero_add, Nat.add_assoc]
  exact Nat.le_refl _

theorem champion_weighted_bound : WeightedBound (proposedTM63Moves+7) championTable :=
  weighted_of_exact champion_halts_exact

/-- The remaining upper bound alone implies the exact raw BB(6). -/
theorem exact_BB6_from_cover
    (cert : Cover (DecidedBelow (proposedTM63Moves+7)) emptyTable) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves+7) :=
  agent8_cover_gives_agent13_exact _ cert champion_raw_witness

/-- One weighted 1RB root cover suffices. No raw witness or score-size premise remains. -/
theorem exact_BB6_from_weighted_cover
    (cert : Cover (WeightedBound (proposedTM63Moves+7)) firstOneCylinder) :
    BB6.Coverage.ExactBB6 (proposedTM63Moves+7) := by
  refine ⟨champion_raw_witness, ?_⟩
  apply (universal_raw_upper_iff (proposedTM63Moves+7)).mp
  apply (upper_iff_weighted_first_one (proposedTM63Moves+7) champion_score_ge_six).mpr
  intro m hf
  exact cert.sound m ((compatible_refine_iff emptyTable m initialSlot rfl
    (some ⟨true,true,(1 : Fin 6)⟩)).mpr ⟨empty_compatible m,hf⟩)

#print axioms champion_raw_halts_exact
#print axioms champion_weighted_bound
#print axioms exact_BB6_from_cover
#print axioms exact_BB6_from_weighted_cover
end BB6Coverage.Agent48DirectRoot
