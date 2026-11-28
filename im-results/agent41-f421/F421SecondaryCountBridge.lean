import F421CappedLife
import F421SecondaryBlankFar

namespace F421SecondaryLifetimes
open BB6Coverage.Agent41F421.EpochWords

theorem cappedSlow_eq (k : Nat) (xs : List Nat) :
    F421CappedLife.slowIter k xs = lifeIter k xs := by
  induction k generalizing xs with
  | zero => rfl
  | succ k ih => exact ih (advance xs)

theorem iter_count (k : Nat) (xs : List Nat) :
    (F421CappedLife.iter k (F421CappedLife.encode k xs)).1 = (lifeIter k xs).length := by
  have h := congrArg Prod.fst (F421CappedLife.iter_encode k xs)
  change _ = (F421CappedLife.slowIter k xs).length at h
  rw [cappedSlow_eq] at h
  exact h

theorem firstLivesLength_of_count (hCount : (F421CappedLife.iter 32750 F421CappedLife.first).1=8215) :
    (lifeIter 32750 firstLives).length=8215 := by
  exact (iter_count 32750 firstLives).symm.trans hCount

theorem firstSecondaryCount_of_count (hCount : (F421CappedLife.iter 32750 F421CappedLife.first).1=8215) :
    (sIter 32750 (2047,3071,firstPrimary)).2.2.length=8217 := by
  obtain ⟨a,b,rest,he,hp⟩ := firstSecondaryFar
  have h := congrArg List.length hp
  simp only [pProjection,List.length_map,physicalPLength,firstLivesLength_of_count hCount] at h
  rw [he]
  simp [h]

end F421SecondaryLifetimes

namespace BB6Coverage.Agent41F421.Compressed
open BB6Coverage Agent31Pump Agent50Zipper EpochWords F421SecondaryLifetimes

theorem blankFirstSecondarySized_of_count (m : Machine) (hm : compatible table m)
    (hCount : (F421CappedLife.iter 32750 F421CappedLife.first).1=8215) :
    ∃ n pos a b, ∃ rest : List PC,
      24+seedBound+32750 ≤ n ∧
      run m n blank = some (embed ⟨3,pos,
        sbody a b 1671166 229374
          (⟨2818045,131073⟩::⟨6946811,2883586⟩::rest)
          (sTailFinal firstTail) (spell firstSuffix),[true]⟩) ∧
      rest.length=8215 ∧ pProjection rest=physicalP 4 (lifeIter 32750 firstLives) := by
  obtain ⟨n,pos,a,b,rest,hN,hRun,hP⟩:=blankFirstSecondaryFar m hm
  have H:=congrArg List.length hP
  simp only [pProjection,List.length_map,physicalPLength,firstLivesLength_of_count hCount] at H
  exact ⟨n,pos,a,b,rest,hN,hRun,H,hP⟩

#print axioms blankFirstSecondarySized_of_count
end BB6Coverage.Agent41F421.Compressed
