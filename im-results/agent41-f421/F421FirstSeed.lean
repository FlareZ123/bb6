import F421CompressedRoot
import F421SeedTrace

namespace BB6Coverage.Agent41F421.Compressed
open BB6Coverage Agent31Pump Agent50Zipper EpochWords

/-- The left suffix untouched by the first secondary epoch, including padding. -/
def firstSuffix : List Piece :=
  [qRun 1,pRun 159,zeroPair,pRun 355,.run ⟨true,true⟩ 1,zeroPair,
    pRun 112,.run ⟨true,true⟩ 1,zeroPair,qRun 1,.run ⟨false,false⟩ 973]

theorem firstSeedShape :
    firstSeed.word = sbody 2047 3071 1703916 262124 firstPrimary firstTail (spell firstSuffix) := by
  have hp : firstSeed = pack (seedPieces 2047 3071 1703916 262124 firstPrimary firstTail firstSuffix) := rfl
  rw [hp,packWord,seedPiecesWord]

/-- Every completion of F1 follows the certified blank-start run to odd 190. -/
theorem blankFirstSeed (m : Machine) (hm : compatible table m) :
    ∃ n pos, 24+seedBound ≤ n ∧ run m n blank =
      some (embed ⟨3,pos,sbody 2047 3071 1703916 262124 firstPrimary firstTail (spell firstSuffix),[true]⟩) := by
  have h := blankFollow m hm 1024 seedBound firstSeed.word seedTrace
  simpa only [firstSeedShape] using h

/-- Name the exact deterministic secondary frontier symbolically. -/
def secondaryZeroWord (n a b x y : Nat) (cs : List PC) (xs : List TC) (u : List Bool) : List Bool :=
  let e := sIter n (a,b,cs)
  sbody e.1 e.2.1 (x-n) (y-n) e.2.2 (sTailFinal xs) u

theorem secondaryZeroReach (n a b x y : Nat) (cs : List PC) (xs : List TC) (u : List Bool)
    (hp : sPrimary n a b cs) (hx : n+3≤x) (hy : n+2≤y) (hc : counter xs=n) (hg : stailGood xs) :
    reaches n (sbody a b x y cs xs u) (secondaryZeroWord n a b x y cs xs u) := by
  have h := secondaryEpochExact n a b x y cs xs u hp hx hy hc hg
  exact h.2.2.2.2

/-- The source machine also completes the next 32750 secondary cycles. -/
theorem blankFirstSecondaryZero (m : Machine) (hm : compatible table m) :
    ∃ n pos, 24+seedBound+32750 ≤ n ∧ run m n blank =
      some (embed ⟨3,pos,secondaryZeroWord 32750 2047 3071 1703916 262124 firstPrimary firstTail
        (spell firstSuffix),[true]⟩) := by
  obtain ⟨n,p,hn,hroot⟩ := blankFirstSeed m hm
  have h := secondaryZeroReach 32750 2047 3071 1703916 262124 firstPrimary firstTail (spell firstSuffix)
    firstPrimaryGood (by decide) (by decide) (by decide) (by simp [stailGood,firstTail,counter,bit])
  obtain ⟨k,pos,hk,hr⟩ := followFrontier m hm n 32750 p _ _ hroot h
  exact ⟨k,pos,by omega,hr⟩

#print axioms blankFirstSeed
#print axioms blankFirstSecondaryZero
end BB6Coverage.Agent41F421.Compressed
