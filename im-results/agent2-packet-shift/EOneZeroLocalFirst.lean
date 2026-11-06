import Lean.Elab.Tactic.Omega
import EOneZero
import EAltBoundaryFirst
import EDoubleTripleGeneral
import AIterDoubleZero

set_option maxHeartbeats 20000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

namespace BB6.Agent2EOneZeroLocalFirst
open CryptidBoundary
open BB6.Agent2EAltBoundaryFirst

private def NoF (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t<n → (run t c).st ≠ 5

private theorem nF_to_nP (c : Cfg) (n : Nat) :
    NoF c n → NoPhysical c n := by
  intro h t ht hp
  exact h t ht hp.1

private theorem appendNoF (c d : Cfg) (a b : Nat)
    (hc : NoF c a) (he : run a c = d) (hd : NoF d b) :
    NoF c (a+b) := by
  intro t ht
  by_cases hs : t<a
  · exact hc t hs
  · have heq : t=a+(t-a) := by omega
    rw [heq,run_add,he]
    exact hd (t-a) (by omega)

private theorem appendNoPhysical (c d : Cfg) (a b : Nat)
    (hc : NoPhysical c a) (he : run a c = d)
    (hd : NoPhysical d b) : NoPhysical c (a+b) := by
  intro t ht
  by_cases hs : t<a
  · exact hc t hs
  · have heq : t=a+(t-a) := by omega
    rw [heq,run_add,he]
    exact hd (t-a) (by omega)

private def aStart (r : Nat) (L ys : List Bool) : Cfg :=
  ⟨L,false,[true,false,true,true,false] ++
    (pairs r ++ (false::ys)),0⟩

private def aMarked (r : Nat) (L ys : List Bool) : Cfg :=
  ⟨[false,true,true,false,true] ++ L,false,
    pairs r ++ (false::ys),0⟩

private theorem firstNine (r : Nat) (L ys : List Bool) :
    run 9 (aStart r L ys) = aMarked r L ys := by
  simp [aStart,aMarked,run,step,goL,goR,pairs]

private theorem firstNineNoF (r : Nat) (L ys : List Bool) :
    NoF (aStart r L ys) 9 := by
  intro t ht
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [aStart,run,step,goL,goR,pairs]

private theorem tenTwoNoF (r : Nat) (L ys : List Bool) :
    NoF (⟨L,false,pairs (r+1) ++ ys,0⟩ : Cfg) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [run,step,goL,goR,pairs]

private theorem tenNoF (r : Nat) (L ys : List Bool) :
    NoF (⟨L,false,pairs r ++ ys,0⟩ : Cfg) (2*r) := by
  induction r generalizing L with
  | zero =>
      intro t ht
      omega
  | succ r ih =>
      have ht : 2*(r+1)=2+2*r := by omega
      rw [ht]
      apply appendNoF
        (⟨L,false,pairs (r+1) ++ ys,0⟩ : Cfg)
        (⟨[false,true]++L,false,pairs r ++ ys,0⟩ : Cfg)
        2 (2*r)
      · exact tenTwoNoF r L ys
      · simpa [pairs] using (aTenOppStep L (pairs r ++ ys))
      · exact ih ([false,true] ++ L)

private theorem zeroTwoNoF (L ys : List Bool) :
    NoF (⟨L,false,false::ys,0⟩ : Cfg) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [run,step,goL,goR]

private theorem walkTwoNoF (r : Nat) (L ys : List Bool) :
    NoF (cWalk (r+1) L ys) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [cWalk,oppairs,run,step,goL,goR]

private theorem walkNoF (r : Nat) (L ys : List Bool) :
    NoF (cWalk r L ys) (2*r) := by
  induction r generalizing ys with
  | zero =>
      intro t ht
      omega
  | succ r ih =>
      have ht : 2*(r+1) = 2+2*r := by omega
      rw [ht]
      apply appendNoF
        (cWalk (r+1) L ys)
        (cWalk r L (true::true::ys)) 2 (2*r)
      · exact walkTwoNoF r L ys
      · exact cWalk_step r L ys
      · exact ih (true::true::ys)

private theorem markedFiveNoPhysical (L ys : List Bool) :
    NoPhysical
      (⟨[false,true,true,false,true] ++ L,true,ys,2⟩ : Cfg) 5 := by
  intro t ht hp
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals simp [Physical,run,step,goL,goR] at hp

/-- The exact source-checked all-left/all-right A/0-to-E/1
    10110(10)^r0Y turn has NO earlier physically blank-left F/0 visit.
    Its last internal F/0 visit has a nonzero left marker. -/
theorem a_one_zero_noPhysical (r : Nat) (L ys : List Bool) :
    NoPhysical (aStart r L ys) (4*r+16) := by
  let marked : List Bool := [false,true,true,false,true] ++ L
  let c0 : Cfg := aStart r L ys
  let c1 : Cfg := aMarked r L ys
  let c2 : Cfg := ⟨oppairs r ++ marked,false,false::ys,0⟩
  let c3 : Cfg := ⟨oppairs r ++ marked,true,true::ys,2⟩
  let c4 : Cfg := ⟨marked,true,List.replicate (2*r) true ++ (true::ys),2⟩
  have h1 : run 9 c0 = c1 := firstNine r L ys
  have h2 : run (2*r) c1 = c2 := by
    dsimp [c1,c2,aMarked,marked]
    exact aTenOppIter r marked (false::ys)
  have h3 : run 2 c2 = c3 := by
    dsimp [c2,c3]
    exact BB6.Agent2AIterDoubleZero.aZeroTwo
      (oppairs r ++ marked) ys
  have h4 : run (2*r) c3 = c4 := by
    dsimp [c3,c4]
    exact cWalk_run r marked (true::ys)
  have hnf0 : NoPhysical c0 9 :=
    nF_to_nP _ _ (firstNineNoF r L ys)
  have hnf1 : NoPhysical c1 (2*r) :=
    nF_to_nP _ _ (tenNoF r marked (false::ys))
  have hnf2 : NoPhysical c2 2 :=
    nF_to_nP _ _ (zeroTwoNoF (oppairs r ++ marked) ys)
  have hnf3 : NoPhysical c3 (2*r) :=
    nF_to_nP _ _ (walkNoF r marked (true::ys))
  have hnf4 : NoPhysical c4 5 :=
    markedFiveNoPhysical L (List.replicate (2*r) true ++ (true::ys))
  have hjoined : NoPhysical c0
      (9+(2*r+(2+(2*r+5)))) :=
    appendNoPhysical c0 c1 9 (2*r+(2+(2*r+5)))
      hnf0 h1
      (appendNoPhysical c1 c2 (2*r) (2+(2*r+5))
        hnf1 h2
        (appendNoPhysical c2 c3 2 (2*r+5)
          hnf2 h3
          (appendNoPhysical c3 c4 (2*r) 5 hnf3 h4 hnf4)))
  have ht : 9+(2*r+(2+(2*r+5)))=4*r+16 := by omega
  simpa [c0,ht] using hjoined

#print axioms a_one_zero_noPhysical
end BB6.Agent2EOneZeroLocalFirst
