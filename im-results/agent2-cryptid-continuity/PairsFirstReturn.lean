import Lean.Elab.Tactic.Omega
import ACodeFirstReturn
import ABridgeTwo

namespace BB6.CryptidPairsFirstReturn
open CryptidBoundary
open BB6.Agent35
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn
open BB6.CryptidFirstReturn
open BB6.CryptidACodeFirstReturn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

private theorem appendNoF (c d : Cfg) (a b : Nat)
    (hc : NoF c a) (he : run a c = d) (hd : NoF d b) :
    NoF c (a+b) := by
  intro t ht
  by_cases hshort : t<a
  · exact hc t hshort
  · have htime : t=a+(t-a) := by omega
    rw [htime,run_add,he]
    exact hd (t-a) (by omega)

/-- All time indices of the pair scanner preceding a reversible A close. -/
private theorem scanner_noF (n : Nat) (L ys : List Bool) :
    NoF (scanStart n L ys) (2*n) := by
  induction n generalizing L ys with
  | zero =>
    intro t ht
    omega
  | succ n ih =>
    intro t ht
    by_cases hshort : t<2
    · have hc : t=0 ∨ t=1 := by omega
      rcases hc with rfl | rfl
      all_goals simp [scanStart,run,step,goL,goR,pairs]
    · have htime : t=2+(t-2) := by omega
      rw [htime,run_add,scan_step]
      exact ih ([false,true]++L) ys (t-2) (by omega)

private theorem ePairs_start_noF (m q : Nat) (ys : List Bool) :
    NoF (ePairs m q ys) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [ePairs,run,step,goL,goR,pairs]

private theorem aCloseStart_noF (n m : Nat) (ys : List Bool) :
    NoF (aCloseStart n m ys) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [aCloseStart,run,step,goL,goR,pairs,oppairs]

private theorem cWalk_two_noF (n : Nat) (L ys : List Bool) :
    NoF (cWalk (n+1) L ys) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [cWalk,run,step,goL,goR,oppairs]

private theorem cWalk_noF (n : Nat) (L ys : List Bool) :
    NoF (cWalk n L ys) (2*n) := by
  induction n generalizing ys with
  | zero =>
    intro t ht
    omega
  | succ n ih =>
    have htime : 2*(n+1)=2+2*n := by omega
    rw [htime]
    exact appendNoF
      (cWalk (n+1) L ys) (cWalk n L (true::true::ys))
      2 (2*n) (cWalk_two_noF n L ys)
      (cWalk_step n L ys) (ih (true::true::ys))

private theorem cBase_noF (m : Nat) (ys : List Bool) :
    NoF (⟨pairs (m+2) ++ [true,true],true,ys,2⟩ : Cfg) 4 := by
  intro t ht
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals simp [run,step,goL,goR,pairs]

/-- Each component of the symbolic E(10)^q0 bridge avoids F altogether. -/
theorem ePairs_toB_noF (m q : Nat) (ys : List Bool) :
    NoF (ePairs m q ys) (4*q+12) := by
  have hb : NoF (⟨pairs (m+2) ++ [true,true],true,
      List.replicate (2*(q+1)) true ++ (true::ys),2⟩ : Cfg) 4 :=
    cBase_noF m (List.replicate (2*(q+1)) true ++ (true::ys))
  have hc : NoF (cWalk (q+1) (pairs (m+2) ++ [true,true]) (true::ys))
      (2*(q+1)+4) := by
    have hsc : NoF (cWalk (q+1) (pairs (m+2) ++ [true,true]) (true::ys))
        (2*(q+1)) :=
      cWalk_noF (q+1) (pairs (m+2) ++ [true,true]) (true::ys)
    have he : run (2*(q+1))
        (cWalk (q+1) (pairs (m+2) ++ [true,true]) (true::ys)) =
        (⟨pairs (m+2) ++ [true,true],true,
          List.replicate (2*(q+1)) true ++ (true::ys),2⟩ : Cfg) :=
      cWalk_run (q+1) (pairs (m+2) ++ [true,true]) (true::ys)
    exact appendNoF _ _ (2*(q+1)) 4 hsc he hb
  have ha : NoF (aCloseStart (q+1) m ys)
      (2+(2*(q+1)+4)) :=
    appendNoF
      (aCloseStart (q+1) m ys)
      (cWalk (q+1) (pairs (m+2) ++ [true,true]) (true::ys))
      2 (2*(q+1)+4)
      (aCloseStart_noF (q+1) m ys)
      (aClose_two (q+1) m ys) hc
  have hscan : NoF
      (scanStart (q+1) (pairs (m+2) ++ [true,true]) (false::ys))
      (2*(q+1)+(2+(2*(q+1)+4))) := by
    have hs := scanner_noF (q+1) (pairs (m+2) ++ [true,true]) (false::ys)
    have he : run (2*(q+1))
      (scanStart (q+1) (pairs (m+2) ++ [true,true]) (false::ys)) =
      aCloseStart (q+1) m ys := by
      rw [scan_run]
      rfl
    exact appendNoF _ _ (2*(q+1)) (2+(2*(q+1)+4)) hs he ha
  have hi : NoF (ePairs m q ys)
      (2+(2*(q+1)+(2+(2*(q+1)+4)))) :=
    appendNoF
      (ePairs m q ys)
      (scanStart (q+1) (pairs (m+2) ++ [true,true]) (false::ys))
      2 (2*(q+1)+(2+(2*(q+1)+4)))
      (ePairs_start_noF m q ys) (ePairs_two m q ys) hscan
  have hn : 2+(2*(q+1)+(2+(2*(q+1)+4)))=4*q+12 := by omega
  simpa only [hn] using hi

/-- Original source: E(10)^q0 returns to F0 at its FIRST physical return,
    for every left-stack parameter and arbitrary finite suffix. -/
theorem ePairs_first_return (m q : Nat) (ys : List Bool) :
    run (2*m+4*q+15) (ePairs m q ys) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (false::List.replicate (2*q+6) true ++ ys),5⟩ ∧
    NoF (ePairs m q ys) (2*m+4*q+15) := by
  constructor
  · exact ePairs_run m q ys
  · have htime : 2*m+4*q+15=(4*q+12)+(2*m+3) := by omega
    rw [htime]
    have hb : NoF
        (sweepB m (false::List.replicate (2*q+6) true ++ ys))
        (2*m+3) := by
      intro t ht
      exact sweepB_firstF m (false::List.replicate (2*q+6) true ++ ys) t ht
    exact appendNoF
      (ePairs m q ys) (sweepB m (false::List.replicate (2*q+6) true ++ ys))
      (4*q+12) (2*m+3)
      (ePairs_toB_noF m q ys) (ePairs_toB m q ys) hb

private theorem aDouble_before3 (m : Nat) (ys : List Bool) :
    NoF (aBoundary (m+1) ([true,true,false,false]++ys)) 3 := by
  intro t ht
  have hc : t=0 ∨ t=1 ∨ t=2 := by omega
  rcases hc with rfl | rfl | rfl
  all_goals simp [aBoundary,run,step,goR,goL,pairs]

/-- The A 1100 branch is a source-certified FIRST return, not only endpoint. -/
theorem aDouble_first_return (m : Nat) (ys : List Bool) :
    run (2*m+18) (aBoundary (m+1) ([true,true,false,false]++ys)) =
      ⟨[],false,List.replicate (2*m+3) true ++
        (false::List.replicate 6 true++ys),5⟩ ∧
    NoF (aBoundary (m+1) ([true,true,false,false]++ys)) (2*m+18) := by
  constructor
  · exact a_double_return m ys
  · have htime : 2*m+18=3+(2*m+15) := by omega
    rw [htime]
    exact appendNoF
      (aBoundary (m+1) ([true,true,false,false]++ys))
      (ePairs m 0 ys)
      3 (2*m+15) (aDouble_before3 m ys)
      (a_double_to_E m ys) (ePairs_first_return m 0 ys).2

/-- Every coded A prelude may terminate with an exceptional 1100 A branch
    without a premature physical F0 return. -/
theorem aCodeDouble_first_return (m : Nat) (ws ys : List Bool) :
    run (CryptidA.wordCost (m+1) ws +
      (2*(m+CryptidA.wordInc ws)+18))
      (aBoundary (m+1) (CryptidA.wordCode ws ++
        ([true,true,false,false]++ys))) =
      ⟨[],false,List.replicate (2*(m+CryptidA.wordInc ws)+3) true ++
        (false::List.replicate 6 true++ys),5⟩ ∧
    NoF (aBoundary (m+1)
      (CryptidA.wordCode ws ++ ([true,true,false,false]++ys)))
      (CryptidA.wordCost (m+1) ws+(2*(m+CryptidA.wordInc ws)+18)) := by
  have he : run (CryptidA.wordCost (m+1) ws)
      (aBoundary (m+1) (CryptidA.wordCode ws ++
        ([true,true,false,false]++ys))) =
      aBoundary ((m+CryptidA.wordInc ws)+1)
        ([true,true,false,false]++ys) := by
    rw [a_code_return]
    have hn : m+1+CryptidA.wordInc ws =
        m+CryptidA.wordInc ws+1 := by omega
    rw [hn]
  constructor
  · rw [run_add,he]
    exact (aDouble_first_return (m+CryptidA.wordInc ws) ys).1
  · exact appendNoF
      (aBoundary (m+1)
        (CryptidA.wordCode ws ++ ([true,true,false,false]++ys)))
      (aBoundary ((m+CryptidA.wordInc ws)+1)
        ([true,true,false,false]++ys))
      (CryptidA.wordCost (m+1) ws)
      (2*(m+CryptidA.wordInc ws)+18)
      (original_word_noF (m+1) ws ([true,true,false,false]++ys))
      he (aDouble_first_return (m+CryptidA.wordInc ws) ys).2

/-- Original input source I_(3k+3)(0 Code(w) 1100 y) has its first physical
    F0 return at the exact Agent35 endpoint, for every arbitrary code/tail. -/
theorem full_A_code_double_first_return (k : Nat) (ws ys : List Bool) :
    let tm := (12*k*k+41*k+32)+
      (CryptidA.wordCost (4*k+3) ws+
        (2*(4*k+2+CryptidA.wordInc ws)+18))
    run tm (init (List.replicate (3*k+1) true ++
      false::(CryptidA.wordCode ws ++ ([true,true,false,false]++ys)))) =
      ⟨[],false,
        List.replicate (2*(4*k+2+CryptidA.wordInc ws)+3) true ++
          (false::List.replicate 6 true++ys),5⟩ ∧
    ∀ t, 0<t → t<tm →
      ¬IsPhysicalReturn (run t
        (init (List.replicate (3*k+1) true ++
          false::(CryptidA.wordCode ws ++ ([true,true,false,false]++ys))))) := by
  dsimp
  constructor
  · rw [run_add,prefix_A]
    change run _ (aBoundary (4*k+3)
      (CryptidA.wordCode ws ++ ([true,true,false,false]++ys))) = _
    have hn : 4*k+3=(4*k+2)+1 := by omega
    rw [hn]
    exact (aCodeDouble_first_return (4*k+2) ws ys).1
  · intro t hpos ht hphys
    by_cases hpref : t<12*k*k+41*k+32
    · exact (prefixA_positive_noF k
        (CryptidA.wordCode ws ++ ([true,true,false,false]++ys))
        t hpos hpref) hphys.1
    · have hprefix : run (12*k*k+41*k+32)
        (init (List.replicate (3*k+1) true ++
          false::(CryptidA.wordCode ws ++ ([true,true,false,false]++ys)))) =
        aBoundary (4*k+3)
          (CryptidA.wordCode ws ++ ([true,true,false,false]++ys)) := by
        rw [prefix_A]
        rfl
      have htime : t=(12*k*k+41*k+32)+(t-(12*k*k+41*k+32)) := by omega
      have hrest : t-(12*k*k+41*k+32) <
          CryptidA.wordCost (4*k+3) ws+
            (2*(4*k+2+CryptidA.wordInc ws)+18) := by omega
      rw [htime,run_add,hprefix] at hphys
      have hn : 4*k+3=(4*k+2)+1 := by omega
      rw [hn] at hphys
      exact (aCodeDouble_first_return (4*k+2) ws ys).2
        (t-(12*k*k+41*k+32)) hrest hphys.1

#print axioms ePairs_toB_noF
#print axioms ePairs_first_return
#print axioms aDouble_first_return
#print axioms aCodeDouble_first_return
#print axioms full_A_code_double_first_return
end BB6.CryptidPairsFirstReturn
