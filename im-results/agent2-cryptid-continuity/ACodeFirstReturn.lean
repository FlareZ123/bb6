import Lean.Elab.Tactic.Omega
import ABridgeCode
import ATenFirstReturn

namespace BB6.CryptidACodeFirstReturn
open CryptidBoundary
open BB6.Agent35
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn
open BB6.CryptidATenFirstReturn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

/-- No F state in the alternate original-state-5-halts-on-1 interpreter.
    The exact source-model simulation is supplied by Agent35 toA_run. -/
def AltNoF (c : CryptidA.Cfg) (n : Nat) : Prop :=
  ∀ t, t<n → (CryptidA.run t c).state ≠ 5

private theorem appendAltNoF (c d : CryptidA.Cfg) (a b : Nat)
    (hc : AltNoF c a) (he : CryptidA.run a c = d)
    (hd : AltNoF d b) : AltNoF c (a+b) := by
  intro t ht
  by_cases hshort : t<a
  · exact hc t hshort
  · have htime : t=a+(t-a) := by omega
    rw [htime,CryptidA.run_add,he]
    exact hd (t-a) (by omega)

private theorem init8_noF (m : Nat) (ys : List Bool) :
    AltNoF (CryptidA.ab m ([true,true,true]++ys)) 8 := by
  intro t ht
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [CryptidA.ab,CryptidA.run,CryptidA.step,
    CryptidA.goR,CryptidA.goL,CryptidA.pat]

private theorem bloop4_noF (m k : Nat) (ys : List Bool) :
    AltNoF (CryptidA.bphase (m+1) k ys) 4 := by
  intro t ht
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals simp [CryptidA.bphase,CryptidA.run,CryptidA.step,
    CryptidA.goR,CryptidA.goL,CryptidA.pat,CryptidA.rightPat]

private theorem bwalk_noF (m k : Nat) (ys : List Bool) :
    AltNoF (CryptidA.bphase m k ys) (4*m) := by
  induction m generalizing k with
  | zero =>
    intro t ht
    omega
  | succ m ih =>
    have htime : 4*(m+1)=4+4*m := by omega
    rw [htime]
    exact appendAltNoF
      (CryptidA.bphase (m+1) k ys)
      (CryptidA.bphase m (k+1) ys)
      4 (4*m) (bloop4_noF m k ys)
      (CryptidA.b_loop m k ys) (ih (k+1))

private theorem btail8_noF (k : Nat) (ys : List Bool) :
    AltNoF (CryptidA.bphase 0 k ys) 8 := by
  intro t ht
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [CryptidA.bphase,CryptidA.run,CryptidA.step,
    CryptidA.goR,CryptidA.goL,CryptidA.pat,CryptidA.rightPat]

private theorem middle10_noF (n : Nat) (ys : List Bool) :
    AltNoF (CryptidA.lphase n ys) 10 := by
  intro t ht
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨
      t=6 ∨ t=7 ∨ t=8 ∨ t=9 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [CryptidA.lphase,CryptidA.run,CryptidA.step,
    CryptidA.goR,CryptidA.goL,CryptidA.rightPat]

private theorem right7_noF (n : Nat) (ys : List Bool) :
    AltNoF (CryptidA.rphase n ys) 7 := by
  cases n with
  | zero =>
    intro t ht
    have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [CryptidA.rphase,CryptidA.run,CryptidA.step,
      CryptidA.goR,CryptidA.goL,CryptidA.rightPat]
  | succ n =>
    intro t ht
    have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 := by omega
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [CryptidA.rphase,CryptidA.run,CryptidA.step,
      CryptidA.goR,CryptidA.goL,CryptidA.rightPat]

private theorem aloop2_noF (m n : Nat) (ys : List Bool) :
    AltNoF (CryptidA.acursor m (n+1) ys) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [CryptidA.acursor,CryptidA.ab,CryptidA.run,
    CryptidA.step,CryptidA.goR,CryptidA.pat]

private theorem awalk_noF (m n : Nat) (ys : List Bool) :
    AltNoF (CryptidA.acursor m n ys) (2*n) := by
  induction n generalizing m with
  | zero =>
    intro t ht
    omega
  | succ n ih =>
    have htime : 2*(n+1)=2+2*n := by omega
    rw [htime]
    exact appendAltNoF
      (CryptidA.acursor m (n+1) ys)
      (CryptidA.acursor (m+1) n ys)
      2 (2*n) (aloop2_noF m n ys)
      (CryptidA.a_loop m n ys) (ih (m+1))

/-- Exact all-m, all-tail interval proof that the 111 A token never reaches
    state F during its complete 6m+41 primitive transition expansion. -/
theorem triple_noF (m : Nat) (ys : List Bool) :
    AltNoF (CryptidA.ab m ([true,true,true]++ys)) (6*m+41) := by
  have hA : AltNoF (CryptidA.acursor 0 (m+4) ys) (2*(m+4)) :=
    awalk_noF 0 (m+4) ys
  have hR : AltNoF (CryptidA.rphase (m+4) ys) (7+2*(m+4)) :=
    appendAltNoF
      (CryptidA.rphase (m+4) ys) (CryptidA.acursor 0 (m+4) ys)
      7 (2*(m+4)) (right7_noF (m+4) ys)
      (CryptidA.right_seven (m+4) ys) hA
  have hM : AltNoF (CryptidA.lphase (m+2) ys)
      (10+(7+2*(m+4))) :=
    appendAltNoF
      (CryptidA.lphase (m+2) ys) (CryptidA.rphase (m+4) ys)
      10 (7+2*(m+4)) (middle10_noF (m+2) ys)
      (CryptidA.middle_ten (m+2) ys) hR
  have hT : AltNoF (CryptidA.bphase 0 (m+1) ys)
      (8+(10+(7+2*(m+4)))) :=
    appendAltNoF
      (CryptidA.bphase 0 (m+1) ys) (CryptidA.lphase (m+2) ys)
      8 (10+(7+2*(m+4))) (btail8_noF (m+1) ys)
      (CryptidA.b_tail (m+1) ys) hM
  have hW : AltNoF (CryptidA.bphase m 1 ys)
      (4*m+(8+(10+(7+2*(m+4))))) :=
    appendAltNoF
      (CryptidA.bphase m 1 ys) (CryptidA.bphase 0 (m+1) ys)
      (4*m) (8+(10+(7+2*(m+4))))
      (bwalk_noF m 1 ys) (CryptidA.b_walk m 1 ys) hT
  have hI : AltNoF (CryptidA.ab m ([true,true,true]++ys))
      (8+(4*m+(8+(10+(7+2*(m+4)))))) :=
    appendAltNoF
      (CryptidA.ab m ([true,true,true]++ys)) (CryptidA.bphase m 1 ys)
      8 (4*m+(8+(10+(7+2*(m+4)))))
      (init8_noF m ys) (CryptidA.initial_eight m ys) hW
  have htime : 8+(4*m+(8+(10+(7+2*(m+4)))))=6*m+41 := by omega
  simpa only [htime] using hI

private theorem tenAlt_noF (m : Nat) (ys : List Bool) :
    AltNoF (CryptidA.ab m ([true,false]++ys)) 2 := by
  intro t ht
  have hc : t=0 ∨ t=1 := by omega
  rcases hc with rfl | rfl
  all_goals simp [CryptidA.ab,CryptidA.run,CryptidA.step,
    CryptidA.goR,CryptidA.goL]

/-- All binary token code words, with false->10 and true->111, avoid F
    until the final code symbol is completely consumed. -/
theorem word_noF (m : Nat) (ws ys : List Bool) :
    AltNoF (CryptidA.ab m (CryptidA.wordCode ws ++ ys))
      (CryptidA.wordCost m ws) := by
  induction ws generalizing m with
  | nil =>
    intro t ht
    simp [CryptidA.wordCost] at ht
  | cons b ws ih =>
    cases b with
    | false =>
      change AltNoF
        (CryptidA.ab m ([true,false]++(CryptidA.wordCode ws++ys)))
        (2+CryptidA.wordCost (m+1) ws)
      exact appendAltNoF
        (CryptidA.ab m ([true,false]++(CryptidA.wordCode ws++ys)))
        (CryptidA.ab (m+1) (CryptidA.wordCode ws++ys))
        2 (CryptidA.wordCost (m+1) ws)
        (tenAlt_noF m (CryptidA.wordCode ws++ys))
        (CryptidA.ten_pump m (CryptidA.wordCode ws++ys))
        (ih (m+1))
    | true =>
      change AltNoF
        (CryptidA.ab m ([true,true,true]++(CryptidA.wordCode ws++ys)))
        ((6*m+41)+CryptidA.wordCost (m+4) ws)
      exact appendAltNoF
        (CryptidA.ab m ([true,true,true]++(CryptidA.wordCode ws++ys)))
        (CryptidA.ab (m+4) (CryptidA.wordCode ws++ys))
        (6*m+41) (CryptidA.wordCost (m+4) ws)
        (triple_noF m (CryptidA.wordCode ws++ys))
        (CryptidA.triplet_pump m (CryptidA.wordCode ws++ys))
        (ih (m+4))

/-- Lift no-F for all mixed A codes into the actual original six-state
    transition table, using the exact source-to-visitor simulation. -/
theorem original_word_noF (m : Nat) (ws ys : List Bool) :
    NoF (aBoundary m (CryptidA.wordCode ws ++ ys))
      (CryptidA.wordCost m ws) := by
  intro t ht hF
  have htarget : (CryptidA.run t
      (CryptidA.ab m (CryptidA.wordCode ws++ys))).state ≠ 5 :=
    word_noF m ws ys t ht
  have hsource : (toA (run t
      (aBoundary m (CryptidA.wordCode ws++ys)))).state = 5 := by
    have hst : (run t
        (aBoundary m (CryptidA.wordCode ws++ys))).st=5 := hF
    simp [toA,hst]
  have heq := toA_run t (aBoundary m (CryptidA.wordCode ws++ys))
  rw [toA_aBoundary] at heq
  rw [heq] at hsource
  exact htarget hsource

private theorem appendNoF (c d : Cfg) (a b : Nat)
    (hc : NoF c a) (he : run a c = d) (hd : NoF d b) :
    NoF c (a+b) := by
  intro t ht
  by_cases hshort : t<a
  · exact hc t hshort
  · have htime : t=a+(t-a) := by omega
    rw [htime,run_add,he]
    exact hd (t-a) (by omega)

/-- Every mixed 10/111 A code followed by a zero closes at its first F state. -/
theorem aCodeClose_first (m : Nat) (ws ys : List Bool) :
    run (CryptidA.wordCost m ws +
      (2*(m+CryptidA.wordInc ws)+6))
      (aBoundary m (CryptidA.wordCode ws ++ false::ys)) =
        ⟨[],false,List.replicate (2*(m+CryptidA.wordInc ws)+5) true ++ ys,5⟩ ∧
    NoF (aBoundary m (CryptidA.wordCode ws ++ false::ys))
      (CryptidA.wordCost m ws+(2*(m+CryptidA.wordInc ws)+6)) := by
  have hc : aBoundary (m+CryptidA.wordInc ws) (false::ys) =
      aBound (m+CryptidA.wordInc ws) (false::ys) := rfl
  have he : run (CryptidA.wordCost m ws)
      (aBoundary m (CryptidA.wordCode ws ++ false::ys)) =
        aBound (m+CryptidA.wordInc ws) (false::ys) := by
    rw [a_code_return]
    rfl
  constructor
  · rw [run_add,he]
    exact (aClose_first (m+CryptidA.wordInc ws) ys).1
  · exact appendNoF
      (aBoundary m (CryptidA.wordCode ws ++ false::ys))
      (aBound (m+CryptidA.wordInc ws) (false::ys))
      (CryptidA.wordCost m ws)
      (2*(m+CryptidA.wordInc ws)+6)
      (original_word_noF m ws (false::ys))
      he (aClose_first (m+CryptidA.wordInc ws) ys).2

def mixedStart (k : Nat) (ws ys : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++
    false :: (CryptidA.wordCode ws ++ false::ys))

def mixedEnd (k : Nat) (ws ys : List Bool) : Cfg :=
  ⟨[],false,List.replicate (2*(4*k+3+CryptidA.wordInc ws)+5) true ++ ys,5⟩

/-- Original raw D-start source: exact earliest physical F0 return after
    arbitrary finite mixed 10/111 A code, with all k and arbitrary tail. -/
theorem full_A_mixed_code_first_return (k : Nat) (ws ys : List Bool) :
    let tm := (12*k*k+41*k+32)+
      (CryptidA.wordCost (4*k+3) ws +
        (2*(4*k+3+CryptidA.wordInc ws)+6))
    run tm (mixedStart k ws ys) = mixedEnd k ws ys ∧
    ∀ t, 0<t → t<tm →
      ¬IsPhysicalReturn (run t (mixedStart k ws ys)) := by
  dsimp
  constructor
  · have hprefix : run (12*k*k+41*k+32) (mixedStart k ws ys) =
        aBoundary (4*k+3) (CryptidA.wordCode ws ++ false::ys) := by
      change run (12*k*k+41*k+32)
        (init (List.replicate (3*k+1) true ++
          false::(CryptidA.wordCode ws ++ false::ys))) = _
      rw [prefix_A]
      rfl
    rw [run_add,hprefix]
    exact (aCodeClose_first (4*k+3) ws ys).1
  · intro t hpos ht hphys
    by_cases hpref : t<12*k*k+41*k+32
    · exact (prefixA_positive_noF k
        (CryptidA.wordCode ws ++ false::ys) t hpos hpref) hphys.1
    · have hprefix : run (12*k*k+41*k+32) (mixedStart k ws ys) =
          aBoundary (4*k+3) (CryptidA.wordCode ws ++ false::ys) := by
        change run (12*k*k+41*k+32)
          (init (List.replicate (3*k+1) true ++
            false::(CryptidA.wordCode ws ++ false::ys))) = _
        rw [prefix_A]
        rfl
      have htime : t=(12*k*k+41*k+32)+(t-(12*k*k+41*k+32)) := by omega
      have hrest : t-(12*k*k+41*k+32) <
          (CryptidA.wordCost (4*k+3) ws+
            (2*(4*k+3+CryptidA.wordInc ws)+6)) := by omega
      rw [htime,run_add,hprefix] at hphys
      exact (aCodeClose_first (4*k+3) ws ys).2
        (t-(12*k*k+41*k+32)) hrest hphys.1

#print axioms init8_noF
#print axioms triple_noF
#print axioms word_noF
#print axioms original_word_noF
#print axioms aCodeClose_first
#print axioms full_A_mixed_code_first_return
end BB6.CryptidACodeFirstReturn
