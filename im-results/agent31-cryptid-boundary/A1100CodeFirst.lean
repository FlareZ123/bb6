import Lean.Elab.Tactic.Omega
import A1100First
import ACodeFirstReturn

namespace BB6.CryptidA1100CodeFirst
open CryptidBoundary
open BB6.CryptidPrefixFirstReturn
open BB6.CryptidE111FirstReturn
open BB6.CryptidACodeFirstReturn

set_option maxHeartbeats 8000000
set_option maxRecDepth 4096

def packet (ys : List Bool) : List Bool :=
  true::true::false::false::ys

def codeStart (k : Nat) (ws ys : List Bool) : Cfg :=
  init (List.replicate (3*k+1) true ++
    false :: (CryptidA.wordCode ws ++ packet ys))

def codeTime (k : Nat) (ws : List Bool) : Nat :=
  (12*k*k+41*k+32) +
    (CryptidA.wordCost (4*k+3) ws +
       (2*(4*k+3+CryptidA.wordInc ws)+16))

theorem code_close (k : Nat) (ws ys : List Bool) :
    run (CryptidA.wordCost (4*k+3) ws +
       (2*(4*k+3+CryptidA.wordInc ws)+16))
      (CryptidBoundary.aBoundary (4*k+3)
        (CryptidA.wordCode ws ++ packet ys)) =
      ⟨[],false,List.replicate (2*(4*k+3+CryptidA.wordInc ws)+1) true ++
         (false::List.replicate 6 true ++ ys),5⟩ := by
  rw [run_add]
  have hcode : run (CryptidA.wordCost (4*k+3) ws)
      (CryptidBoundary.aBoundary (4*k+3)
        (CryptidA.wordCode ws ++ packet ys)) =
        CryptidBoundary.aBoundary (4*k+3+CryptidA.wordInc ws)
          (packet ys) :=
    BB6.Agent35.a_code_return (4*k+3) ws (packet ys)
  rw [hcode]
  have hm : (4*k+1+CryptidA.wordInc ws)+2 =
      4*k+3+CryptidA.wordInc ws := by omega
  have hs := a1100_run (4*k+1+CryptidA.wordInc ws) ys
  rw [hm] at hs
  exact hs

theorem code_close_noPhysical (k : Nat) (ws ys : List Bool)
    (t : Nat)
    (ht : t < CryptidA.wordCost (4*k+3) ws +
       (2*(4*k+3+CryptidA.wordInc ws)+16)) :
    ¬ Physical (run t
      (CryptidBoundary.aBoundary (4*k+3)
        (CryptidA.wordCode ws ++ packet ys))) := by
  by_cases hcode : t < CryptidA.wordCost (4*k+3) ws
  · intro h
    exact (original_word_noF (4*k+3) ws (packet ys) t hcode) h.1
  · obtain ⟨u,hu⟩ : ∃ u, t=CryptidA.wordCost (4*k+3) ws+u :=
        ⟨t-CryptidA.wordCost (4*k+3) ws,by omega⟩
    rw [hu,run_add]
    have hcodeeq : run (CryptidA.wordCost (4*k+3) ws)
      (CryptidBoundary.aBoundary (4*k+3)
        (CryptidA.wordCode ws ++ packet ys)) =
        CryptidBoundary.aBoundary (4*k+3+CryptidA.wordInc ws)
          (packet ys) :=
      BB6.Agent35.a_code_return (4*k+3) ws (packet ys)
    rw [hcodeeq]
    have hbound : u < 2*(4*k+3+CryptidA.wordInc ws)+16 := by omega
    have hm : (4*k+1+CryptidA.wordInc ws)+2 =
      4*k+3+CryptidA.wordInc ws := by omega
    have hno := a1100_first_physical
        (4*k+1+CryptidA.wordInc ws) ys u
        (by simpa only [hm] using hbound)
    rw [hm] at hno
    exact hno

/-- Arbitrary mixed 10/111 code followed by the exceptional 1100
  yields the first positive physical F/0 return, for all k, words and tails. -/
theorem full_A_code_1100_first_return (k : Nat) (ws ys : List Bool) :
    run (codeTime k ws) (codeStart k ws ys) =
      ⟨[],false,List.replicate (2*(4*k+3+CryptidA.wordInc ws)+1) true ++
         (false::List.replicate 6 true ++ ys),5⟩ ∧
    ∀ t, 0<t → t<codeTime k ws →
      ¬ IsPhysicalReturn (run t (codeStart k ws ys)) := by
  constructor
  · unfold codeTime codeStart
    rw [run_add, prefix_A]
    exact code_close k ws ys
  · intro t hpos ht hret
    by_cases hpre : t < 12*k*k+41*k+32
    · exact (prefixA_positive_noF k
        (CryptidA.wordCode ws ++ packet ys) t hpos hpre) hret.1
    · obtain ⟨u,hu⟩ : ∃ u, t=(12*k*k+41*k+32)+u :=
        ⟨t-(12*k*k+41*k+32),by omega⟩
      have hprefix : run (12*k*k+41*k+32) (codeStart k ws ys) =
          CryptidBoundary.aBoundary (4*k+3)
            (CryptidA.wordCode ws ++ packet ys) := by
        exact prefix_A k (CryptidA.wordCode ws ++ packet ys)
      have hret' : IsPhysicalReturn
          (run u (CryptidBoundary.aBoundary (4*k+3)
            (CryptidA.wordCode ws ++ packet ys))) := by
        simpa only [hu,run_add,hprefix] using hret
      have hbound : u < CryptidA.wordCost (4*k+3) ws +
       (2*(4*k+3+CryptidA.wordInc ws)+16) := by
        unfold codeTime at ht
        omega
      have hno := code_close_noPhysical k ws ys u hbound
      apply hno
      exact ⟨hret'.1, by simp [hret'.2.2]⟩

#print axioms code_close
#print axioms code_close_noPhysical
#print axioms full_A_code_1100_first_return
end BB6.CryptidA1100CodeFirst
