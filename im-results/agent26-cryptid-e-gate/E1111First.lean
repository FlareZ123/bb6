import Lean.Elab.Tactic.Omega
import E1111ThenE
import PrefixENoFSource

namespace BB6.Agent26EFourFirst

open CryptidBoundary
open BB6.Agent26EFour
open BB6.CryptidPrefixFirstReturn

set_option maxHeartbeats 10000000
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def NoFLocal (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t<n → (run t c).st ≠ 5

private theorem appendNoF (c d : Cfg) (a b : Nat)
    (hc : NoFLocal c a) (he : run a c = d) (hd : NoFLocal d b) :
    NoFLocal c (a+b) := by
  intro t ht
  by_cases hs : t < a
  · exact hc t hs
  · have htime : t = a+(t-a) := by omega
    rw [htime,run_add,he]
    exact hd (t-a) (by omega)

/-- The entire 17-step E/1111 fixed turn avoids the state F. -/
theorem eFour17_noF (m : Nat) (ys : List Bool) :
    NoFLocal (eFour m ys) 17 := by
  intro t ht
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 ∨ t=4 ∨ t=5 ∨ t=6 ∨ t=7 ∨ t=8 ∨ t=9 ∨ t=10 ∨ t=11 ∨ t=12 ∨ t=13 ∨ t=14 ∨ t=15 ∨ t=16 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp [eFour,run,step,goL,goR,pairs]

private theorem cWalk_noF (n : Nat) (L ys : List Bool) :
    NoFLocal (cWalk n L ys) (2*n) := by
  induction n generalizing ys with
  | zero => intro t ht; omega
  | succ n ih =>
      have ht : 2*(n+1)=2+2*n := by omega
      rw [ht]
      apply appendNoF (cWalk (n+1) L ys)
        (cWalk n L (true::true::ys)) 2 (2*n)
      · intro t hlt
        have hc : t=0 ∨ t=1 := by omega
        rcases hc with rfl | rfl
        all_goals simp [cWalk,oppairs,run,step,goL,goR]
      · exact cWalk_step n L ys
      · exact ih (true::true::ys)

private theorem cFour4_noF (ys : List Bool) :
    NoFLocal (⟨[false,true,true],true,ys,2⟩ : Cfg) 4 := by
  intro t ht
  have hc : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by omega
  rcases hc with rfl | rfl | rfl | rfl
  all_goals simp [run,step,goL,goR]

/-- Stronger than first physical return: the E/1111 boundary never
    visits F at any time before its declared endpoint. -/
theorem eFour_firstF (m : Nat) (ys : List Bool) :
    NoFLocal (eFour m ys) (2*m+23) := by
  have ht : 2*m+23=17+(2*(m+1)+4) := by omega
  rw [ht]
  apply appendNoF (eFour m ys)
    (cWalk (m+1) [false,true,true] (restTail ys))
    17 (2*(m+1)+4)
  · exact eFour17_noF m ys
  · exact eFour17 m ys
  · apply appendNoF
      (cWalk (m+1) [false,true,true] (restTail ys))
      (⟨[false,true,true],true,
        List.replicate (2*(m+1)) true ++ restTail ys,2⟩ : Cfg)
      (2*(m+1)) 4
    · exact cWalk_noF (m+1) [false,true,true] (restTail ys)
    · exact cWalk_run (m+1) [false,true,true] (restTail ys)
    · exact cFour4_noF _

/-- For every k and arbitrary finite suffix, this is the exact first
    positive-time F-state return, hence first physical F/0 return. -/
theorem full_E_four_first_return (k : Nat) (ys : List Bool) :
    let duration := 12*k*k+49*k+58
    let initial := init (List.replicate (3*k+2) true ++
       false :: ([true,true,true,true] ++ ys))
    run duration initial =
      ⟨[],false,
        [true,true,true,true] ++
          (List.replicate (2*((4*k+1)+1)) true ++ restTail ys),5⟩
    ∧ ∀ t, 0<t → t<duration → (run t initial).st ≠ 5 := by
  dsimp
  constructor
  · exact full_E_four k ys
  · intro t hpos hlt
    by_cases hbefore : t<12*k*k+41*k+33
    · exact prefixE_positive_noF k ([true,true,true,true]++ys)
        t hpos hbefore
    · have hprefix :
        run (12*k*k+41*k+33)
          (init (List.replicate (3*k+2) true ++
            false :: ([true,true,true,true]++ys))) =
          eFour (4*k+1) ys := by
            rw [prefix_E]
            rfl
      have htime :
          t = (12*k*k+41*k+33) +
            (t-(12*k*k+41*k+33)) := by omega
      have hrest :
          t-(12*k*k+41*k+33)<2*(4*k+1)+23 := by omega
      rw [htime,run_add,hprefix]
      exact eFour_firstF (4*k+1) ys
        (t-(12*k*k+41*k+33)) hrest

#print axioms eFour17_noF
#print axioms eFour_firstF
#print axioms full_E_four_first_return

end BB6.Agent26EFourFirst
