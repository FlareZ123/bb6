import EPositiveSimplified
import NoEarlierF
import Lean.Elab.Tactic.Omega
namespace BB6.Agent36PositiveFirst
open CryptidBoundary
open BB6.Agent36PositiveDoubleZero
open BB6.CryptidFirstReturn
set_option maxHeartbeats 12000000
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false

/-- Physical F/0, including list representations padded with blank zeros. -/
def PhysicalF0 (c : Cfg) : Prop :=
  c.st = 5 ∧ c.h = false ∧ c.l.any id = false
def NoPhysical (c : Cfg) (n : Nat) : Prop :=
  ∀ t, t<n → ¬ PhysicalF0 (run t c)

theorem join (c d : Cfg) (a b : Nat)
    (hc : NoPhysical c a) (he : run a c = d)
    (hd : NoPhysical d b) : NoPhysical c (a+b) := by
  intro t ht
  by_cases small : t<a
  · exact hc t small
  · have heq : t=a+(t-a) := by omega
    rw [heq,run_add,he]
    exact hd (t-a) (by omega)

theorem noF_noPhysical (c : Cfg) (n : Nat)
    (h : ∀ t, t<n → (run t c).st ≠ 5) : NoPhysical c n := by
  intro t ht hp
  exact h t ht hp.1

theorem eTwoNoPhysical (m q r : Nat) (ys : List Bool) :
    NoPhysical (input m q r ys) 2 := by
  intro t ht hp
  have cases : t=0 ∨ t=1 := by omega
  rcases cases with rfl | rfl
  all_goals simp [PhysicalF0,input,run,step,goL,goR,core,pairs] at hp
#print axioms join
#print axioms eTwoNoPhysical
end BB6.Agent36PositiveFirst
