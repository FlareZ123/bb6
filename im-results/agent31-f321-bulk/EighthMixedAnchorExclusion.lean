import DangerWindowCriterion
import HighFarRootTargets
import Lean.Elab.Tactic.Omega

/-!
First application of the generic danger-window criterion: exact root exclusion
for the eighth dangerous H^(24k+22)/Far terminal anchor, k=7.
-/

set_option maxRecDepth 1200000

namespace BB6.Agent31F321EighthMixed
open BB6.Agent31F321Density
open BB6.Agent31F321FirstMixed
open BB6.Agent31F321HighFarRootTargets
open BB6.Agent31F321DangerWindow

theorem root_at_33035 :
    CounterReach 1 1 33035
      961393035615140673549516718710040875308440268606910406798
      1457498944512501642702467274440552173554525480555251475134 :=
  rootIter_sound (by decide)

theorem root_at_33036 :
    CounterReach 1 1 33036
      3845572142460562694198066874840163501233761074427641627198 2 :=
  rootIter_sound (by decide)

theorem root_at_33225 :
    CounterReach 1 1 33225
      7535911400608899821997530720351070984807099992130523368450 2 :=
  rootIter_sound (by decide)

def eighthWindowFirsts : List (Option Nat) :=
  (List.range 189).map fun j =>
    (rootIter j
      3845572142460562694198066874840163501233761074427641627198 2).map Prod.fst

theorem eighth_target_not_in_window :
    some 1793457638681908789667368406630761833172101555561152717920 ∉
      eighthWindowFirsts := by
  decide

theorem eighth_middleOdd_predecessor_unreachable
    {n d : Nat}
    (hr : CounterReach 1 1 n
      1793457638681908789667368406630761833172101555561152717920 d)
    (h1 :
      1793457638681908789667368406630761833172101555561152717920 < d)
    (h2 : d <
      3*1793457638681908789667368406630761833172101555561152717920+1) :
    False := by
  exact middleOdd_target_unreachable_of_window
    (preN:=33035) (startN:=33036) (width:=189) (endN:=33225)
    (preA:=961393035615140673549516718710040875308440268606910406798)
    (preD:=1457498944512501642702467274440552173554525480555251475134)
    (startA:=3845572142460562694198066874840163501233761074427641627198)
    (startD:=2)
    (endA:=7535911400608899821997530720351070984807099992130523368450)
    (endD:=2)
    (target:=1793457638681908789667368406630761833172101555561152717920)
    (n:=n) (d:=d)
    (by decide) (by decide)
    root_at_33035 root_at_33036 root_at_33225
    (by omega) (by omega)
    eighth_target_not_in_window
    hr h1 h2

theorem dangerR_seven :
    dangerR 7 =
      7173830554727635158669473626523047332688406222244610871686 := by
  decide

theorem eighth_danger_anchor_not_root
    {n a d : Nat}
    (hr : CounterReach 1 1 n a d)
    (ha : SmallAnchorMove a d (dangerR 7) 1) :
    False := by
  have hm := danger_anchor_requires_middleOdd hr ha
  rw [dangerR_seven] at hm
  have ha' :
      a=1793457638681908789667368406630761833172101555561152717920 := by
    omega
  subst a
  exact eighth_middleOdd_predecessor_unreachable hr hm.1 hm.2.1

#print axioms root_at_33035
#print axioms root_at_33036
#print axioms root_at_33225
#print axioms eighth_target_not_in_window
#print axioms eighth_middleOdd_predecessor_unreachable
#print axioms eighth_danger_anchor_not_root
end BB6.Agent31F321EighthMixed
