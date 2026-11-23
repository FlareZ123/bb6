import EvenOddTwoParentRoot
import Lean.Elab.Tactic.Omega

namespace BB6.Agent13SourceRect
open BB6.Agent46

/-- The original six-sector normalizer rejects any sufficiently large
    odd-right state in the forbidden blank-image sum-two sector. -/
theorem six_excludes_odd_sum_two (a k : Nat)
    (hk : 5≤k) (hko : k%2=1) (hsum : (a+k)%4=2) :
    BB6.Agent11SixForced.sixForcedExcluded a k=true := by
  have hO : ¬ BB6.Agent3.oddLowGate a k := by
    intro h
    rcases h with ⟨_,_,_,hs,_,_⟩
    omega
  have hS : ¬ BB6.Agent3.evenSevenGate a k := by
    intro h
    rcases h with ⟨_,_,_,hs,_⟩
    omega
  have hA : ¬ BB6.Agent3.evenAffineGate a k := by
    intro h
    rcases h with ⟨_,he,_⟩
    omega
  have hB : ¬ BB6.Agent46.sixEvenRightGate a k := by
    intro h
    rcases h with ⟨_,he,_,_⟩
    omega
  have hV : ¬ BB6.Agent3ValSix.valSixGate a k := by
    intro h
    rcases h with ⟨_,hy,_⟩
    omega
  have hF : ¬ BB6.Agent11SixForced.evenOddFourGate a k := by
    intro h
    rcases h with ⟨_,_,_,hs⟩
    omega
  simp [BB6.Agent11SixForced.sixForcedExcluded,
    BB6.Agent11SixForced.sixForcedNormalize,
    hO,hS,hA,hB,hV,hF,hk,hko,hsum]

/-- A genuine original-source unreachable rectangle independent of any
    quotient certificate: x=144, y=223 modulo 256, with large counters.
    The complete odd-source fan consists of two directly forbidden
    blank-image predecessors. -/
theorem even_odd_rectangle_144_223
    (x y : Nat) (hx : x%256=144) (hy : y%256=223) :
    ¬ BB6.Agent3.CReach x y := by
  have hxl : 5<x := by omega
  have hyl : 5≤y := by omega
  have hxe : x%2=0 := by omega
  have hyo : y%2=1 := by omega
  have hbig : 64≤x+y+1 := by omega
  have hn64 : (x+y+1)%64≠0 := by omega
  apply BB6.Agent13TwoParent.two_parent_normalizer_excluded
    x y hxl hxe hyo hyl hbig hn64
  · have hL : (BB6.Agent13TwoParent.parentLeft x y 0)%16=5 := by
      unfold BB6.Agent13TwoParent.parentLeft
      omega
    have hR : (BB6.Agent13TwoParent.parentRight x y 0)%16=9 := by
      unfold BB6.Agent13TwoParent.parentRight
        BB6.Agent13TwoParent.parentLeft
      omega
    apply six_excludes_odd_sum_two
    · unfold BB6.Agent13TwoParent.parentRight
        BB6.Agent13TwoParent.parentLeft
      omega
    · omega
    · omega
  · have hL : (BB6.Agent13TwoParent.parentLeft x y 2)%16=11 := by
      unfold BB6.Agent13TwoParent.parentLeft
      omega
    have hR : (BB6.Agent13TwoParent.parentRight x y 2)%16=11 := by
      unfold BB6.Agent13TwoParent.parentRight
        BB6.Agent13TwoParent.parentLeft
      omega
    apply six_excludes_odd_sum_two
    · unfold BB6.Agent13TwoParent.parentRight
        BB6.Agent13TwoParent.parentLeft
      omega
    · omega
    · omega

#print axioms even_odd_rectangle_144_223
end BB6.Agent13SourceRect
