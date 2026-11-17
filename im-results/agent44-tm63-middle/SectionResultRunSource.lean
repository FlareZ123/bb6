import StageAlgebra
import S1Encoder
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent44SectionResultRunSource

open BB6Coverage.Agent48Champion
open BB6Coverage.Agent8S1Encoder
open BB6ChampionArithmetic

private theorem run_compose_local {n m : Nat} {c1 c2 c3 : Config}
    (h1 : run tm2 n c1 = some c2)
    (h2 : run tm2 m c2 = some c3) :
    run tm2 (n+m) c1 = some c3 := by
  rw [run_add, h1]
  simp only [Option.bind_some]
  exact h2

/-- Head reached after consuming n source increments, with the current right
counter b as the first counter in the remaining suffix. -/
def sectionHeadAfter : Nat → Nat → Int → Int
  | 0, _, h => h
  | n+1, b, h => sectionHeadAfter n (nextRight b) (h+5+3*b)

/-- Closed form for the accumulated head displacement. -/
theorem sectionHeadAfter_eq (n b : Nat) (h : Int) :
    sectionHeadAfter n b h = h + 5*n + 3*sumRight n b := by
  induction n generalizing b h with
  | zero =>
      simp [sectionHeadAfter, sumRight]
  | succ n ih =>
      simp only [sectionHeadAfter]
      rw [ih]
      simp [sumRight, Nat.mul_succ]
      omega

/-- If every individual counted source increment is realized by the original
TM2 machine, then the complete primitive-recursive sectionResult stage is
also an original-TM2 run.  The head coordinate is carried explicitly; the
closed form is sectionHeadAfter_eq. -/
theorem sectionResult_run_of_source_macro
    (L n m a b : Nat) (head : Int)
    (hbound : n < 2^L) (ha : 0 < a)
    (hmacro : ∀ (k mm aa bb : Nat) (hh : Int),
      0 < k → k < 2^L → 0 < aa →
      run tm2 (proposedIncrementCost (mm%3) k aa bb)
        (s1Config L k (mm%3) aa 0 bb hh) =
      some (s1Config L (k-1) (nextMarker mm)
        (nextExponent mm aa bb) 0 (nextRight bb) (hh+5+3*bb))) :
    run tm2 (sectionResult n m a b).cost
      (s1Config L n (m%3) a 0 b head) =
    some (s1Config L 0
      (sectionResult n m a b).marker
      (sectionResult n m a b).exponent 0
      (sectionResult n m a b).right
      (sectionHeadAfter n b head)) := by
  induction n generalizing m a b head with
  | zero =>
      simp [sectionResult, sectionHeadAfter]
  | succ n ih =>
      have hstep := hmacro (n+1) m a b head (by omega) hbound ha
      have hbound' : n < 2^L := by omega
      have ha' : 0 < nextExponent m a b := by
        unfold nextExponent
        omega
      have hrest := ih (nextMarker m) (nextExponent m a b)
        (nextRight b) (head+5+3*b) hbound' ha'
      have hnorm : (nextMarker m)%3 = nextMarker m := by
        simp [nextMarker]
      have hrest' :
          run tm2
            (sectionResult n (nextMarker m) (nextExponent m a b)
              (nextRight b)).cost
            (s1Config L n (nextMarker m) (nextExponent m a b)
              0 (nextRight b) (head+5+3*b)) =
          some (s1Config L 0
            (sectionResult n (nextMarker m) (nextExponent m a b)
              (nextRight b)).marker
            (sectionResult n (nextMarker m) (nextExponent m a b)
              (nextRight b)).exponent
            0
            (sectionResult n (nextMarker m) (nextExponent m a b)
              (nextRight b)).right
            (sectionHeadAfter n (nextRight b) (head+5+3*b))) := by
        simpa [hnorm] using hrest
      have htotal := run_compose_local hstep hrest'
      simpa [sectionResult, sectionHeadAfter] using htotal

#print axioms sectionHeadAfter_eq
#print axioms sectionResult_run_of_source_macro

end BB6Coverage.Agent44SectionResultRunSource
