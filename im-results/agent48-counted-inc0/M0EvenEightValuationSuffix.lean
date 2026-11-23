import M0EvenEightQ4Prefix
import Q4Suffix
import Lean.Elab.Tactic.Omega

namespace BB6Coverage.Agent48M0EvenEightValuationSuffix

open BB6Coverage
open BB6Coverage.Agent8S1Encoder
open BB6Coverage.Agent48M0EvenEightQ4Prefix
open BB6Coverage.Agent8Q4Suffix

/-- General q4 left-facing interface, with the residual binary tail kept
in its canonical `binDec L (8*q-1)` form. -/
def m0EvenEightQ4LeftFacingAll (L q a : Nat) : List Bool :=
  [true] ++ d1pow (a-1) ++ markerWord 2 ++ d0 ++
    binDec L (8*q-1) ++ lh

/-- The q4 suffix target-left identity is independent of q's parity. -/
theorem m0EvenEightQ4SuffixTargetLeftAllQ
    (L q a b : Nat) (ha : 0 < a) :
    s1LeftFacing L (8*q-1) 2 (a+b+1) (2^b-1) =
      d0pow b ++ d1pow 2 ++
        (m0EvenEightQ4LeftFacingAll L q a).drop 1 := by
  unfold s1LeftFacing m0EvenEightQ4LeftFacingAll
  have hbin : binDec (a+b+1) (2^b-1) =
      d0pow b ++ d1pow (a+1) := by
    have h := BB6Coverage.Agent8Q4Suffix.binDec_pow2_sub_one (a-1) b
    have hlen : (a-1)+b+2 = a+b+1 := by omega
    have hval : (a-1)+2 = a+1 := by omega
    simpa [hlen,hval] using h
  rw [hbin]
  have hadd : d1pow (a+1) = d1pow 2 ++ d1pow (a-1) := by
    have h := BB6Coverage.Agent8Q4Suffix.d1pow_add_right (a-1) 2
    have hval : (a-1)+2 = a+1 := by omega
    simpa [hval] using h
  rw [hadd]
  simp [List.drop,List.append_assoc]

#print axioms m0EvenEightQ4SuffixTargetLeftAllQ

end BB6Coverage.Agent48M0EvenEightValuationSuffix
