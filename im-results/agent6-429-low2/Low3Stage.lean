import Low2Stage
import Lean.Elab.Tactic.Omega

namespace BB429Low3Stage
open BB429OddExcursion BB429SourceE1Return BB429FinishScanEDelta
open BB429Low2Stage BB429CZeroToJunc0

/-- The source checkpoint after (u-1) bubbles of J(u,2u-3),
    with u=v+2 and physical head 2v+2. -/
def stage3 (v : Nat) : Zipper :=
  z 0 (ones (4*v+4) ++ (true::false::ones 6)) true [false,true]

private theorem ones_add (m n : Nat) :
  ones (m+n) = ones m ++ ones n := by simp [ones]

private theorem af_tail (left right : List Bool) :
  run 2 (z 0 (true::false::left) true right) =
    some (z 0 left false (true::false::right)) := by rfl

private theorem tail4 (left : List Bool) :
  run 4 (z 0 left false [false,true]) =
    some (z 2 (true::false::true::true::left) false []) := by rfl

private theorem compose (m n : Nat) (a b c : Zipper)
  (h1 : run m a=some b) (h2 : run n b=some c) :
  run (m+n) a=some c := by
  rw [run_add,h1]
  exact h2

/-- Arbitrary-parameter source passage through the first C/0 frontier. -/
theorem stage3_to_C0 (v : Nat) :
  run (8*v+16) (stage3 v) =
    some (z 2 (true::false::ones (4*v+14)) false []) := by
  have hAF : run (4*v+4) (stage3 v) =
    some (z 0 (true::false::ones 6) true (tens (2*v+2) ++ [false,true])) := by
    simpa [stage3,ones,show 2*(2*v+2)=4*v+4 by omega] using
      (af_pairs (2*v+2) (true::false::ones 6) [false,true])
  have h2 : run 2 (z 0 (true::false::ones 6) true
      (tens (2*v+2) ++ [false,true])) =
    some (z 0 (ones 6) false (tens (2*v+3) ++ [false,true])) := by
    change run 2 (z 0 (true::false::ones 6) true
      (tens (2*v+2) ++ [false,true])) =
      some (z 0 (ones 6) false (true::false::(tens (2*v+2) ++ [false,true])))
    exact af_tail (ones 6) _
  have hAR : run (4*v+6) (z 0 (ones 6) false
      (tens (2*v+3) ++ [false,true])) =
      some (z 0 (ones (4*v+6) ++ ones 6) false [false,true]) := by
    simpa [show 2*(2*v+3)=4*v+6 by omega] using
      (ar_pairs_exact (2*v+3) (ones 6) [false,true])
  have h4 : run 4 (z 0 (ones (4*v+6) ++ ones 6) false [false,true]) =
      some (z 2 (true::false::ones (4*v+14)) false []) := by
    have hw : ones (4*v+14) = true::true::(ones (4*v+6) ++ ones 6) := by
      rw [show 4*v+14 = 2+((4*v+6)+6) by omega, ones_add, ones_add]
      rfl
    rw [hw]
    exact tail4 _
  have h12 := compose (4*v+6) 4
    (z 0 (ones 6) false (tens (2*v+3) ++ [false,true]))
    (z 0 (ones (4*v+6) ++ ones 6) false [false,true])
    (z 2 (true::false::ones (4*v+14)) false []) hAR h4
  have h212 := compose 2 ((4*v+6)+4)
    (z 0 (true::false::ones 6) true (tens (2*v+2) ++ [false,true]))
    (z 0 (ones 6) false (tens (2*v+3) ++ [false,true]))
    (z 2 (true::false::ones (4*v+14)) false []) h2 h12
  have hAll := compose (4*v+4) (2+((4*v+6)+4))
    (stage3 v)
    (z 0 (true::false::ones 6) true (tens (2*v+2) ++ [false,true]))
    (z 2 (true::false::ones (4*v+14)) false []) hAF h212
  have ht : (4*v+4)+(2+((4*v+6)+4)) = 8*v+16 := by omega
  simpa only [ht] using hAll

/-- All-natural exact odd-deficit-three stage to canonical junction. -/
theorem stage3_to_junc (v : Nat) :
  run (12*v+48) (stage3 v) = some (junc 0 0 (4*v+10)) := by
  have hnext : run (2*(2*v+5)+22)
       (z 2 (true::false::ones (4*v+14)) false []) =
       some (junc 0 0 (4*v+10)) := by
    have h1 : 2*(2*v+5)+4 = 4*v+14 := by omega
    have h2 : 2*(2*v+5) = 4*v+10 := by omega
    simpa only [h1,h2] using C0_to_junc0 (2*v+5)
  have hfull := compose (8*v+16) (2*(2*v+5)+22)
    (stage3 v) (z 2 (true::false::ones (4*v+14)) false [])
    (junc 0 0 (4*v+10)) (stage3_to_C0 v) hnext
  have ht : (8*v+16)+(2*(2*v+5)+22) = 12*v+48 := by omega
  simpa only [ht] using hfull

#print axioms stage3_to_C0
#print axioms stage3_to_junc
end BB429Low3Stage
