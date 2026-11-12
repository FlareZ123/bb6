import Low3Delta
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429Low43Delta

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429Low3Delta

/-- The A/1 zipper reached after the (v+1)-bubble prefix of the
    prepared J input with odd deficit 4k+3. -/
def stage43 (v k : Nat) : Zipper :=
  z 0 (ones (4*v+4) ++ (tens (2*k+1) ++ ones 6)) true [false,true]

private theorem af_tail_delta (l r : List Bool) :
    runWithDelta 2 (z 0 (true::false::l) true r) =
      some (z 0 l false (true::false::r), -2) := by
  rfl

private theorem low3_tail_delta (l : List Bool) :
    runWithDelta 4 (z 0 l false [false,true]) =
      some (z 2 (true::false::true::true::l) false [], 4) := by
  rfl

private theorem compose_delta (m n : Nat) (a b c : Zipper) (d e : Int)
    (h1 : runWithDelta m a = some (b,d))
    (h2 : runWithDelta n b = some (c,e)) :
    runWithDelta (m+n) a = some (c,d+e) := by
  rw [runWithDelta_add,h1]
  simp only [Option.bind_some]
  rw [h2]
  rfl

/-- Exact original-table entry into the C/0 low-branch corridor.
    This is the first 8v+16 steps after the prepared J state; it consumes
    the A/F left sweep, the A/F tail pair, the A/B right sweep, and the
    four-step C/0 tail. -/
theorem stage43_to_C0_delta (v k : Nat) :
    runWithDelta (8*v+16) (stage43 v k) =
      some (z 2 (true::false::true::true::
        (ones (4*v+6) ++ (tens (2*k) ++ ones 6))) false [], 4) := by
  have hAF : runWithDelta (4*v+4) (stage43 v k) =
      some (z 0 (tens (2*k+1) ++ ones 6) true
        (tens (2*v+2) ++ [false,true]), -((4*v+4 : Nat) : Int)) := by
    simpa [stage43, show 2*(2*v+2)=4*v+4 by omega, List.append_assoc] using
      (BB429Low3Delta.af_pairs_delta (2*v+2)
        (tens (2*k+1) ++ ones 6) [false,true])
  have h2 : runWithDelta 2
      (z 0 (tens (2*k+1) ++ ones 6) true
        (tens (2*v+2) ++ [false,true])) =
      some (z 0 (tens (2*k) ++ ones 6) false
        (tens (2*v+3) ++ [false,true]), -2) := by
    rw [show tens (2*k+1) = true::false::tens (2*k) by rfl]
    change runWithDelta 2
      (z 0 (true::false::(tens (2*k) ++ ones 6)) true
        (tens (2*v+2) ++ [false,true])) =
      some (z 0 (tens (2*k) ++ ones 6) false
        (true::false::(tens (2*v+2) ++ [false,true])), -2)
    exact af_tail_delta _ _
  have hAR : runWithDelta (4*v+6)
      (z 0 (tens (2*k) ++ ones 6) false
        (tens (2*v+3) ++ [false,true])) =
      some (z 0 (ones (4*v+6) ++ (tens (2*k) ++ ones 6))
        false [false,true], ((4*v+6 : Nat) : Int)) := by
    simpa [show 2*(2*v+3)=4*v+6 by omega, List.append_assoc] using
      (BB429Low3Delta.ar_pairs_delta (2*v+3)
        (tens (2*k) ++ ones 6) [false,true])
  have h4 : runWithDelta 4
      (z 0 (ones (4*v+6) ++ (tens (2*k) ++ ones 6))
        false [false,true]) =
      some (z 2 (true::false::true::true::
        (ones (4*v+6) ++ (tens (2*k) ++ ones 6))) false [], 4) := by
    exact low3_tail_delta _
  have h12 := compose_delta (4*v+6) 4
    (z 0 (tens (2*k) ++ ones 6) false
      (tens (2*v+3) ++ [false,true]))
    (z 0 (ones (4*v+6) ++ (tens (2*k) ++ ones 6))
      false [false,true])
    (z 2 (true::false::true::true::
      (ones (4*v+6) ++ (tens (2*k) ++ ones 6))) false [])
    ((4*v+6 : Nat) : Int) 4 hAR h4
  have h212 := compose_delta 2 ((4*v+6)+4)
    (z 0 (tens (2*k+1) ++ ones 6) true
      (tens (2*v+2) ++ [false,true]))
    (z 0 (tens (2*k) ++ ones 6) false
      (tens (2*v+3) ++ [false,true]))
    (z 2 (true::false::true::true::
      (ones (4*v+6) ++ (tens (2*k) ++ ones 6))) false [])
    (-2) (((4*v+6 : Nat) : Int)+4) h2 h12
  have hAll := compose_delta (4*v+4) (2+((4*v+6)+4))
    (stage43 v k)
    (z 0 (tens (2*k+1) ++ ones 6) true
      (tens (2*v+2) ++ [false,true]))
    (z 2 (true::false::true::true::
      (ones (4*v+6) ++ (tens (2*k) ++ ones 6))) false [])
    (-((4*v+4 : Nat) : Int)) (-2+(((4*v+6 : Nat) : Int)+4))
    hAF h212
  have ht : (4*v+4)+(2+((4*v+6)+4)) = 8*v+16 := by omega
  have hd : -((4*v+4 : Nat) : Int) +
      (-2+(((4*v+6 : Nat) : Int)+4)) = 4 := by omega
  simpa only [ht,hd] using hAll

#print axioms stage43_to_C0_delta

end BB429Low43Delta
