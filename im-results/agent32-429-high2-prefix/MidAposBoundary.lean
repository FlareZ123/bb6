import High2Return
import Lean.Elab.Tactic.Omega

namespace BB429MidAposBoundary

open BB429High2Return BB429JuncHeadExcursion BB429FinishScanEDelta
open BB429SourceE1Delta BB429SourceE1Return BB429OddExcursion BB6Coverage

/-- Consume a right-hand alternating block `1(01)^n`, leaving its final
    one as the only right-hand mark. This is the exact A/0,B/1 sweep used
    at the zero-right-budget Junc boundary. -/
theorem shift_A01_tail_delta (n : Nat) (hn : 1 ≤ n) (left : List Bool) :
    runWithDelta (2*n) (z 0 left false (true :: pairs01 n)) =
      some (z 0 (ones (2*n) ++ left) false [true], ((2*n : Nat) : Int)) := by
  induction n generalizing left with
  | zero =>
      omega
  | succ n ih =>
      cases n with
      | zero =>
          simpa [pairs01, ones] using
            (shift_A01_pair_delta left [false,true])
      | succ n =>
          have hpair :
              runWithDelta 2
                (z 0 left false (true :: (false :: true :: pairs01 (n+1)))) =
              some (z 0 (true :: true :: left) false (true :: pairs01 (n+1)), 2) := by
            simpa [pairs01] using
              (shift_A01_pair_delta left (false :: true :: pairs01 (n+1)))
          have hrest := ih (by omega) (true :: true :: left)
          have htime : 2*(n+2) = 2 + 2*(n+1) := by omega
          rw [htime, runWithDelta_add]
          have hpair' :
              runWithDelta 2 (z 0 left false (true :: pairs01 (n+2))) =
                some (z 0 (true :: true :: left) false (true :: pairs01 (n+1)), 2) := by
            simpa only [pairs01] using hpair
          rw [hpair']
          simp only [Option.bind_some]
          rw [hrest]
          simp only [Option.map_some]
          have hleft : ones (2*(n+1)) ++ [true,true] = ones (2*(n+2)) := by
            calc
              ones (2*(n+1)) ++ [true,true] =
                  ones (2*(n+1)) ++ ones 2 := by simp [ones]
              _ = ones (2*(n+1)+2) := by rw [← BB429SourceE1Return.ones_add]
              _ = ones (2*(n+2)) := by congr 1 <;> omega
          have hleft' : ones (2*(n+1)) ++ (true :: true :: left) =
              ones (2+2*(n+1)) ++ left := by
            calc
              ones (2*(n+1)) ++ (true :: true :: left) =
                  (ones (2*(n+1)) ++ [true,true]) ++ left := by
                    rw [show true :: true :: left = [true,true] ++ left by rfl,
                      ← List.append_assoc]
              _ = ones (2+2*(n+1)) ++ left := by
                rw [hleft]
                rw [show 2*(n+2) = 2+2*(n+1) by omega]
          rw [hleft']
          simp [Int.natCast_add, Int.natCast_mul]
  
/-- A positive-left-parameter Junc with zero right budget has an exact
    finite exit to A/0 with one marked cell immediately to the right. -/
theorem juncPos_w0_exit_delta (u v : Nat) :
    runWithDelta (2*v+6) (junc (u+1) v 0) =
      some (z 0 (ones (2*v+5) ++ pairs01 u ++ ones 5) false [true],
        ((2*v+2 : Nat) : Int)) := by
  have hprep := juncPos_prep4_delta u v 0
  have htail := shift_A01_tail_delta (v+1) (by omega)
    (true :: true :: true :: (pairs01 u ++ ones 5))
  have htime : 2*v+6 = 4 + 2*(v+1) := by omega
  rw [htime, runWithDelta_add, hprep]
  simp only [Option.bind_some]
  have hright : pairs01 v ++ ones 0 ++ [false,true] = pairs01 (v+1) := by
    simpa [ones] using pairs01_succ_append v
  have hinput :
      z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: (pairs01 v ++ ones 0 ++ [false,true])) =
      z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false
        (true :: pairs01 (v+1)) := by
    exact congrArg (fun r : List Bool =>
      z 0 (true :: true :: true :: (pairs01 u ++ ones 5)) false (true :: r)) hright
  rw [hinput, htail]
  simp only [Option.map_some]
  have hleft : ones (2*(v+1)) ++ [true,true,true] = ones (2*v+5) := by
    calc
      ones (2*(v+1)) ++ [true,true,true] =
          ones (2*(v+1)) ++ ones 3 := by simp [ones]
      _ = ones (2*(v+1)+3) := by rw [← BB429SourceE1Return.ones_add]
      _ = ones (2*v+5) := by congr 1 <;> omega
  have hleft' :
      ones (2*(v+1)) ++ (true :: true :: true :: (pairs01 u ++ ones 5)) =
        ones (2*v+5) ++ pairs01 u ++ ones 5 := by
    calc
      ones (2*(v+1)) ++ (true :: true :: true :: (pairs01 u ++ ones 5)) =
          (ones (2*(v+1)) ++ [true,true,true]) ++ (pairs01 u ++ ones 5) := by
            rw [show true :: true :: true :: (pairs01 u ++ ones 5) =
              [true,true,true] ++ (pairs01 u ++ ones 5) by rfl,
              ← List.append_assoc]
      _ = ones (2*v+5) ++ pairs01 u ++ ones 5 := by
        rw [hleft, List.append_assoc]
  rw [hleft']
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- A MidA-positive configuration with at least two right ones normalizes
    exactly to a Junc configuration by the source shift_A_11 macro. -/
theorem midApos_to_junc_delta (u v w : Nat) (hw : 2 ≤ w) :
    runWithDelta (2*(v+2)) (midApos u v w) =
      some (junc u (v+2) (w-2), -((2*(v+2) : Nat) : Int)) := by
  have hones : ones (w-1) = true :: ones (w-2) := by
    cases w with
    | zero => omega
    | succ w => cases w with
      | zero => omega
      | succ w => rfl
  have hstart :
      midApos u v w =
        z 0 (true :: (ones (2*(v+2)) ++ (pairs01 u ++ ones 5))) true
          (true :: (ones (w-2) ++ [false,true])) := by
    simp [midApos, hones, List.append_assoc, List.cons_append]
  rw [hstart]
  simpa [junc, pairs01, List.append_assoc, List.cons_append] using
    (shift_A11_delta (v+2) (pairs01 u ++ ones 5) (ones (w-2) ++ [false,true]))

/-- Re-enter the MidA-positive family after one Junc excursion. For w>=3,
    the parameter update is (u,v,w) -> (u-1,v+2,w-2), with net head
    displacement +2 and exact cost 4v+14. -/
theorem midApos_reenter_delta (u v w : Nat) (hu : 1 ≤ u) (hw : 3 ≤ w) :
    runWithDelta (4*v+14) (midApos u v w) =
      some (midApos (u-1) (v+2) (w-2), 2) := by
  have hshift := midApos_to_junc_delta u v w (by omega)
  have hcross := juncPos_iter_mid_delta 1 u (v+2) (w-2)
    (by omega) (by omega) (by omega)
  have htime : 4*v+14 = 2*(v+2) + juncPosMidTime 1 (v+2) := by
    simp [juncPosMidTime]
    omega
  rw [htime, runWithDelta_add, hshift]
  simp only [Option.bind_some]
  rw [hcross]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- Two successive re-entries reduce a right parameter of five to one. -/
theorem midApos_reenter_twice_delta (u v : Nat) (hu : 2 ≤ u) :
    runWithDelta (8*v+36) (midApos u v 5) =
      some (midApos (u-2) (v+4) 1, 4) := by
  have hfirst := midApos_reenter_delta u v 5 (by omega) (by omega)
  have hsecond := midApos_reenter_delta (u-1) (v+2) 3 (by omega) (by omega)
  have htime : 8*v+36 = (4*v+14) + (4*(v+2)+14) := by omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [hsecond]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  have hsub : u - 1 - 1 = u - 2 := by omega
  rw [hsub]

/-- The w=2 boundary after a MidA-positive shift has an exact A/0 exit.
    The right tape is now a single one; the remaining left pattern is
    recorded explicitly for subsequent analysis. -/
theorem midApos_w2_exit_delta (u v : Nat) (hu : 1 ≤ u) :
    runWithDelta (4*v+14) (midApos u v 2) =
      some (z 0 (ones (2*v+9) ++ pairs01 (u-1) ++ ones 5) false [true], 2) := by
  have hshift := midApos_to_junc_delta u v 2 (by omega)
  have htail := juncPos_w0_exit_delta (u-1) (v+2)
  have htail' :
      runWithDelta (2*(v+2)+6) (junc u (v+2) 0) =
        some (z 0 (ones (2*(v+2)+5) ++ pairs01 (u-1) ++ ones 5) false [true],
          ((2*(v+2)+2 : Nat) : Int)) := by
    simpa [Nat.sub_add_cancel hu, Int.natCast_add, Int.natCast_mul] using htail
  have htime : 4*v+14 = 2*(v+2) + (2*(v+2)+6) := by omega
  rw [htime, runWithDelta_add, hshift]
  simp only [Option.bind_some]
  rw [htail']
  simp only [Option.map_some]
  have hleft : 2*(v+2)+5 = 2*v+9 := by omega
  simp [hleft, Int.natCast_add, Int.natCast_mul]
  omega
  
#print axioms shift_A01_tail_delta
#print axioms juncPos_w0_exit_delta
#print axioms midApos_to_junc_delta
#print axioms midApos_reenter_delta
#print axioms midApos_reenter_twice_delta
#print axioms midApos_w2_exit_delta

end BB429MidAposBoundary
