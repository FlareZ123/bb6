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
  
/-- The u=0 Junc boundary with two right ones has an exact A/1 exit. -/
theorem junc0_w2_boundary_delta (v : Nat) :
    runWithDelta (2*v+27) (junc 0 v 2) =
      some (z 0 (true :: (pairs01 (v+3) ++ ones 5)) true [false,true],
        ((2*v+3 : Nat) : Int)) := by
  have hB := junc0_to_B_delta v 2 (by omega)
  have hlast :
      runWithDelta 1
        (z 1 (pairs01 (v+3) ++ ones 5) true (ones 1 ++ [false,true])) =
      some (z 0 (true :: (pairs01 (v+3) ++ ones 5)) true [false,true], 1) := by
    rfl
  rw [show 2*v+27 = (2*v+26)+1 by omega, runWithDelta_add, hB]
  simp only [Option.bind_some]
  rw [hlast]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- The u=0 Junc boundary with three right ones exits to a positive-u
    zero-budget Junc, then to an explicit A/0 configuration. -/
theorem junc0_w3_exit_delta (v : Nat) :
    runWithDelta (2*v+33) (junc 0 v 3) =
      some (z 0 (ones 5 ++ pairs01 (v+2) ++ ones 5) false [true],
        ((2*v+5 : Nat) : Int)) := by
  have hnext := junc0_next_delta v 3 (by omega)
  have htail := juncPos_w0_exit_delta (v+2) 0
  rw [show 2*v+33 = (2*v+27)+6 by omega, runWithDelta_add, hnext]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- Exhausting the positive-u counter at the w=4 MidA boundary gives an
    exact A/1 state with the remaining alternating block exposed. -/
theorem midApos_zero_w4_boundary_delta (v : Nat) :
    runWithDelta (4*v+35) (midApos 0 v 4) =
      some (z 0 (true :: (pairs01 (v+5) ++ ones 5)) true [false,true], 3) := by
  have hshift := midApos_to_junc_delta 0 v 4 (by omega)
  have htail := junc0_w2_boundary_delta (v+2)
  have htime : 4*v+35 = 2*(v+2) + (2*(v+2)+27) := by omega
  rw [htime, runWithDelta_add, hshift]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- Exhausting the positive-u counter at the w=5 MidA boundary gives an
    exact A/0 state with the remaining alternating block exposed. -/
theorem midApos_zero_w5_boundary_delta (v : Nat) :
    runWithDelta (4*v+41) (midApos 0 v 5) =
      some (z 0 (ones 5 ++ pairs01 (v+4) ++ ones 5) false [true], 5) := by
  have hshift := midApos_to_junc_delta 0 v 5 (by omega)
  have htail := junc0_w3_exit_delta (v+2)
  have htime : 4*v+41 = 2*(v+2) + (2*(v+2)+33) := by omega
  rw [htime, runWithDelta_add, hshift]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some]
  simp [Int.natCast_add, Int.natCast_mul]
  omega

/-- The explicit w=5,u=0 A/0 boundary is a source E/1 configuration
    after 19 further steps, with a fixed right suffix ending in 001. -/
theorem midApos_zero_w5_to_sourceScanE_delta (v : Nat) :
    runWithDelta (4*v+60) (midApos 0 v 5) =
      some (sourceScanE (v+3) (ones 3 ++ pairs01 3 ++ [false,false,true]), -2) := by
  have hboundary := midApos_zero_w5_boundary_delta v
  have hscan :
      runWithDelta 19 (z 0 (ones 5 ++ pairs01 (v+4) ++ ones 5) false [true]) =
        some (sourceScanE (v+3) (ones 3 ++ pairs01 3 ++ [false,false,true]), -7) := by
    rfl
  have htime : 4*v+60 = (4*v+41)+19 := by omega
  rw [htime, runWithDelta_add, hboundary]
  simp only [Option.bind_some]
  rw [hscan]
  simp only [Option.map_some]
  rfl

/-- The w=5 zero-u branch returns to C/1 with a solid left stack
    when v is even. -/
theorem midApos_zero_w5_to_C1_even_delta (k : Nat) :
    runWithDelta (22*k+90) (midApos 0 (2*k) 5) =
      some (z 2 (ones (4*k+12)) true
        (ones 3 ++ pairs01 3 ++ [false,false,true]), -2) := by
  have hsource := midApos_zero_w5_to_sourceScanE_delta (2*k)
  rw [show 2*k+3 = 2*(k+1)+1 by omega] at hsource
  have hreturn := sourceScanE_e1_revisit_delta (2*k+3)
    (ones 3 ++ pairs01 3 ++ [false,false,true])
  rw [show 2*k+3 = 2*(k+1)+1 by omega, crossTime_odd] at hreturn
  have htime : 22*k+90 = (4*(2*k)+60) + (14*(k+1)+15+1) := by omega
  rw [htime, runWithDelta_add, hsource]
  simp only [Option.bind_some]
  rw [hreturn]
  simp only [Option.map_some]
  rw [finalLeft_odd (k+1)]
  rw [show 4*(k+1)+8 = 4*k+12 by omega]
  rfl

/-- The w=5 zero-u branch returns to C/1 with an alternating two-pair
    left block when v is odd. -/
theorem midApos_zero_w5_to_C1_odd_delta (k : Nat) :
    runWithDelta (22*k+134) (midApos 0 (2*k+1) 5) =
      some (z 2 (ones (4*k+9) ++ pairs01 2 ++ ones 5) true
        (ones 3 ++ pairs01 3 ++ [false,false,true]), -2) := by
  have hsource := midApos_zero_w5_to_sourceScanE_delta (2*k+1)
  rw [show 2*k+1+3 = 2*(k+2) by omega] at hsource
  have hreturn := sourceScanE_e1_revisit_delta (2*k+4)
    (ones 3 ++ pairs01 3 ++ [false,false,true])
  rw [show 2*k+4 = 2*(k+2) by omega, crossTime_even] at hreturn
  have htime : 22*k+134 = (4*(2*k+1)+60) + (14*(k+2)+41+1) := by omega
  rw [htime, runWithDelta_add, hsource]
  simp only [Option.bind_some]
  rw [hreturn]
  simp only [Option.map_some]
  rw [finalLeft_even (k+2)]
  rw [show 4*(k+2)+1 = 4*k+9 by omega]
  rfl

/-- Sweep a leading block of ones in an E/1 zipper while preserving
    an arbitrary untouched left tail. -/
theorem E1_sweep_prefix_delta (n : Nat) (left suffix : List Bool) :
    runWithDelta n (z 4 (ones n ++ left) true suffix) =
      some (z 4 left true (ones n ++ suffix), -((n : Nat) : Int)) := by
  induction n generalizing left suffix with
  | zero =>
      rfl
  | succ n ih =>
      rw [show n+1 = 1+n by omega, runWithDelta_add]
      have hleft : ones (1+n) ++ left = true :: (ones n ++ left) := by
        rw [BB429SourceE1Return.ones_add 1 n]
        simp [ones, List.append_assoc]
      have hstep :
          runWithDelta 1 (z 4 (ones (1+n) ++ left) true suffix) =
            some (z 4 (ones n ++ left) true (true :: suffix), -1) := by
        rw [hleft]
        simp [runWithDelta, oneWithDelta, one, action, z, ones]
      rw [hstep]
      simp only [Option.bind_some]
      rw [ih]
      simp only [Option.map_some]
      have hones : ones n ++ [true] = ones (n+1) := by
        simpa [ones] using (BB429SourceE1Return.ones_add n 1).symm
      have hright : ones n ++ (true :: suffix) = ones (n+1) ++ suffix := by
        calc
          ones n ++ (true :: suffix) = ones n ++ ([true] ++ suffix) := rfl
          _ = (ones n ++ [true]) ++ suffix := by rw [← List.append_assoc]
          _ = ones (n+1) ++ suffix := by rw [hones]
      rw [hright, show n+1 = 1+n by omega]
      simp only [Option.some.injEq, Prod.mk.injEq]
      constructor
      · rfl
      · omega

/-- Appending a fixed 101 tail to an all-one block exposes one
    additional leading one. -/
theorem ones_right_101 (n : Nat) :
    ones n ++ [true,false,true] = true :: (ones n ++ [false,true]) := by
  have hones : ones n ++ [true] = ones (n+1) := by
    calc
      ones n ++ [true] = ones n ++ ones 1 := by rfl
      _ = ones (n+1) := (BB429SourceE1Return.ones_add n 1).symm
  have hsucc : ones (n+1) = true :: ones n := by
    rw [show n+1 = 1+n by omega, BB429SourceE1Return.ones_add 1 n]
    rfl
  calc
    ones n ++ [true,false,true] = (ones n ++ [true]) ++ [false,true] := by
      simpa using (List.append_assoc (ones n) [true] [false,true]).symm
    _ = ones (n+1) ++ [false,true] := by rw [hones]
    _ = (true :: ones n) ++ [false,true] := by rw [hsucc]
    _ = true :: (ones n ++ [false,true]) := by rfl

/-- The even-b C/1 boundary begins with a fixed 24-step E/1 preparation. -/
theorem c1_odd_to_e1_prefix_delta (k : Nat) :
    runWithDelta 24
      (z 2 (ones (4*k+12)) true
        (ones 3 ++ pairs01 3 ++ [false,false,true])) =
      some (z 4 (ones (4*k+24)) true [true,false,true], 12) := by
  rfl

/-- The odd-b C/1 boundary begins with the corresponding 24-step
    preparation, retaining the two-pair alternating left block. -/
theorem c1_even_to_e1_prefix_delta (k : Nat) :
    runWithDelta 24
      (z 2 (ones (4*k+9) ++ pairs01 2 ++ ones 5) true
        (ones 3 ++ pairs01 3 ++ [false,false,true])) =
      some (z 4 (ones (4*k+21) ++ pairs01 2 ++ ones 5) true
        [true,false,true], 12) := by
  rfl

/-- The even-v C/1 boundary reduces exactly to a zero-u Junc state. -/
theorem c1_odd_to_junc0_delta (k : Nat) :
    runWithDelta (4*k+60)
      (z 2 (ones (4*k+12)) true
        (ones 3 ++ pairs01 3 ++ [false,false,true])) =
      some (junc 0 0 (4*k+20), -((4*k+8 : Nat) : Int)) := by
  have hprefix := c1_odd_to_e1_prefix_delta k
  have hsweep := BB429High2TailBase.E1_sweep_delta (4*k+24) [true,false,true]
  have htail := BB429High2TailBase.E1_tail12_delta (ones (4*k+20) ++ [true,false,true])
  have hones : ones (4*k+24) = ones 4 ++ ones (4*k+20) := by
    calc
      ones (4*k+24) = ones (4+(4*k+20)) := by congr 1 <;> omega
      _ = ones 4 ++ ones (4*k+20) :=
        BB429SourceE1Return.ones_add 4 (4*k+20)
  have hinput :
      z 4 [] true (ones (4*k+24) ++ [true,false,true]) =
      z 4 [] true (ones 4 ++ (ones (4*k+20) ++ [true,false,true])) := by
    congr 1
    rw [hones, List.append_assoc]
  have hcfg :
      z 0 (ones 6) true (ones (4*k+20) ++ [true,false,true]) =
      junc 0 0 (4*k+20) := by
    unfold junc
    simp only [pairs01]
    rw [ones_right_101]
    simp [ones]
    simp [ones]
  have htime : 4*k+60 = 24 + ((4*k+24)+12) := by omega
  rw [htime, runWithDelta_add, hprefix]
  simp only [Option.bind_some]
  rw [List.append_assoc]
  rw [runWithDelta_add, hsweep]
  simp only [Option.bind_some]
  rw [hinput, htail]
  simp only [Option.map_some]
  simp only [Option.map_some]
  rw [hcfg]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · rfl
  · omega

/-- One more u=0 Junc macro moves the even-v boundary to positive u. -/
theorem c1_odd_to_junc3_delta (k : Nat) :
    runWithDelta (4*k+87)
      (z 2 (ones (4*k+12)) true
        (ones 3 ++ pairs01 3 ++ [false,false,true])) =
      some (junc 3 0 (4*k+17), -((4*k+5 : Nat) : Int)) := by
  have hfirst := c1_odd_to_junc0_delta k
  have hnext := junc0_next_delta 0 (4*k+20) (by omega)
  have htime : 4*k+87 = (4*k+60)+27 := by omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [hnext]
  simp only [Option.map_some]
  have hw : 4*k+20-3 = 4*k+17 := by omega
  rw [hw]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · rfl
  · omega

/-- Compose the even-v C/1 return with its positive-u Junc continuation. -/
theorem midApos_zero_w5_even_to_junc3_delta (k : Nat) :
    runWithDelta (26*k+177) (midApos 0 (2*k) 5) =
      some (junc 3 0 (4*k+17), -((4*k+7 : Nat) : Int)) := by
  have hfirst := midApos_zero_w5_to_C1_even_delta k
  have htail := c1_odd_to_junc3_delta k
  have htime : 26*k+177 = (22*k+90)+(4*k+87) := by omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · rfl
  · omega

/-- The odd-v C/1 boundary reduces through a source S_E suffix to
    a positive-u Junc state. -/
theorem c1_even_to_junc11_delta (k : Nat) :
    runWithDelta (4*k+220)
      (z 2 (ones (4*k+9) ++ pairs01 2 ++ ones 5) true
        (ones 3 ++ pairs01 3 ++ [false,false,true])) =
      some (junc 11 0 (4*k+10), (2 : Int) - (4*k : Int)) := by
  have hprefix := c1_even_to_e1_prefix_delta k
  have hsweep := E1_sweep_prefix_delta (4*k+21)
    (pairs01 2 ++ ones 5) [true,false,true]
  have hones1 : ones (4*k+21) ++ [true] = ones (4*k+22) := by
    calc
      ones (4*k+21) ++ [true] = ones (4*k+21) ++ ones 1 := by rfl
      _ = ones ((4*k+21)+1) :=
          (BB429SourceE1Return.ones_add (4*k+21) 1).symm
      _ = ones (4*k+22) := by congr 1 <;> omega
  have hones2 : ones 6 ++ ones (4*k+16) = ones (4*k+22) := by
    calc
      ones 6 ++ ones (4*k+16) = ones (6+(4*k+16)) :=
          (BB429SourceE1Return.ones_add 6 (4*k+16)).symm
      _ = ones (4*k+22) := by congr 1 <;> omega
  have hright :
      ones (4*k+21) ++ [true,false,true] =
      ones 6 ++ ones (4*k+16) ++ [false,true] := by
    calc
      ones (4*k+21) ++ [true,false,true] =
          (ones (4*k+21) ++ [true]) ++ [false,true] := by
            simpa using (List.append_assoc (ones (4*k+21)) [true] [false,true]).symm
      _ = ones (4*k+22) ++ [false,true] := by rw [hones1]
      _ = (ones 6 ++ ones (4*k+16)) ++ [false,true] := by rw [hones2]
      _ = ones 6 ++ ones (4*k+16) ++ [false,true] := by rw [List.append_assoc]
  have hsource :
      z 4 (pairs01 2 ++ ones 5) true
        (ones (4*k+21) ++ [true,false,true]) =
      sourceScanE 2 (sourceSuffix (2*k+8)) := by
    simp only [sourceScanE, sourceSuffix]
    rw [show 2*(2*k+8) = 4*k+16 by omega, hright]
  have htail := sourceScanE_finishC_even_after_junc0_delta 1 (2*k+8) (by omega)
  have htailTime :
      ((crossTime (2*1)+1+(12+2*(2*1))) +
        (juncPosFullTime 2 (2*1+2) + (2*(2*1+6)+27))) = 175 := by
    rw [crossTime_even 1]
    simp [juncPosFullTime]
  rw [htailTime] at htail
  have hw : 2*(2*k+8)-6 = 4*k+10 := by omega
  rw [show 2*1+9=11 by omega, hw] at htail
  have htime : 4*k+220 = 24 + ((4*k+21)+175) := by omega
  rw [htime, runWithDelta_add, hprefix]
  simp only [Option.bind_some]
  rw [List.append_assoc]
  rw [runWithDelta_add, hsweep]
  simp only [Option.bind_some]
  rw [hsource, htail]
  simp only [Option.map_some]
  simp only [Option.map_some]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · rfl
  · omega

/-- Compose the odd-v C/1 return with its positive-u Junc continuation. -/
theorem midApos_zero_w5_odd_to_junc11_delta (k : Nat) :
    runWithDelta (26*k+354) (midApos 0 (2*k+1) 5) =
      some (junc 11 0 (4*k+10), -((4*k : Nat) : Int)) := by
  have hfirst := midApos_zero_w5_to_C1_odd_delta k
  have htail := c1_even_to_junc11_delta k
  have htime : 26*k+354 = (22*k+134)+(4*k+220) := by omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · rfl
  · omega

#print axioms shift_A01_tail_delta
#print axioms juncPos_w0_exit_delta
#print axioms midApos_to_junc_delta
#print axioms midApos_reenter_delta
#print axioms midApos_reenter_twice_delta
#print axioms midApos_w2_exit_delta
#print axioms junc0_w2_boundary_delta
#print axioms junc0_w3_exit_delta
#print axioms midApos_zero_w4_boundary_delta
#print axioms midApos_zero_w5_boundary_delta
#print axioms midApos_zero_w5_to_sourceScanE_delta
#print axioms midApos_zero_w5_to_C1_even_delta
#print axioms midApos_zero_w5_to_C1_odd_delta
#print axioms E1_sweep_prefix_delta
#print axioms c1_odd_to_e1_prefix_delta
#print axioms c1_even_to_e1_prefix_delta
#print axioms c1_odd_to_junc0_delta
#print axioms c1_odd_to_junc3_delta
#print axioms midApos_zero_w5_even_to_junc3_delta
#print axioms c1_even_to_junc11_delta
#print axioms midApos_zero_w5_odd_to_junc11_delta

end BB429MidAposBoundary
