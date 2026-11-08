import High2TailBase
import Lean.Elab.Tactic.Omega

namespace BB429W4JuncOne

open BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion BB429High2TailBase

def sigma : List Bool := ones 3 ++ pairs01 1 ++ [false,false,true]

/-- Exact sixteen-step suffix from any zero-left Junc w=1 B/1 boundary into S_E. -/
theorem b1_to_scanE_16 (v : Nat) :
  runWithDelta 16 (z 1 (pairs01 (v+3) ++ ones 5) true [false,true]) =
    some (sourceScanE (v+2) sigma, -2) := by
  rfl

/-- Fixed twenty-step continuation at the C/1 left-one-stack boundary. -/
theorem c1_to_e1_20 (k : Nat) :
  runWithDelta 20 (z 2 (ones (4*k+24)) true sigma) =
    some (z 4 (ones (4*k+32)) true [true,false,true], 8) := by
  rfl

/-- A right-budget-one zero-left Junc reaches S_E for every middle parameter. -/
theorem junc0_w1_to_scanE (v : Nat) :
  runWithDelta (2*v+42) (junc 0 v 1) =
    some (sourceScanE (v+2) sigma, ((2*v : Nat) : Int)) := by
  have hB := junc0_to_B_delta v 1 (by omega)
  have htail := b1_to_scanE_16 v
  rw [show 2*v+42 = (2*v+26)+16 by omega, runWithDelta_add, hB]
  simp only [Option.bind_some]
  have hr : ones (1-1) ++ [false,true] = [false,true] := by rfl
  rw [hr, htail]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

theorem ones_append (m n : Nat) : ones (m+n) = ones m ++ ones n := by
  simp [ones]

theorem ones_right_101 (n : Nat) :
  ones n ++ [true,false,true] = true :: (ones n ++ [false,true]) := by
  have h : ones n ++ [true] = true :: ones n := by
    have h1 : ones (n+1) = ones n ++ [true] := by
      change List.replicate (n+1) true = List.replicate n true ++ [true]
      exact List.replicate_succ'
    have h2 : ones (n+1) = true :: ones n := by
      change List.replicate (n+1) true = true :: List.replicate n true
      exact List.replicate_succ
    exact h1.symm.trans h2
  calc
    ones n ++ [true,false,true] = (ones n ++ [true]) ++ [false,true] := by
      simp [List.append_assoc]
    _ = true :: (ones n ++ [false,true]) := by rw [h]; rfl

/-- An infinite odd S_E family with the exact source sigma suffix returns to
    a canonical Junc with zero left/middle parameters. -/
theorem scanE_odd_sigma_to_junc0 (k : Nat) :
  runWithDelta (18*k+136) (sourceScanE (2*k+9) sigma) =
    some (junc 0 0 (4*k+28), -((4*k+20 : Nat) : Int)) := by
  have hret := sourceScanE_e1_revisit_delta (2*(k+4)+1) sigma
  rw [crossTime_odd, finalLeft_odd] at hret
  have hprep := c1_to_e1_20 k
  have hsweep := E1_sweep_delta (4*k+32) [true,false,true]
  have htail := E1_tail12_delta (ones (4*k+28) ++ [true,false,true])
  have hrewrite : 2*(k+4)+1 = 2*k+9 := by omega
  rw [hrewrite] at hret
  have hleft : 4*(k+4)+8 = 4*k+24 := by omega
  rw [hleft] at hret
  have htime : 18*k+136 =
      ((14*(k+4)+15)+1) + (20 + ((4*k+32)+12)) := by omega
  rw [htime, runWithDelta_add, hret]
  simp only [Option.bind_some]
  rw [runWithDelta_add, hprep]
  simp only [Option.bind_some]
  rw [runWithDelta_add, hsweep]
  simp only [Option.bind_some]
  have hones : ones (4*k+32) = ones 4 ++ ones (4*k+28) := by
    calc
      ones (4*k+32) = ones (4+(4*k+28)) := by congr 1 <;> omega
      _ = ones 4 ++ ones (4*k+28) := ones_append 4 (4*k+28)
  rw [hones, List.append_assoc, htail]
  simp only [Option.map_some]
  have hcfg : z 0 (ones 6) true (ones (4*k+28) ++ [true,false,true]) =
      junc 0 0 (4*k+28) := by
    change z 0 (ones 6) true (ones (4*k+28) ++ [true,false,true]) =
      z 0 (true :: ones 5) true (true :: (ones (4*k+28) ++ [false,true]))
    rw [ones_right_101]
    rfl
  rw [hcfg]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- Entire right-one odd-parameter Junc path, source exact and unbounded. -/
theorem junc0_odd_w1_to_junc0 (k : Nat) :
  runWithDelta (22*k+192) (junc 0 (2*k+7) 1) =
    some (junc 0 0 (4*k+28), -6) := by
  have hfirst := junc0_w1_to_scanE (2*k+7)
  have htail := scanE_odd_sigma_to_junc0 k
  have hb : 2*k+7+2 = 2*k+9 := by omega
  rw [hb] at hfirst
  have htime : 22*k+192 = (2*(2*k+7)+42) + (18*k+136) := by omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- Uniform C/1 preparation covering all odd S_E indices from three up. -/
theorem c1_to_e1_20_general (k : Nat) :
  runWithDelta 20 (z 2 (ones (4*k+12)) true sigma) =
    some (z 4 (ones (4*k+20)) true [true,false,true], 8) := by
  rfl

/-- Complete canonical return of the entire odd-parameter, right-one Junc
    subfamily, including the four small indices omitted in the w4 application. -/
theorem scanE_odd_sigma_to_junc0_general (k : Nat) :
  runWithDelta (18*k+82) (sourceScanE (2*k+3) sigma) =
    some (junc 0 0 (4*k+16), -((4*k+8 : Nat) : Int)) := by
  have hret := sourceScanE_e1_revisit_delta (2*(k+1)+1) sigma
  rw [crossTime_odd, finalLeft_odd] at hret
  have hprep := c1_to_e1_20_general k
  have hsweep := E1_sweep_delta (4*k+20) [true,false,true]
  have htail := E1_tail12_delta (ones (4*k+16) ++ [true,false,true])
  have hrewrite : 2*(k+1)+1 = 2*k+3 := by omega
  rw [hrewrite] at hret
  have hleft : 4*(k+1)+8 = 4*k+12 := by omega
  rw [hleft] at hret
  have htime : 18*k+82 =
      ((14*(k+1)+15)+1) + (20 + ((4*k+20)+12)) := by omega
  rw [htime, runWithDelta_add, hret]
  simp only [Option.bind_some]
  rw [runWithDelta_add, hprep]
  simp only [Option.bind_some]
  rw [runWithDelta_add, hsweep]
  simp only [Option.bind_some]
  have hones : ones (4*k+20) = ones 4 ++ ones (4*k+16) := by
    calc
      ones (4*k+20) = ones (4+(4*k+16)) := by congr 1 <;> omega
      _ = ones 4 ++ ones (4*k+16) := ones_append 4 (4*k+16)
  rw [hones, List.append_assoc, htail]
  simp only [Option.map_some]
  have hcfg : z 0 (ones 6) true (ones (4*k+16) ++ [true,false,true]) =
      junc 0 0 (4*k+16) := by
    change z 0 (ones 6) true (ones (4*k+16) ++ [true,false,true]) =
      z 0 (true :: ones 5) true (true :: (ones (4*k+16) ++ [false,true]))
    rw [ones_right_101]
    rfl
  rw [hcfg]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

theorem junc0_all_odd_w1 (k : Nat) :
  runWithDelta (22*k+126) (junc 0 (2*k+1) 1) =
    some (junc 0 0 (4*k+16), -6) := by
  have hfirst := junc0_w1_to_scanE (2*k+1)
  have htail := scanE_odd_sigma_to_junc0_general k
  have hb : 2*k+1+2 = 2*k+3 := by omega
  rw [hb] at hfirst
  have htime : 22*k+126 = (2*(2*k+1)+42)+(18*k+82) := by omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some]
  simp only [Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

/-- Every positive-middle Junc(2,v,1) returns to canonical Junc(0,0,*).
    This is the complementary right-one case to the zero-u odd family. -/
theorem junc2_w1_to_junc0 (v : Nat) (hv : 1 ≤ v) :
    runWithDelta (8*v+54) (junc 2 v 1) =
      some (junc 0 0 (2*v+10), -6) := by
  have hfirst := juncPos_to_midA_delta 1 v 1 (by omega)
  have htail := BB429High2Tail.midApos_to_junc0_of_base v hv midAaux_zero_base
  have htime : 8*v+54 = (2*v+6)+(6*v+48) := by omega
  rw [htime, runWithDelta_add, hfirst]
  simp only [Option.bind_some]
  rw [htail]
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq]
  constructor
  · trivial
  · omega

#print axioms b1_to_scanE_16
#print axioms c1_to_e1_20
#print axioms junc0_w1_to_scanE
#print axioms scanE_odd_sigma_to_junc0
#print axioms junc0_odd_w1_to_junc0
#print axioms junc2_w1_to_junc0
#print axioms junc0_all_odd_w1

end BB429W4JuncOne
