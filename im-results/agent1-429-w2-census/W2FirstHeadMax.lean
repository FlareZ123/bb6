import W4JuncMax
import W4HeadPrefix
import BB429DeltaPhysicalBridge
import Lean.Elab.Tactic.Omega

set_option maxHeartbeats 30000000
set_option maxRecDepth 8192

namespace BB429W2FirstHeadMax

open BB6Coverage BB429OddExcursion BB429SourceE1Return BB429SourceE1Delta
open BB429FinishScanEDelta BB429JuncHeadExcursion
open BB429PhysicalFrontier BB429PhysicalBridge BB429DeltaPhysicalBridge
open BB429W4HeadMax BB429W4JuncMax BB429W4HeadPrefix

/-- The final nine steps of a right-two B/1 boundary visit exactly five
    cells to the right, and the C/0 endpoint attains that maximum.
    The left tail is arbitrary. -/
theorem b1_w2_to_czero9_max (tail : List Bool) :
    runWithMax 9 (z 1 (false :: true :: tail) true [true,false,true]) =
      some (z 2 (([true,false] ++ ones 5) ++ tail) false [], 5, 5) := by
  rfl

/-- The first C/0 of every right-two zero-left Junc is a genuine
    primitive-step head record, with a completely blank right tape. -/
theorem junc0_w2_first_czero_max (v : Nat) :
    runWithMax (2*v+35) (junc 0 v 2) =
      some (z 2 (([true,false] ++ ones 5) ++ (pairs01 (v+2) ++ ones 5)) false [],
        ((2*v+7 : Nat) : Int), ((2*v+7 : Nat) : Int)) := by
  have hprep := junc0_prep20_max v 2
  have hshift := shift_B01_max (v+2) (ones 5) [true,false,true]
  have htail := b1_w2_to_czero9_max (pairs01 (v+2) ++ ones 5)
  have hinput :
      z 1 (ones 5) false (true :: (pairs01 (v+2) ++ ones 2 ++ [false,true])) =
      z 1 (ones 5) false
        (true :: (pairs01 (v+2) ++ (true :: [true,false,true]))) := by
    simp [ones, List.append_assoc]
  have hpairs : pairs01 (v+3) =
      false :: true :: pairs01 (v+2) := by rfl
  have htail' :
      runWithMax 9 (z 1 (pairs01 (v+3) ++ ones 5) true [true,false,true]) =
      some (z 2 (([true,false] ++ ones 5) ++ (pairs01 (v+2) ++ ones 5))
        false [],5,5) := by
    rw [hpairs]
    simpa only [List.cons_append, List.append_assoc] using htail
  have htime : 2*v+35 = 20 + (2*((v+2)+1)+9) := by omega
  rw [htime,runWithMax_add,hprep]
  simp only [Option.bind_some]
  rw [hinput,runWithMax_add,hshift]
  simp only [Option.bind_some]
  rw [htail']
  simp only [Option.map_some,Option.some.injEq,Prod.mk.injEq]
  constructor
  · trivial
  · constructor <;> simp [Int.max_def] <;> omega

/-- Every source prefix up to the first right-two C/0 gate remains at or
    left of that gate's exact head coordinate. -/
theorem junc0_w2_first_gate_prefix_bound
    (v t : Nat) (ht : t ≤ 2*v+35) (c : Zipper) (delta : Int)
    (hrun : runWithDelta t (junc 0 v 2) = some (c,delta)) :
    delta ≤ ((2*v+7 : Nat) : Int) := by
  have hproj := runWithMax_toDelta t (junc 0 v 2)
  cases hm : runWithMax t (junc 0 v 2) with
  | none => simp [hm,hrun] at hproj
  | some p =>
      have hdelta : p.2.1 = delta := by
        simp [hm,hrun] at hproj
        exact hproj.2
      have hlen : t+(2*v+35-t) = 2*v+35 := by omega
      have hfull := junc0_w2_first_czero_max v
      rw [← hlen] at hfull
      have hmax := runWithMax_prefix_le t (2*v+35-t)
        (junc 0 v 2) p hm
        (z 2 (([true,false] ++ ones 5) ++ (pairs01 (v+2) ++ ones 5))
          false [], ((2*v+7 : Nat) : Int), ((2*v+7 : Nat) : Int)) hfull
      omega

/-- The head barrier holds in the original physical #429 Turing machine
    for all primitive prefixes and any physical tape representing the Junc. -/
theorem physical_junc0_w2_first_gate_prefix_bound
    (v t : Nat) (c : Config)
    (hrep : Represents (junc 0 v 2) c)
    (ht : t ≤ 2*v+35) :
    ∃ c', BB6Coverage.run BB429PhysicalFrontier.target429 t c = some c' ∧
      c'.head ≤ c.head + ((2*v+7 : Nat) : Int) := by
  have hfull : runWithDelta (2*v+35) (junc 0 v 2) =
      some (z 2 (([true,false] ++ ones 5) ++ (pairs01 (v+2) ++ ones 5))
        false [], ((2*v+7 : Nat) : Int)) := by
    rw [← runWithMax_toDelta, junc0_w2_first_czero_max]
    rfl
  have hlen : 2*v+35 = t+(2*v+35-t) := by omega
  cases hpre : runWithDelta t (junc 0 v 2) with
  | none =>
      rw [hlen,runWithDelta_add,hpre] at hfull
      simp at hfull
  | some p =>
      have hloc : p.2 ≤ ((2*v+7 : Nat) : Int) :=
        junc0_w2_first_gate_prefix_bound v t ht p.1 p.2 hpre
      obtain ⟨c',hr,hs,hd⟩ :=
        source_runWithDelta_rep t (junc 0 v 2) c hrep p.1 p.2 hpre
      refine ⟨c',hr,?_⟩
      omega

#print axioms b1_w2_to_czero9_max
#print axioms junc0_w2_first_czero_max
#print axioms junc0_w2_first_gate_prefix_bound
#print axioms physical_junc0_w2_first_gate_prefix_bound

end BB429W2FirstHeadMax
