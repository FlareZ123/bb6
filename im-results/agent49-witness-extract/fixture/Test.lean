import WitnessExtract
import Source
open BusyBeaver
example (x : Nat) : ReachesIn M 3 (cfg (0+x)) (cfg (x+3+0)) := by extract_cost t1Pub x
example (x : Nat) : ReachesIn M 5 (cfg (0+x)) (cfg (x+5+0)) := by extract_cost t2Pub x
example (x : Nat) : ReachesIn M 8 (cfg (0+x)) (cfg (x+8+0)) := by extract_cost combined x
-- wrong cost must fail
example (x : Nat) : ReachesIn M 3 (cfg (0+x)) (cfg (x+3+0)) := by
  fail_if_success (have : ReachesIn M 4 (cfg (0+x)) (cfg (x+3+0)) := by extract_cost t1Pub x)
  extract_cost t1Pub x
example (x : Nat) : ReachesIn M 3 (cfg (0+x)) (cfg (x+3+0)) := by
  extract_cost_from "t1" using [x]
example (x : Nat) : ReachesIn M 5 (cfg (0+x)) (cfg (x+5+0)) := by
  extract_cost_from "t2" using [x]
#extract_exact "t1" as T1Exact cost 3
#extract_exact "t2" as T2Exact cost 5
#extract_exact "combined" as CombinedExact cost 8
#check T1Exact
#check T2Exact
#check CombinedExact
#print axioms T1Exact
#print axioms T2Exact
#print axioms CombinedExact
#extract_induction "cycle" as CycleExact cost_by (fun k => 3*k)
#check CycleExact
#print axioms CycleExact
example (k x : Nat) : ReachesIn M (3*k) (cfg x) (cfg (x+3*k)) := CycleExact k x
#extract_composed "twoCycle" as TwoCycleExact using ["cycle" => CycleExact]
#check TwoCycleExact
#print axioms TwoCycleExact
example (k x : Nat) : ReachesIn M (3*k+3*k) (cfg x) (cfg (x+6*k)) := TwoCycleExact k x
