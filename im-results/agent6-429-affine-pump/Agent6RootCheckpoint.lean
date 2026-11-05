import BB429Rank
import Lean.Elab.Tactic.Omega

namespace Agent6RootCheckpoint
set_option maxRecDepth 200000
set_option maxHeartbeats 1000000000

/-! Exact blank-root prefix split into 28 independently kernel-checked segments.
    No custom trusted evaluator: each segment is proved with `by decide`. -/

private theorem segment_1 : BB429.run 10000 (0,0)=some (0,42260) := by decide
private theorem segment_2 : BB429.run 10000 (0,42260)=some (31081,21465) := by decide
private theorem segment_3 : BB429.run 10000 (31081,21465)=some (24573,71453) := by decide
private theorem segment_4 : BB429.run 10000 (24573,71453)=some (765,153738) := by decide
private theorem segment_5 : BB429.run 10000 (765,153738)=some (21,189895) := by decide
private theorem segment_6 : BB429.run 10000 (21,189895)=some (6141,219019) := by decide
private theorem segment_7 : BB429.run 10000 (6141,219019)=some (98301,75631) := by decide
private theorem segment_8 : BB429.run 10000 (98301,75631)=some (28669,257419) := by decide
private theorem segment_9 : BB429.run 10000 (28669,257419)=some (0,357264) := by decide
private theorem segment_10 : BB429.run 10000 (0,357264)=some (893,398020) := by decide
private theorem segment_11 : BB429.run 10000 (893,398020)=some (11,440062) := by decide
private theorem segment_12 : BB429.run 10000 (11,440062)=some (109,478495) := by decide
private theorem segment_13 : BB429.run 10000 (109,478495)=some (45,516118) := by decide
private theorem segment_14 : BB429.run 10000 (45,516118)=some (109,553495) := by decide
private theorem segment_15 : BB429.run 10000 (109,553495)=some (45,591118) := by decide
private theorem segment_16 : BB429.run 10000 (45,591118)=some (109,628495) := by decide
private theorem segment_17 : BB429.run 10000 (109,628495)=some (45,666118) := by decide
private theorem segment_18 : BB429.run 10000 (45,666118)=some (109,703495) := by decide
private theorem segment_19 : BB429.run 10000 (109,703495)=some (45,741118) := by decide
private theorem segment_20 : BB429.run 10000 (45,741118)=some (109,778495) := by decide
private theorem segment_21 : BB429.run 10000 (109,778495)=some (393213,28417) := by decide
private theorem segment_22 : BB429.run 10000 (393213,28417)=some (45,850550) := by decide
private theorem segment_23 : BB429.run 10000 (45,850550)=some (3069,880288) := by decide
private theorem segment_24 : BB429.run 10000 (3069,880288)=some (196605,529002) := by decide
private theorem segment_25 : BB429.run 10000 (196605,529002)=some (21,957967) := by decide
private theorem segment_26 : BB429.run 10000 (21,957967)=some (1533,990729) := by decide
private theorem segment_27 : BB429.run 10000 (1533,990729)=some (98301,832979) := by decide
private theorem segment_28 : BB429.run 5343 (98301,832979)=some (11,1048722) := by decide

private theorem cumulative_1 : BB429.run 10000 (0,0)=some (0,42260) := segment_1
private theorem cumulative_2 : BB429.run 20000 (0,0)=some (31081,21465) := by
  rw [show (20000:Nat)=10000+10000 by decide, BB429.run_add, cumulative_1]
  exact segment_2
private theorem cumulative_3 : BB429.run 30000 (0,0)=some (24573,71453) := by
  rw [show (30000:Nat)=20000+10000 by decide, BB429.run_add, cumulative_2]
  exact segment_3
private theorem cumulative_4 : BB429.run 40000 (0,0)=some (765,153738) := by
  rw [show (40000:Nat)=30000+10000 by decide, BB429.run_add, cumulative_3]
  exact segment_4
private theorem cumulative_5 : BB429.run 50000 (0,0)=some (21,189895) := by
  rw [show (50000:Nat)=40000+10000 by decide, BB429.run_add, cumulative_4]
  exact segment_5
private theorem cumulative_6 : BB429.run 60000 (0,0)=some (6141,219019) := by
  rw [show (60000:Nat)=50000+10000 by decide, BB429.run_add, cumulative_5]
  exact segment_6
private theorem cumulative_7 : BB429.run 70000 (0,0)=some (98301,75631) := by
  rw [show (70000:Nat)=60000+10000 by decide, BB429.run_add, cumulative_6]
  exact segment_7
private theorem cumulative_8 : BB429.run 80000 (0,0)=some (28669,257419) := by
  rw [show (80000:Nat)=70000+10000 by decide, BB429.run_add, cumulative_7]
  exact segment_8
private theorem cumulative_9 : BB429.run 90000 (0,0)=some (0,357264) := by
  rw [show (90000:Nat)=80000+10000 by decide, BB429.run_add, cumulative_8]
  exact segment_9
private theorem cumulative_10 : BB429.run 100000 (0,0)=some (893,398020) := by
  rw [show (100000:Nat)=90000+10000 by decide, BB429.run_add, cumulative_9]
  exact segment_10
private theorem cumulative_11 : BB429.run 110000 (0,0)=some (11,440062) := by
  rw [show (110000:Nat)=100000+10000 by decide, BB429.run_add, cumulative_10]
  exact segment_11
private theorem cumulative_12 : BB429.run 120000 (0,0)=some (109,478495) := by
  rw [show (120000:Nat)=110000+10000 by decide, BB429.run_add, cumulative_11]
  exact segment_12
private theorem cumulative_13 : BB429.run 130000 (0,0)=some (45,516118) := by
  rw [show (130000:Nat)=120000+10000 by decide, BB429.run_add, cumulative_12]
  exact segment_13
private theorem cumulative_14 : BB429.run 140000 (0,0)=some (109,553495) := by
  rw [show (140000:Nat)=130000+10000 by decide, BB429.run_add, cumulative_13]
  exact segment_14
private theorem cumulative_15 : BB429.run 150000 (0,0)=some (45,591118) := by
  rw [show (150000:Nat)=140000+10000 by decide, BB429.run_add, cumulative_14]
  exact segment_15
private theorem cumulative_16 : BB429.run 160000 (0,0)=some (109,628495) := by
  rw [show (160000:Nat)=150000+10000 by decide, BB429.run_add, cumulative_15]
  exact segment_16
private theorem cumulative_17 : BB429.run 170000 (0,0)=some (45,666118) := by
  rw [show (170000:Nat)=160000+10000 by decide, BB429.run_add, cumulative_16]
  exact segment_17
private theorem cumulative_18 : BB429.run 180000 (0,0)=some (109,703495) := by
  rw [show (180000:Nat)=170000+10000 by decide, BB429.run_add, cumulative_17]
  exact segment_18
private theorem cumulative_19 : BB429.run 190000 (0,0)=some (45,741118) := by
  rw [show (190000:Nat)=180000+10000 by decide, BB429.run_add, cumulative_18]
  exact segment_19
private theorem cumulative_20 : BB429.run 200000 (0,0)=some (109,778495) := by
  rw [show (200000:Nat)=190000+10000 by decide, BB429.run_add, cumulative_19]
  exact segment_20
private theorem cumulative_21 : BB429.run 210000 (0,0)=some (393213,28417) := by
  rw [show (210000:Nat)=200000+10000 by decide, BB429.run_add, cumulative_20]
  exact segment_21
private theorem cumulative_22 : BB429.run 220000 (0,0)=some (45,850550) := by
  rw [show (220000:Nat)=210000+10000 by decide, BB429.run_add, cumulative_21]
  exact segment_22
private theorem cumulative_23 : BB429.run 230000 (0,0)=some (3069,880288) := by
  rw [show (230000:Nat)=220000+10000 by decide, BB429.run_add, cumulative_22]
  exact segment_23
private theorem cumulative_24 : BB429.run 240000 (0,0)=some (196605,529002) := by
  rw [show (240000:Nat)=230000+10000 by decide, BB429.run_add, cumulative_23]
  exact segment_24
private theorem cumulative_25 : BB429.run 250000 (0,0)=some (21,957967) := by
  rw [show (250000:Nat)=240000+10000 by decide, BB429.run_add, cumulative_24]
  exact segment_25
private theorem cumulative_26 : BB429.run 260000 (0,0)=some (1533,990729) := by
  rw [show (260000:Nat)=250000+10000 by decide, BB429.run_add, cumulative_25]
  exact segment_26
private theorem cumulative_27 : BB429.run 270000 (0,0)=some (98301,832979) := by
  rw [show (270000:Nat)=260000+10000 by decide, BB429.run_add, cumulative_26]
  exact segment_27
private theorem cumulative_28 : BB429.run 275343 (0,0)=some (11,1048722) := by
  rw [show (275343:Nat)=270000+5343 by decide, BB429.run_add, cumulative_27]
  exact segment_28

/-- Complete kernel-checked source-map root prefix, if this generated module compiles end-to-end. -/
theorem rooted_at_pump : BB429.run 275343 (0,0)=some (11,1048722) := cumulative_28

#print axioms rooted_at_pump
end Agent6RootCheckpoint
