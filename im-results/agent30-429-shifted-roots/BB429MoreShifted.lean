import BB429ShiftRays
import Lean.Elab.Tactic.Omega

/-!
A single exact 240,000-macro-step *successful genuine blank-root checkpoint*
rules out every possible terminal state of lower rank, at every time.
Combine this finite-endpoint theorem with the already proved symbolic
all-parameter affine inverse certifier, eliminating nine further infinite
rays formerly surviving at modulus 262144. This reuse of the finite
checkpoint and inverse method is intended as an intermediate refinement.
-/
namespace BB429MoreShifted
open BB429NewResidue
set_option maxHeartbeats 60000000
set_option maxRecDepth 50000

/-- Any terminal of rank less than a certified surviving blank-run checkpoint
    is unreachable, including times later than the checkpoint. -/
theorem no_terminal_below_rank
    (N n a b : Nat) (s : BB429.State)
    (hN : BB429.run N (0,0) = some s)
    (hn : BB429.run n (0,0) = some (a,b))
    (hg : b+1=2*a)
    (hl : BB429.rank (a,b) < BB429.rank s) : False := by
  by_cases hearly : n < N
  · have hnext : BB429.next (a,b)=none :=
      (BB429.next_none_iff_halt_line a b).mpr hg
    have hstop : BB429.run (n+1) (0,0)=none := by
      change (BB429.run n (0,0)).bind BB429.next = none
      simp [hn, hnext]
    have heq : N=(n+1)+(N-(n+1)) := by omega
    rw [heq, BB429.run_add, hstop] at hN
    simp at hN
  · have heq : n=N+(n-N) := by omega
    rw [heq, BB429.run_add, hN] at hn
    simp only [Option.bind_some] at hn
    have hbound := (BB429.run_rank_bounds s (a,b) (n-N) hn).1
    omega

private theorem cp0 : BB429.run 0 (0,0)=some (0,0) := by decide

private theorem cp1000 : BB429.run 1000 (0,0)=some (53,4556) := by
  rw [show (1000:Nat)=0+1000 by decide, BB429.run_add, cp0]
  decide

private theorem cp2000 : BB429.run 2000 (0,0)=some (189,8264) := by
  rw [show (2000:Nat)=1000+1000 by decide, BB429.run_add, cp1000]
  decide

private theorem cp3000 : BB429.run 3000 (0,0)=some (93,12093) := by
  rw [show (3000:Nat)=2000+1000 by decide, BB429.run_add, cp2000]
  decide

private theorem cp4000 : BB429.run 4000 (0,0)=some (0,16916) := by
  rw [show (4000:Nat)=3000+1000 by decide, BB429.run_add, cp3000]
  decide

private theorem cp5000 : BB429.run 5000 (0,0)=some (45,21462) := by
  rw [show (5000:Nat)=4000+1000 by decide, BB429.run_add, cp4000]
  decide

private theorem cp6000 : BB429.run 6000 (0,0)=some (1789,22515) := by
  rw [show (6000:Nat)=5000+1000 by decide, BB429.run_add, cp5000]
  decide

private theorem cp7000 : BB429.run 7000 (0,0)=some (0,30260) := by
  rw [show (7000:Nat)=6000+1000 by decide, BB429.run_add, cp6000]
  decide

private theorem cp8000 : BB429.run 8000 (0,0)=some (109,34043) := by
  rw [show (8000:Nat)=7000+1000 by decide, BB429.run_add, cp7000]
  decide

private theorem cp9000 : BB429.run 9000 (0,0)=some (765,36722) := by
  rw [show (9000:Nat)=8000+1000 by decide, BB429.run_add, cp8000]
  decide

private theorem cp10000 : BB429.run 10000 (0,0)=some (0,42260) := by
  rw [show (10000:Nat)=9000+1000 by decide, BB429.run_add, cp9000]
  decide

private theorem cp11000 : BB429.run 11000 (0,0)=some (109,46043) := by
  rw [show (11000:Nat)=10000+1000 by decide, BB429.run_add, cp10000]
  decide

private theorem cp12000 : BB429.run 12000 (0,0)=some (9,50168) := by
  rw [show (12000:Nat)=11000+1000 by decide, BB429.run_add, cp11000]
  decide

private theorem cp13000 : BB429.run 13000 (0,0)=some (12285,29342) := by
  rw [show (13000:Nat)=12000+1000 by decide, BB429.run_add, cp12000]
  decide

private theorem cp14000 : BB429.run 14000 (0,0)=some (381,56887) := by
  rw [show (14000:Nat)=13000+1000 by decide, BB429.run_add, cp13000]
  decide

private theorem cp15000 : BB429.run 15000 (0,0)=some (9,61368) := by
  rw [show (15000:Nat)=14000+1000 by decide, BB429.run_add, cp14000]
  decide

private theorem cp16000 : BB429.run 16000 (0,0)=some (12285,40542) := by
  rw [show (16000:Nat)=15000+1000 by decide, BB429.run_add, cp15000]
  decide

private theorem cp17000 : BB429.run 17000 (0,0)=some (221,69462) := by
  rw [show (17000:Nat)=16000+1000 by decide, BB429.run_add, cp16000]
  decide

private theorem cp18000 : BB429.run 18000 (0,0)=some (109,74611) := by
  rw [show (18000:Nat)=17000+1000 by decide, BB429.run_add, cp17000]
  decide

private theorem cp19000 : BB429.run 19000 (0,0)=some (381,78599) := by
  rw [show (19000:Nat)=18000+1000 by decide, BB429.run_add, cp18000]
  decide

private theorem cp20000 : BB429.run 20000 (0,0)=some (31081,21465) := by
  rw [show (20000:Nat)=19000+1000 by decide, BB429.run_add, cp19000]
  decide

private theorem cp21000 : BB429.run 21000 (0,0)=some (10071,68099) := by
  rw [show (21000:Nat)=20000+1000 by decide, BB429.run_add, cp20000]
  decide

private theorem cp22000 : BB429.run 22000 (0,0)=some (5995,80327) := by
  rw [show (22000:Nat)=21000+1000 by decide, BB429.run_add, cp21000]
  decide

private theorem cp23000 : BB429.run 23000 (0,0)=some (3581,88870) := by
  rw [show (23000:Nat)=22000+1000 by decide, BB429.run_add, cp22000]
  decide

private theorem cp24000 : BB429.run 24000 (0,0)=some (24573,50653) := by
  rw [show (24000:Nat)=23000+1000 by decide, BB429.run_add, cp23000]
  decide

private theorem cp25000 : BB429.run 25000 (0,0)=some (765,101738) := by
  rw [show (25000:Nat)=24000+1000 by decide, BB429.run_add, cp24000]
  decide

private theorem cp26000 : BB429.run 26000 (0,0)=some (21,106695) := by
  rw [show (26000:Nat)=25000+1000 by decide, BB429.run_add, cp25000]
  decide

private theorem cp27000 : BB429.run 27000 (0,0)=some (24573,61053) := by
  rw [show (27000:Nat)=26000+1000 by decide, BB429.run_add, cp26000]
  decide

private theorem cp28000 : BB429.run 28000 (0,0)=some (765,112138) := by
  rw [show (28000:Nat)=27000+1000 by decide, BB429.run_add, cp27000]
  decide

private theorem cp29000 : BB429.run 29000 (0,0)=some (21,117095) := by
  rw [show (29000:Nat)=28000+1000 by decide, BB429.run_add, cp28000]
  decide

private theorem cp30000 : BB429.run 30000 (0,0)=some (24573,71453) := by
  rw [show (30000:Nat)=29000+1000 by decide, BB429.run_add, cp29000]
  decide

private theorem cp31000 : BB429.run 31000 (0,0)=some (765,122538) := by
  rw [show (31000:Nat)=30000+1000 by decide, BB429.run_add, cp30000]
  decide

private theorem cp32000 : BB429.run 32000 (0,0)=some (21,127495) := by
  rw [show (32000:Nat)=31000+1000 by decide, BB429.run_add, cp31000]
  decide

private theorem cp33000 : BB429.run 33000 (0,0)=some (24573,81853) := by
  rw [show (33000:Nat)=32000+1000 by decide, BB429.run_add, cp32000]
  decide

private theorem cp34000 : BB429.run 34000 (0,0)=some (765,132938) := by
  rw [show (34000:Nat)=33000+1000 by decide, BB429.run_add, cp33000]
  decide

private theorem cp35000 : BB429.run 35000 (0,0)=some (21,137895) := by
  rw [show (35000:Nat)=34000+1000 by decide, BB429.run_add, cp34000]
  decide

private theorem cp36000 : BB429.run 36000 (0,0)=some (24573,92253) := by
  rw [show (36000:Nat)=35000+1000 by decide, BB429.run_add, cp35000]
  decide

private theorem cp37000 : BB429.run 37000 (0,0)=some (765,143338) := by
  rw [show (37000:Nat)=36000+1000 by decide, BB429.run_add, cp36000]
  decide

private theorem cp38000 : BB429.run 38000 (0,0)=some (21,148295) := by
  rw [show (38000:Nat)=37000+1000 by decide, BB429.run_add, cp37000]
  decide

private theorem cp39000 : BB429.run 39000 (0,0)=some (24573,102653) := by
  rw [show (39000:Nat)=38000+1000 by decide, BB429.run_add, cp38000]
  decide

private theorem cp40000 : BB429.run 40000 (0,0)=some (765,153738) := by
  rw [show (40000:Nat)=39000+1000 by decide, BB429.run_add, cp39000]
  decide

private theorem cp41000 : BB429.run 41000 (0,0)=some (21,158695) := by
  rw [show (41000:Nat)=40000+1000 by decide, BB429.run_add, cp40000]
  decide

private theorem cp42000 : BB429.run 42000 (0,0)=some (24573,113053) := by
  rw [show (42000:Nat)=41000+1000 by decide, BB429.run_add, cp41000]
  decide

private theorem cp43000 : BB429.run 43000 (0,0)=some (765,164138) := by
  rw [show (43000:Nat)=42000+1000 by decide, BB429.run_add, cp42000]
  decide

private theorem cp44000 : BB429.run 44000 (0,0)=some (21,169095) := by
  rw [show (44000:Nat)=43000+1000 by decide, BB429.run_add, cp43000]
  decide

private theorem cp45000 : BB429.run 45000 (0,0)=some (24573,123453) := by
  rw [show (45000:Nat)=44000+1000 by decide, BB429.run_add, cp44000]
  decide

private theorem cp46000 : BB429.run 46000 (0,0)=some (765,174538) := by
  rw [show (46000:Nat)=45000+1000 by decide, BB429.run_add, cp45000]
  decide

private theorem cp47000 : BB429.run 47000 (0,0)=some (21,179495) := by
  rw [show (47000:Nat)=46000+1000 by decide, BB429.run_add, cp46000]
  decide

private theorem cp48000 : BB429.run 48000 (0,0)=some (24573,133853) := by
  rw [show (48000:Nat)=47000+1000 by decide, BB429.run_add, cp47000]
  decide

private theorem cp49000 : BB429.run 49000 (0,0)=some (765,184938) := by
  rw [show (49000:Nat)=48000+1000 by decide, BB429.run_add, cp48000]
  decide

private theorem cp50000 : BB429.run 50000 (0,0)=some (21,189895) := by
  rw [show (50000:Nat)=49000+1000 by decide, BB429.run_add, cp49000]
  decide

private theorem cp51000 : BB429.run 51000 (0,0)=some (24573,144253) := by
  rw [show (51000:Nat)=50000+1000 by decide, BB429.run_add, cp50000]
  decide

private theorem cp52000 : BB429.run 52000 (0,0)=some (25,196893) := by
  rw [show (52000:Nat)=51000+1000 by decide, BB429.run_add, cp51000]
  decide

private theorem cp53000 : BB429.run 53000 (0,0)=some (11,201230) := by
  rw [show (53000:Nat)=52000+1000 by decide, BB429.run_add, cp52000]
  decide

private theorem cp54000 : BB429.run 54000 (0,0)=some (57341,90862) := by
  rw [show (54000:Nat)=53000+1000 by decide, BB429.run_add, cp53000]
  decide

private theorem cp55000 : BB429.run 55000 (0,0)=some (28669,152515) := by
  rw [show (55000:Nat)=54000+1000 by decide, BB429.run_add, cp54000]
  decide

private theorem cp56000 : BB429.run 56000 (0,0)=some (14333,185496) := by
  rw [show (56000:Nat)=55000+1000 by decide, BB429.run_add, cp55000]
  decide

private theorem cp57000 : BB429.run 57000 (0,0)=some (7165,204141) := by
  rw [show (57000:Nat)=56000+1000 by decide, BB429.run_add, cp56000]
  decide

private theorem cp58000 : BB429.run 58000 (0,0)=some (3581,215618) := by
  rw [show (58000:Nat)=57000+1000 by decide, BB429.run_add, cp57000]
  decide

private theorem cp59000 : BB429.run 59000 (0,0)=some (1789,223511) := by
  rw [show (59000:Nat)=58000+1000 by decide, BB429.run_add, cp58000]
  decide

private theorem cp60000 : BB429.run 60000 (0,0)=some (6141,219019) := by
  rw [show (60000:Nat)=59000+1000 by decide, BB429.run_add, cp59000]
  decide

private theorem cp61000 : BB429.run 61000 (0,0)=some (53,235336) := by
  rw [show (61000:Nat)=60000+1000 by decide, BB429.run_add, cp60000]
  decide

private theorem cp62000 : BB429.run 62000 (0,0)=some (14333,210892) := by
  rw [show (62000:Nat)=61000+1000 by decide, BB429.run_add, cp61000]
  decide

private theorem cp63000 : BB429.run 63000 (0,0)=some (21,243643) := by
  rw [show (63000:Nat)=62000+1000 by decide, BB429.run_add, cp62000]
  decide

private theorem cp64000 : BB429.run 64000 (0,0)=some (6141,235519) := by
  rw [show (64000:Nat)=63000+1000 by decide, BB429.run_add, cp63000]
  decide

private theorem cp65000 : BB429.run 65000 (0,0)=some (53,251836) := by
  rw [show (65000:Nat)=64000+1000 by decide, BB429.run_add, cp64000]
  decide

private theorem cp66000 : BB429.run 66000 (0,0)=some (14333,227392) := by
  rw [show (66000:Nat)=65000+1000 by decide, BB429.run_add, cp65000]
  decide

private theorem cp67000 : BB429.run 67000 (0,0)=some (21,260143) := by
  rw [show (67000:Nat)=66000+1000 by decide, BB429.run_add, cp66000]
  decide

private theorem cp68000 : BB429.run 68000 (0,0)=some (3069,258100) := by
  rw [show (68000:Nat)=67000+1000 by decide, BB429.run_add, cp67000]
  decide

private theorem cp69000 : BB429.run 69000 (0,0)=some (21,268203) := by
  rw [show (69000:Nat)=68000+1000 by decide, BB429.run_add, cp68000]
  decide

private theorem cp70000 : BB429.run 70000 (0,0)=some (98301,75631) := by
  rw [show (70000:Nat)=69000+1000 by decide, BB429.run_add, cp69000]
  decide

private theorem cp71000 : BB429.run 71000 (0,0)=some (765,274710) := by
  rw [show (71000:Nat)=70000+1000 by decide, BB429.run_add, cp70000]
  decide

private theorem cp72000 : BB429.run 72000 (0,0)=some (3,280241) := by
  rw [show (72000:Nat)=71000+1000 by decide, BB429.run_add, cp71000]
  decide

private theorem cp73000 : BB429.run 73000 (0,0)=some (24573,235089) := by
  rw [show (73000:Nat)=72000+1000 by decide, BB429.run_add, cp72000]
  decide

private theorem cp74000 : BB429.run 74000 (0,0)=some (0,288440) := by
  rw [show (74000:Nat)=73000+1000 by decide, BB429.run_add, cp73000]
  decide

private theorem cp75000 : BB429.run 75000 (0,0)=some (93,292581) := by
  rw [show (75000:Nat)=74000+1000 by decide, BB429.run_add, cp74000]
  decide

private theorem cp76000 : BB429.run 76000 (0,0)=some (87499,122103) := by
  rw [show (76000:Nat)=75000+1000 by decide, BB429.run_add, cp75000]
  decide

private theorem cp77000 : BB429.run 77000 (0,0)=some (78726,143850) := by
  rw [show (77000:Nat)=76000+1000 by decide, BB429.run_add, cp76000]
  decide

private theorem cp78000 : BB429.run 78000 (0,0)=some (893,303632) := by
  rw [show (78000:Nat)=77000+1000 by decide, BB429.run_add, cp77000]
  decide

private theorem cp79000 : BB429.run 79000 (0,0)=some (74352,161346) := by
  rw [show (79000:Nat)=78000+1000 by decide, BB429.run_add, cp78000]
  decide

private theorem cp80000 : BB429.run 80000 (0,0)=some (28669,257419) := by
  rw [show (80000:Nat)=79000+1000 by decide, BB429.run_add, cp79000]
  decide

private theorem cp81000 : BB429.run 81000 (0,0)=some (3581,312306) := by
  rw [show (81000:Nat)=80000+1000 by decide, BB429.run_add, cp80000]
  decide

private theorem cp82000 : BB429.run 82000 (0,0)=some (445,323289) := by
  rw [show (82000:Nat)=81000+1000 by decide, BB429.run_add, cp81000]
  decide

private theorem cp83000 : BB429.run 83000 (0,0)=some (53,328784) := by
  rw [show (83000:Nat)=82000+1000 by decide, BB429.run_add, cp82000]
  decide

private theorem cp84000 : BB429.run 84000 (0,0)=some (83595,166394) := by
  rw [show (84000:Nat)=83000+1000 by decide, BB429.run_add, cp83000]
  decide

private theorem cp85000 : BB429.run 85000 (0,0)=some (6141,325107) := by
  rw [show (85000:Nat)=84000+1000 by decide, BB429.run_add, cp84000]
  decide

private theorem cp86000 : BB429.run 86000 (0,0)=some (45,341094) := by
  rw [show (86000:Nat)=85000+1000 by decide, BB429.run_add, cp85000]
  decide

private theorem cp87000 : BB429.run 87000 (0,0)=some (24129,296714) := by
  rw [show (87000:Nat)=86000+1000 by decide, BB429.run_add, cp86000]
  decide

private theorem cp88000 : BB429.run 88000 (0,0)=some (1533,345693) := by
  rw [show (88000:Nat)=87000+1000 by decide, BB429.run_add, cp87000]
  decide

private theorem cp89000 : BB429.run 89000 (0,0)=some (0,352964) := by
  rw [show (89000:Nat)=88000+1000 by decide, BB429.run_add, cp88000]
  decide

private theorem cp90000 : BB429.run 90000 (0,0)=some (0,357264) := by
  rw [show (90000:Nat)=89000+1000 by decide, BB429.run_add, cp89000]
  decide

private theorem cp91000 : BB429.run 91000 (0,0)=some (12285,337158) := by
  rw [show (91000:Nat)=90000+1000 by decide, BB429.run_add, cp90000]
  decide

private theorem cp92000 : BB429.run 92000 (0,0)=some (98301,169387) := by
  rw [show (92000:Nat)=91000+1000 by decide, BB429.run_add, cp91000]
  decide

private theorem cp93000 : BB429.run 93000 (0,0)=some (14333,341488) := by
  rw [show (93000:Nat)=92000+1000 by decide, BB429.run_add, cp92000]
  decide

private theorem cp94000 : BB429.run 94000 (0,0)=some (1789,370815) := by
  rw [show (94000:Nat)=93000+1000 by decide, BB429.run_add, cp93000]
  decide

private theorem cp95000 : BB429.run 95000 (0,0)=some (221,378190) := by
  rw [show (95000:Nat)=94000+1000 by decide, BB429.run_add, cp94000]
  decide

private theorem cp96000 : BB429.run 96000 (0,0)=some (25,382821) := by
  rw [show (96000:Nat)=95000+1000 by decide, BB429.run_add, cp95000]
  decide

private theorem cp97000 : BB429.run 97000 (0,0)=some (71667,243759) := by
  rw [show (97000:Nat)=96000+1000 by decide, BB429.run_add, cp96000]
  decide

private theorem cp98000 : BB429.run 98000 (0,0)=some (57341,276646) := by
  rw [show (98000:Nat)=97000+1000 by decide, BB429.run_add, cp97000]
  decide

private theorem cp99000 : BB429.run 99000 (0,0)=some (7165,381237) := by
  rw [show (99000:Nat)=98000+1000 by decide, BB429.run_add, cp98000]
  decide

private theorem cp100000 : BB429.run 100000 (0,0)=some (893,398020) := by
  rw [show (100000:Nat)=99000+1000 by decide, BB429.run_add, cp99000]
  decide

private theorem cp101000 : BB429.run 101000 (0,0)=some (109,403827) := by
  rw [show (101000:Nat)=100000+1000 by decide, BB429.run_add, cp100000]
  decide

private theorem cp102000 : BB429.run 102000 (0,0)=some (28669,350895) := by
  rw [show (102000:Nat)=101000+1000 by decide, BB429.run_add, cp101000]
  decide

private theorem cp103000 : BB429.run 103000 (0,0)=some (109,411911) := by
  rw [show (103000:Nat)=102000+1000 by decide, BB429.run_add, cp102000]
  decide

private theorem cp104000 : BB429.run 104000 (0,0)=some (12285,391438) := by
  rw [show (104000:Nat)=103000+1000 by decide, BB429.run_add, cp103000]
  decide

private theorem cp105000 : BB429.run 105000 (0,0)=some (445,419101) := by
  rw [show (105000:Nat)=104000+1000 by decide, BB429.run_add, cp104000]
  decide

private theorem cp106000 : BB429.run 106000 (0,0)=some (765,422866) := by
  rw [show (106000:Nat)=105000+1000 by decide, BB429.run_add, cp105000]
  decide

private theorem cp107000 : BB429.run 107000 (0,0)=some (445,427693) := by
  rw [show (107000:Nat)=106000+1000 by decide, BB429.run_add, cp106000]
  decide

private theorem cp108000 : BB429.run 108000 (0,0)=some (52489,327542) := by
  rw [show (108000:Nat)=107000+1000 by decide, BB429.run_add, cp107000]
  decide

private theorem cp109000 : BB429.run 109000 (0,0)=some (3581,429138) := by
  rw [show (109000:Nat)=108000+1000 by decide, BB429.run_add, cp108000]
  decide

private theorem cp110000 : BB429.run 110000 (0,0)=some (11,440062) := by
  rw [show (110000:Nat)=109000+1000 by decide, BB429.run_add, cp109000]
  decide

private theorem cp111000 : BB429.run 111000 (0,0)=some (1533,440785) := by
  rw [show (111000:Nat)=110000+1000 by decide, BB429.run_add, cp110000]
  decide

private theorem cp112000 : BB429.run 112000 (0,0)=some (445,447189) := by
  rw [show (112000:Nat)=111000+1000 by decide, BB429.run_add, cp111000]
  decide

private theorem cp113000 : BB429.run 113000 (0,0)=some (445,451269) := by
  rw [show (113000:Nat)=112000+1000 by decide, BB429.run_add, cp112000]
  decide

private theorem cp114000 : BB429.run 114000 (0,0)=some (7165,441777) := by
  rw [show (114000:Nat)=113000+1000 by decide, BB429.run_add, cp113000]
  decide

private theorem cp115000 : BB429.run 115000 (0,0)=some (12285,435382) := by
  rw [show (115000:Nat)=114000+1000 by decide, BB429.run_add, cp114000]
  decide

private theorem cp116000 : BB429.run 116000 (0,0)=some (109,463495) := by
  rw [show (116000:Nat)=115000+1000 by decide, BB429.run_add, cp115000]
  decide

private theorem cp117000 : BB429.run 117000 (0,0)=some (28669,410119) := by
  rw [show (117000:Nat)=116000+1000 by decide, BB429.run_add, cp116000]
  decide

private theorem cp118000 : BB429.run 118000 (0,0)=some (45,471118) := by
  rw [show (118000:Nat)=117000+1000 by decide, BB429.run_add, cp117000]
  decide

private theorem cp119000 : BB429.run 119000 (0,0)=some (12285,450382) := by
  rw [show (119000:Nat)=118000+1000 by decide, BB429.run_add, cp118000]
  decide

private theorem cp120000 : BB429.run 120000 (0,0)=some (109,478495) := by
  rw [show (120000:Nat)=119000+1000 by decide, BB429.run_add, cp119000]
  decide

private theorem cp121000 : BB429.run 121000 (0,0)=some (28669,425119) := by
  rw [show (121000:Nat)=120000+1000 by decide, BB429.run_add, cp120000]
  decide

private theorem cp122000 : BB429.run 122000 (0,0)=some (45,486118) := by
  rw [show (122000:Nat)=121000+1000 by decide, BB429.run_add, cp121000]
  decide

private theorem cp123000 : BB429.run 123000 (0,0)=some (12285,465382) := by
  rw [show (123000:Nat)=122000+1000 by decide, BB429.run_add, cp122000]
  decide

private theorem cp124000 : BB429.run 124000 (0,0)=some (109,493495) := by
  rw [show (124000:Nat)=123000+1000 by decide, BB429.run_add, cp123000]
  decide

private theorem cp125000 : BB429.run 125000 (0,0)=some (28669,440119) := by
  rw [show (125000:Nat)=124000+1000 by decide, BB429.run_add, cp124000]
  decide

private theorem cp126000 : BB429.run 126000 (0,0)=some (45,501118) := by
  rw [show (126000:Nat)=125000+1000 by decide, BB429.run_add, cp125000]
  decide

private theorem cp127000 : BB429.run 127000 (0,0)=some (12285,480382) := by
  rw [show (127000:Nat)=126000+1000 by decide, BB429.run_add, cp126000]
  decide

private theorem cp128000 : BB429.run 128000 (0,0)=some (109,508495) := by
  rw [show (128000:Nat)=127000+1000 by decide, BB429.run_add, cp127000]
  decide

private theorem cp129000 : BB429.run 129000 (0,0)=some (28669,455119) := by
  rw [show (129000:Nat)=128000+1000 by decide, BB429.run_add, cp128000]
  decide

private theorem cp130000 : BB429.run 130000 (0,0)=some (45,516118) := by
  rw [show (130000:Nat)=129000+1000 by decide, BB429.run_add, cp129000]
  decide

private theorem cp131000 : BB429.run 131000 (0,0)=some (12285,495382) := by
  rw [show (131000:Nat)=130000+1000 by decide, BB429.run_add, cp130000]
  decide

private theorem cp132000 : BB429.run 132000 (0,0)=some (109,523495) := by
  rw [show (132000:Nat)=131000+1000 by decide, BB429.run_add, cp131000]
  decide

private theorem cp133000 : BB429.run 133000 (0,0)=some (28669,470119) := by
  rw [show (133000:Nat)=132000+1000 by decide, BB429.run_add, cp132000]
  decide

private theorem cp134000 : BB429.run 134000 (0,0)=some (45,531118) := by
  rw [show (134000:Nat)=133000+1000 by decide, BB429.run_add, cp133000]
  decide

private theorem cp135000 : BB429.run 135000 (0,0)=some (12285,510382) := by
  rw [show (135000:Nat)=134000+1000 by decide, BB429.run_add, cp134000]
  decide

private theorem cp136000 : BB429.run 136000 (0,0)=some (109,538495) := by
  rw [show (136000:Nat)=135000+1000 by decide, BB429.run_add, cp135000]
  decide

private theorem cp137000 : BB429.run 137000 (0,0)=some (28669,485119) := by
  rw [show (137000:Nat)=136000+1000 by decide, BB429.run_add, cp136000]
  decide

private theorem cp138000 : BB429.run 138000 (0,0)=some (45,546118) := by
  rw [show (138000:Nat)=137000+1000 by decide, BB429.run_add, cp137000]
  decide

private theorem cp139000 : BB429.run 139000 (0,0)=some (12285,525382) := by
  rw [show (139000:Nat)=138000+1000 by decide, BB429.run_add, cp138000]
  decide

private theorem cp140000 : BB429.run 140000 (0,0)=some (109,553495) := by
  rw [show (140000:Nat)=139000+1000 by decide, BB429.run_add, cp139000]
  decide

private theorem cp141000 : BB429.run 141000 (0,0)=some (28669,500119) := by
  rw [show (141000:Nat)=140000+1000 by decide, BB429.run_add, cp140000]
  decide

private theorem cp142000 : BB429.run 142000 (0,0)=some (45,561118) := by
  rw [show (142000:Nat)=141000+1000 by decide, BB429.run_add, cp141000]
  decide

private theorem cp143000 : BB429.run 143000 (0,0)=some (12285,540382) := by
  rw [show (143000:Nat)=142000+1000 by decide, BB429.run_add, cp142000]
  decide

private theorem cp144000 : BB429.run 144000 (0,0)=some (109,568495) := by
  rw [show (144000:Nat)=143000+1000 by decide, BB429.run_add, cp143000]
  decide

private theorem cp145000 : BB429.run 145000 (0,0)=some (28669,515119) := by
  rw [show (145000:Nat)=144000+1000 by decide, BB429.run_add, cp144000]
  decide

private theorem cp146000 : BB429.run 146000 (0,0)=some (45,576118) := by
  rw [show (146000:Nat)=145000+1000 by decide, BB429.run_add, cp145000]
  decide

private theorem cp147000 : BB429.run 147000 (0,0)=some (12285,555382) := by
  rw [show (147000:Nat)=146000+1000 by decide, BB429.run_add, cp146000]
  decide

private theorem cp148000 : BB429.run 148000 (0,0)=some (109,583495) := by
  rw [show (148000:Nat)=147000+1000 by decide, BB429.run_add, cp147000]
  decide

private theorem cp149000 : BB429.run 149000 (0,0)=some (28669,530119) := by
  rw [show (149000:Nat)=148000+1000 by decide, BB429.run_add, cp148000]
  decide

private theorem cp150000 : BB429.run 150000 (0,0)=some (45,591118) := by
  rw [show (150000:Nat)=149000+1000 by decide, BB429.run_add, cp149000]
  decide

private theorem cp151000 : BB429.run 151000 (0,0)=some (12285,570382) := by
  rw [show (151000:Nat)=150000+1000 by decide, BB429.run_add, cp150000]
  decide

private theorem cp152000 : BB429.run 152000 (0,0)=some (109,598495) := by
  rw [show (152000:Nat)=151000+1000 by decide, BB429.run_add, cp151000]
  decide

private theorem cp153000 : BB429.run 153000 (0,0)=some (28669,545119) := by
  rw [show (153000:Nat)=152000+1000 by decide, BB429.run_add, cp152000]
  decide

private theorem cp154000 : BB429.run 154000 (0,0)=some (45,606118) := by
  rw [show (154000:Nat)=153000+1000 by decide, BB429.run_add, cp153000]
  decide

private theorem cp155000 : BB429.run 155000 (0,0)=some (12285,585382) := by
  rw [show (155000:Nat)=154000+1000 by decide, BB429.run_add, cp154000]
  decide

private theorem cp156000 : BB429.run 156000 (0,0)=some (109,613495) := by
  rw [show (156000:Nat)=155000+1000 by decide, BB429.run_add, cp155000]
  decide

private theorem cp157000 : BB429.run 157000 (0,0)=some (28669,560119) := by
  rw [show (157000:Nat)=156000+1000 by decide, BB429.run_add, cp156000]
  decide

private theorem cp158000 : BB429.run 158000 (0,0)=some (45,621118) := by
  rw [show (158000:Nat)=157000+1000 by decide, BB429.run_add, cp157000]
  decide

private theorem cp159000 : BB429.run 159000 (0,0)=some (12285,600382) := by
  rw [show (159000:Nat)=158000+1000 by decide, BB429.run_add, cp158000]
  decide

private theorem cp160000 : BB429.run 160000 (0,0)=some (109,628495) := by
  rw [show (160000:Nat)=159000+1000 by decide, BB429.run_add, cp159000]
  decide

private theorem cp161000 : BB429.run 161000 (0,0)=some (28669,575119) := by
  rw [show (161000:Nat)=160000+1000 by decide, BB429.run_add, cp160000]
  decide

private theorem cp162000 : BB429.run 162000 (0,0)=some (45,636118) := by
  rw [show (162000:Nat)=161000+1000 by decide, BB429.run_add, cp161000]
  decide

private theorem cp163000 : BB429.run 163000 (0,0)=some (12285,615382) := by
  rw [show (163000:Nat)=162000+1000 by decide, BB429.run_add, cp162000]
  decide

private theorem cp164000 : BB429.run 164000 (0,0)=some (109,643495) := by
  rw [show (164000:Nat)=163000+1000 by decide, BB429.run_add, cp163000]
  decide

private theorem cp165000 : BB429.run 165000 (0,0)=some (28669,590119) := by
  rw [show (165000:Nat)=164000+1000 by decide, BB429.run_add, cp164000]
  decide

private theorem cp166000 : BB429.run 166000 (0,0)=some (45,651118) := by
  rw [show (166000:Nat)=165000+1000 by decide, BB429.run_add, cp165000]
  decide

private theorem cp167000 : BB429.run 167000 (0,0)=some (12285,630382) := by
  rw [show (167000:Nat)=166000+1000 by decide, BB429.run_add, cp166000]
  decide

private theorem cp168000 : BB429.run 168000 (0,0)=some (109,658495) := by
  rw [show (168000:Nat)=167000+1000 by decide, BB429.run_add, cp167000]
  decide

private theorem cp169000 : BB429.run 169000 (0,0)=some (28669,605119) := by
  rw [show (169000:Nat)=168000+1000 by decide, BB429.run_add, cp168000]
  decide

private theorem cp170000 : BB429.run 170000 (0,0)=some (45,666118) := by
  rw [show (170000:Nat)=169000+1000 by decide, BB429.run_add, cp169000]
  decide

private theorem cp171000 : BB429.run 171000 (0,0)=some (12285,645382) := by
  rw [show (171000:Nat)=170000+1000 by decide, BB429.run_add, cp170000]
  decide

private theorem cp172000 : BB429.run 172000 (0,0)=some (109,673495) := by
  rw [show (172000:Nat)=171000+1000 by decide, BB429.run_add, cp171000]
  decide

private theorem cp173000 : BB429.run 173000 (0,0)=some (28669,620119) := by
  rw [show (173000:Nat)=172000+1000 by decide, BB429.run_add, cp172000]
  decide

private theorem cp174000 : BB429.run 174000 (0,0)=some (45,681118) := by
  rw [show (174000:Nat)=173000+1000 by decide, BB429.run_add, cp173000]
  decide

private theorem cp175000 : BB429.run 175000 (0,0)=some (12285,660382) := by
  rw [show (175000:Nat)=174000+1000 by decide, BB429.run_add, cp174000]
  decide

private theorem cp176000 : BB429.run 176000 (0,0)=some (109,688495) := by
  rw [show (176000:Nat)=175000+1000 by decide, BB429.run_add, cp175000]
  decide

private theorem cp177000 : BB429.run 177000 (0,0)=some (28669,635119) := by
  rw [show (177000:Nat)=176000+1000 by decide, BB429.run_add, cp176000]
  decide

private theorem cp178000 : BB429.run 178000 (0,0)=some (45,696118) := by
  rw [show (178000:Nat)=177000+1000 by decide, BB429.run_add, cp177000]
  decide

private theorem cp179000 : BB429.run 179000 (0,0)=some (12285,675382) := by
  rw [show (179000:Nat)=178000+1000 by decide, BB429.run_add, cp178000]
  decide

private theorem cp180000 : BB429.run 180000 (0,0)=some (109,703495) := by
  rw [show (180000:Nat)=179000+1000 by decide, BB429.run_add, cp179000]
  decide

private theorem cp181000 : BB429.run 181000 (0,0)=some (28669,650119) := by
  rw [show (181000:Nat)=180000+1000 by decide, BB429.run_add, cp180000]
  decide

private theorem cp182000 : BB429.run 182000 (0,0)=some (45,711118) := by
  rw [show (182000:Nat)=181000+1000 by decide, BB429.run_add, cp181000]
  decide

private theorem cp183000 : BB429.run 183000 (0,0)=some (12285,690382) := by
  rw [show (183000:Nat)=182000+1000 by decide, BB429.run_add, cp182000]
  decide

private theorem cp184000 : BB429.run 184000 (0,0)=some (109,718495) := by
  rw [show (184000:Nat)=183000+1000 by decide, BB429.run_add, cp183000]
  decide

private theorem cp185000 : BB429.run 185000 (0,0)=some (28669,665119) := by
  rw [show (185000:Nat)=184000+1000 by decide, BB429.run_add, cp184000]
  decide

private theorem cp186000 : BB429.run 186000 (0,0)=some (45,726118) := by
  rw [show (186000:Nat)=185000+1000 by decide, BB429.run_add, cp185000]
  decide

private theorem cp187000 : BB429.run 187000 (0,0)=some (12285,705382) := by
  rw [show (187000:Nat)=186000+1000 by decide, BB429.run_add, cp186000]
  decide

private theorem cp188000 : BB429.run 188000 (0,0)=some (109,733495) := by
  rw [show (188000:Nat)=187000+1000 by decide, BB429.run_add, cp187000]
  decide

private theorem cp189000 : BB429.run 189000 (0,0)=some (28669,680119) := by
  rw [show (189000:Nat)=188000+1000 by decide, BB429.run_add, cp188000]
  decide

private theorem cp190000 : BB429.run 190000 (0,0)=some (45,741118) := by
  rw [show (190000:Nat)=189000+1000 by decide, BB429.run_add, cp189000]
  decide

private theorem cp191000 : BB429.run 191000 (0,0)=some (12285,720382) := by
  rw [show (191000:Nat)=190000+1000 by decide, BB429.run_add, cp190000]
  decide

private theorem cp192000 : BB429.run 192000 (0,0)=some (109,748495) := by
  rw [show (192000:Nat)=191000+1000 by decide, BB429.run_add, cp191000]
  decide

private theorem cp193000 : BB429.run 193000 (0,0)=some (28669,695119) := by
  rw [show (193000:Nat)=192000+1000 by decide, BB429.run_add, cp192000]
  decide

private theorem cp194000 : BB429.run 194000 (0,0)=some (45,756118) := by
  rw [show (194000:Nat)=193000+1000 by decide, BB429.run_add, cp193000]
  decide

private theorem cp195000 : BB429.run 195000 (0,0)=some (12285,735382) := by
  rw [show (195000:Nat)=194000+1000 by decide, BB429.run_add, cp194000]
  decide

private theorem cp196000 : BB429.run 196000 (0,0)=some (109,763495) := by
  rw [show (196000:Nat)=195000+1000 by decide, BB429.run_add, cp195000]
  decide

private theorem cp197000 : BB429.run 197000 (0,0)=some (28669,710119) := by
  rw [show (197000:Nat)=196000+1000 by decide, BB429.run_add, cp196000]
  decide

private theorem cp198000 : BB429.run 198000 (0,0)=some (45,771118) := by
  rw [show (198000:Nat)=197000+1000 by decide, BB429.run_add, cp197000]
  decide

private theorem cp199000 : BB429.run 199000 (0,0)=some (12285,750382) := by
  rw [show (199000:Nat)=198000+1000 by decide, BB429.run_add, cp198000]
  decide

private theorem cp200000 : BB429.run 200000 (0,0)=some (109,778495) := by
  rw [show (200000:Nat)=199000+1000 by decide, BB429.run_add, cp199000]
  decide

private theorem cp201000 : BB429.run 201000 (0,0)=some (28669,725119) := by
  rw [show (201000:Nat)=200000+1000 by decide, BB429.run_add, cp200000]
  decide

private theorem cp202000 : BB429.run 202000 (0,0)=some (45,786118) := by
  rw [show (202000:Nat)=201000+1000 by decide, BB429.run_add, cp201000]
  decide

private theorem cp203000 : BB429.run 203000 (0,0)=some (1533,786729) := by
  rw [show (203000:Nat)=202000+1000 by decide, BB429.run_add, cp202000]
  decide

private theorem cp204000 : BB429.run 204000 (0,0)=some (9,793360) := by
  rw [show (204000:Nat)=203000+1000 by decide, BB429.run_add, cp203000]
  decide

private theorem cp205000 : BB429.run 205000 (0,0)=some (49149,698652) := by
  rw [show (205000:Nat)=204000+1000 by decide, BB429.run_add, cp204000]
  decide

private theorem cp206000 : BB429.run 206000 (0,0)=some (381,799771) := by
  rw [show (206000:Nat)=205000+1000 by decide, BB429.run_add, cp205000]
  decide

private theorem cp207000 : BB429.run 207000 (0,0)=some (0,804116) := by
  rw [show (207000:Nat)=206000+1000 by decide, BB429.run_add, cp206000]
  decide

private theorem cp208000 : BB429.run 208000 (0,0)=some (12285,783118) := by
  rw [show (208000:Nat)=207000+1000 by decide, BB429.run_add, cp207000]
  decide

private theorem cp209000 : BB429.run 209000 (0,0)=some (93,811085) := by
  rw [show (209000:Nat)=208000+1000 by decide, BB429.run_add, cp208000]
  decide

private theorem cp210000 : BB429.run 210000 (0,0)=some (393213,28417) := by
  rw [show (210000:Nat)=209000+1000 by decide, BB429.run_add, cp209000]
  decide

private theorem cp211000 : BB429.run 211000 (0,0)=some (3069,812288) := by
  rw [show (211000:Nat)=210000+1000 by decide, BB429.run_add, cp210000]
  decide

private theorem cp212000 : BB429.run 212000 (0,0)=some (21,821967) := by
  rw [show (212000:Nat)=211000+1000 by decide, BB429.run_add, cp211000]
  decide

private theorem cp213000 : BB429.run 213000 (0,0)=some (98301,628979) := by
  rw [show (213000:Nat)=212000+1000 by decide, BB429.run_add, cp212000]
  decide

private theorem cp214000 : BB429.run 214000 (0,0)=some (765,827634) := by
  rw [show (214000:Nat)=213000+1000 by decide, BB429.run_add, cp213000]
  decide

private theorem cp215000 : BB429.run 215000 (0,0)=some (3,832741) := by
  rw [show (215000:Nat)=214000+1000 by decide, BB429.run_add, cp214000]
  decide

private theorem cp216000 : BB429.run 216000 (0,0)=some (24573,787173) := by
  rw [show (216000:Nat)=215000+1000 by decide, BB429.run_add, cp215000]
  decide

private theorem cp217000 : BB429.run 217000 (0,0)=some (189,839524) := by
  rw [show (217000:Nat)=216000+1000 by decide, BB429.run_add, cp216000]
  decide

private theorem cp218000 : BB429.run 218000 (0,0)=some (364694,114090) := by
  rw [show (218000:Nat)=217000+1000 by decide, BB429.run_add, cp217000]
  decide

private theorem cp219000 : BB429.run 219000 (0,0)=some (6141,834775) := by
  rw [show (219000:Nat)=218000+1000 by decide, BB429.run_add, cp218000]
  decide

private theorem cp220000 : BB429.run 220000 (0,0)=some (45,850550) := by
  rw [show (220000:Nat)=219000+1000 by decide, BB429.run_add, cp219000]
  decide

private theorem cp221000 : BB429.run 221000 (0,0)=some (196605,461002) := by
  rw [show (221000:Nat)=220000+1000 by decide, BB429.run_add, cp220000]
  decide

private theorem cp222000 : BB429.run 222000 (0,0)=some (1533,854729) := by
  rw [show (222000:Nat)=221000+1000 by decide, BB429.run_add, cp221000]
  decide

private theorem cp223000 : BB429.run 223000 (0,0)=some (9,861360) := by
  rw [show (223000:Nat)=222000+1000 by decide, BB429.run_add, cp222000]
  decide

private theorem cp224000 : BB429.run 224000 (0,0)=some (49149,766652) := by
  rw [show (224000:Nat)=223000+1000 by decide, BB429.run_add, cp223000]
  decide

private theorem cp225000 : BB429.run 225000 (0,0)=some (381,867771) := by
  rw [show (225000:Nat)=224000+1000 by decide, BB429.run_add, cp224000]
  decide

private theorem cp226000 : BB429.run 226000 (0,0)=some (0,872116) := by
  rw [show (226000:Nat)=225000+1000 by decide, BB429.run_add, cp225000]
  decide

private theorem cp227000 : BB429.run 227000 (0,0)=some (12285,851118) := by
  rw [show (227000:Nat)=226000+1000 by decide, BB429.run_add, cp226000]
  decide

private theorem cp228000 : BB429.run 228000 (0,0)=some (93,879085) := by
  rw [show (228000:Nat)=227000+1000 by decide, BB429.run_add, cp227000]
  decide

private theorem cp229000 : BB429.run 229000 (0,0)=some (393213,96417) := by
  rw [show (229000:Nat)=228000+1000 by decide, BB429.run_add, cp228000]
  decide

private theorem cp230000 : BB429.run 230000 (0,0)=some (3069,880288) := by
  rw [show (230000:Nat)=229000+1000 by decide, BB429.run_add, cp229000]
  decide

private theorem cp231000 : BB429.run 231000 (0,0)=some (21,889967) := by
  rw [show (231000:Nat)=230000+1000 by decide, BB429.run_add, cp230000]
  decide

private theorem cp232000 : BB429.run 232000 (0,0)=some (98301,696979) := by
  rw [show (232000:Nat)=231000+1000 by decide, BB429.run_add, cp231000]
  decide

private theorem cp233000 : BB429.run 233000 (0,0)=some (765,895634) := by
  rw [show (233000:Nat)=232000+1000 by decide, BB429.run_add, cp232000]
  decide

private theorem cp234000 : BB429.run 234000 (0,0)=some (3,900741) := by
  rw [show (234000:Nat)=233000+1000 by decide, BB429.run_add, cp233000]
  decide

private theorem cp235000 : BB429.run 235000 (0,0)=some (24573,855173) := by
  rw [show (235000:Nat)=234000+1000 by decide, BB429.run_add, cp234000]
  decide

private theorem cp236000 : BB429.run 236000 (0,0)=some (189,907524) := by
  rw [show (236000:Nat)=235000+1000 by decide, BB429.run_add, cp235000]
  decide

private theorem cp237000 : BB429.run 237000 (0,0)=some (330694,250090) := by
  rw [show (237000:Nat)=236000+1000 by decide, BB429.run_add, cp236000]
  decide

private theorem cp238000 : BB429.run 238000 (0,0)=some (6141,902775) := by
  rw [show (238000:Nat)=237000+1000 by decide, BB429.run_add, cp237000]
  decide

private theorem cp239000 : BB429.run 239000 (0,0)=some (45,918550) := by
  rw [show (239000:Nat)=238000+1000 by decide, BB429.run_add, cp238000]
  decide

private theorem cp240000 : BB429.run 240000 (0,0)=some (196605,529002) := by
  rw [show (240000:Nat)=239000+1000 by decide, BB429.run_add, cp239000]
  decide

/-- No authentic blank-root terminal is the zero-quotient state. -/
private theorem seed_6141 : ¬Reach 6141 12281 := by
  rintro ⟨n,hn⟩
  exact no_terminal_below_rank 240000 n 6141 12281
    (196605,529002) cp240000 hn (by decide) (by decide)

/-- One symbolic inverse tree simultaneously excludes every positive quotient. -/
private theorem positive_6141 (q : Nat) :
    ¬Reach (262144*q+268285) (524288*q+536569) := by
  have hc : BB429Kernel16.cert 16
      ⟨262144,268285,524288,536569⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16
      ⟨262144,268285,524288,536569⟩ q hc

/-- Complete infinite affine family from true blank root. -/
theorem no_reach_6141 (q : Nat) :
    ¬Reach (262144*q+6141) (524288*q+12281) := by
  cases q with
  | zero => simpa using seed_6141
  | succ q =>
    have h1 : 262144*(q+1)+6141=262144*q+268285 := by omega
    have h2 : 524288*(q+1)+12281=524288*q+536569 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_6141 q)

/-- This residue is impossible at every genuine blank-root halting gateway. -/
theorem blank_halt_not_6141 (n a b : Nat)
    (hr : BB429.run n (0,0) = some (a,b))
    (hg : b+1=2*a) : a%262144≠6141 := by
  intro hm
  let q := a/262144
  have ha : a=262144*q+6141 := by dsimp [q]; omega
  have hb : b=524288*q+12281 := by omega
  exact (no_reach_6141 q) ⟨n, by simpa only [←ha,←hb] using hr⟩

/-- No authentic blank-root terminal is the zero-quotient state. -/
private theorem seed_19665 : ¬Reach 19665 39329 := by
  rintro ⟨n,hn⟩
  exact no_terminal_below_rank 240000 n 19665 39329
    (196605,529002) cp240000 hn (by decide) (by decide)

/-- One symbolic inverse tree simultaneously excludes every positive quotient. -/
private theorem positive_19665 (q : Nat) :
    ¬Reach (262144*q+281809) (524288*q+563617) := by
  have hc : BB429Kernel16.cert 16
      ⟨262144,281809,524288,563617⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16
      ⟨262144,281809,524288,563617⟩ q hc

/-- Complete infinite affine family from true blank root. -/
theorem no_reach_19665 (q : Nat) :
    ¬Reach (262144*q+19665) (524288*q+39329) := by
  cases q with
  | zero => simpa using seed_19665
  | succ q =>
    have h1 : 262144*(q+1)+19665=262144*q+281809 := by omega
    have h2 : 524288*(q+1)+39329=524288*q+563617 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_19665 q)

/-- This residue is impossible at every genuine blank-root halting gateway. -/
theorem blank_halt_not_19665 (n a b : Nat)
    (hr : BB429.run n (0,0) = some (a,b))
    (hg : b+1=2*a) : a%262144≠19665 := by
  intro hm
  let q := a/262144
  have ha : a=262144*q+19665 := by dsimp [q]; omega
  have hb : b=524288*q+39329 := by omega
  exact (no_reach_19665 q) ⟨n, by simpa only [←ha,←hb] using hr⟩

/-- No authentic blank-root terminal is the zero-quotient state. -/
private theorem seed_49149 : ¬Reach 49149 98297 := by
  rintro ⟨n,hn⟩
  exact no_terminal_below_rank 240000 n 49149 98297
    (196605,529002) cp240000 hn (by decide) (by decide)

/-- One symbolic inverse tree simultaneously excludes every positive quotient. -/
private theorem positive_49149 (q : Nat) :
    ¬Reach (262144*q+311293) (524288*q+622585) := by
  have hc : BB429Kernel16.cert 16
      ⟨262144,311293,524288,622585⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16
      ⟨262144,311293,524288,622585⟩ q hc

/-- Complete infinite affine family from true blank root. -/
theorem no_reach_49149 (q : Nat) :
    ¬Reach (262144*q+49149) (524288*q+98297) := by
  cases q with
  | zero => simpa using seed_49149
  | succ q =>
    have h1 : 262144*(q+1)+49149=262144*q+311293 := by omega
    have h2 : 524288*(q+1)+98297=524288*q+622585 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_49149 q)

/-- This residue is impossible at every genuine blank-root halting gateway. -/
theorem blank_halt_not_49149 (n a b : Nat)
    (hr : BB429.run n (0,0) = some (a,b))
    (hg : b+1=2*a) : a%262144≠49149 := by
  intro hm
  let q := a/262144
  have ha : a=262144*q+49149 := by dsimp [q]; omega
  have hb : b=524288*q+98297 := by omega
  exact (no_reach_49149 q) ⟨n, by simpa only [←ha,←hb] using hr⟩

/-- No authentic blank-root terminal is the zero-quotient state. -/
private theorem seed_65533 : ¬Reach 65533 131065 := by
  rintro ⟨n,hn⟩
  exact no_terminal_below_rank 240000 n 65533 131065
    (196605,529002) cp240000 hn (by decide) (by decide)

/-- One symbolic inverse tree simultaneously excludes every positive quotient. -/
private theorem positive_65533 (q : Nat) :
    ¬Reach (262144*q+327677) (524288*q+655353) := by
  have hc : BB429Kernel16.cert 16
      ⟨262144,327677,524288,655353⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16
      ⟨262144,327677,524288,655353⟩ q hc

/-- Complete infinite affine family from true blank root. -/
theorem no_reach_65533 (q : Nat) :
    ¬Reach (262144*q+65533) (524288*q+131065) := by
  cases q with
  | zero => simpa using seed_65533
  | succ q =>
    have h1 : 262144*(q+1)+65533=262144*q+327677 := by omega
    have h2 : 524288*(q+1)+131065=524288*q+655353 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_65533 q)

/-- This residue is impossible at every genuine blank-root halting gateway. -/
theorem blank_halt_not_65533 (n a b : Nat)
    (hr : BB429.run n (0,0) = some (a,b))
    (hg : b+1=2*a) : a%262144≠65533 := by
  intro hm
  let q := a/262144
  have ha : a=262144*q+65533 := by dsimp [q]; omega
  have hb : b=524288*q+131065 := by omega
  exact (no_reach_65533 q) ⟨n, by simpa only [←ha,←hb] using hr⟩

/-- No authentic blank-root terminal is the zero-quotient state. -/
private theorem seed_81917 : ¬Reach 81917 163833 := by
  rintro ⟨n,hn⟩
  exact no_terminal_below_rank 240000 n 81917 163833
    (196605,529002) cp240000 hn (by decide) (by decide)

/-- One symbolic inverse tree simultaneously excludes every positive quotient. -/
private theorem positive_81917 (q : Nat) :
    ¬Reach (262144*q+344061) (524288*q+688121) := by
  have hc : BB429Kernel16.cert 16
      ⟨262144,344061,524288,688121⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16
      ⟨262144,344061,524288,688121⟩ q hc

/-- Complete infinite affine family from true blank root. -/
theorem no_reach_81917 (q : Nat) :
    ¬Reach (262144*q+81917) (524288*q+163833) := by
  cases q with
  | zero => simpa using seed_81917
  | succ q =>
    have h1 : 262144*(q+1)+81917=262144*q+344061 := by omega
    have h2 : 524288*(q+1)+163833=524288*q+688121 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_81917 q)

/-- This residue is impossible at every genuine blank-root halting gateway. -/
theorem blank_halt_not_81917 (n a b : Nat)
    (hr : BB429.run n (0,0) = some (a,b))
    (hg : b+1=2*a) : a%262144≠81917 := by
  intro hm
  let q := a/262144
  have ha : a=262144*q+81917 := by dsimp [q]; omega
  have hb : b=524288*q+163833 := by omega
  exact (no_reach_81917 q) ⟨n, by simpa only [←ha,←hb] using hr⟩

/-- No authentic blank-root terminal is the zero-quotient state. -/
private theorem seed_98301 : ¬Reach 98301 196601 := by
  rintro ⟨n,hn⟩
  exact no_terminal_below_rank 240000 n 98301 196601
    (196605,529002) cp240000 hn (by decide) (by decide)

/-- One symbolic inverse tree simultaneously excludes every positive quotient. -/
private theorem positive_98301 (q : Nat) :
    ¬Reach (262144*q+360445) (524288*q+720889) := by
  have hc : BB429Kernel16.cert 16
      ⟨262144,360445,524288,720889⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16
      ⟨262144,360445,524288,720889⟩ q hc

/-- Complete infinite affine family from true blank root. -/
theorem no_reach_98301 (q : Nat) :
    ¬Reach (262144*q+98301) (524288*q+196601) := by
  cases q with
  | zero => simpa using seed_98301
  | succ q =>
    have h1 : 262144*(q+1)+98301=262144*q+360445 := by omega
    have h2 : 524288*(q+1)+196601=524288*q+720889 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_98301 q)

/-- This residue is impossible at every genuine blank-root halting gateway. -/
theorem blank_halt_not_98301 (n a b : Nat)
    (hr : BB429.run n (0,0) = some (a,b))
    (hg : b+1=2*a) : a%262144≠98301 := by
  intro hm
  let q := a/262144
  have ha : a=262144*q+98301 := by dsimp [q]; omega
  have hb : b=524288*q+196601 := by omega
  exact (no_reach_98301 q) ⟨n, by simpa only [←ha,←hb] using hr⟩

/-- No authentic blank-root terminal is the zero-quotient state. -/
private theorem seed_114685 : ¬Reach 114685 229369 := by
  rintro ⟨n,hn⟩
  exact no_terminal_below_rank 240000 n 114685 229369
    (196605,529002) cp240000 hn (by decide) (by decide)

/-- One symbolic inverse tree simultaneously excludes every positive quotient. -/
private theorem positive_114685 (q : Nat) :
    ¬Reach (262144*q+376829) (524288*q+753657) := by
  have hc : BB429Kernel16.cert 16
      ⟨262144,376829,524288,753657⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16
      ⟨262144,376829,524288,753657⟩ q hc

/-- Complete infinite affine family from true blank root. -/
theorem no_reach_114685 (q : Nat) :
    ¬Reach (262144*q+114685) (524288*q+229369) := by
  cases q with
  | zero => simpa using seed_114685
  | succ q =>
    have h1 : 262144*(q+1)+114685=262144*q+376829 := by omega
    have h2 : 524288*(q+1)+229369=524288*q+753657 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_114685 q)

/-- This residue is impossible at every genuine blank-root halting gateway. -/
theorem blank_halt_not_114685 (n a b : Nat)
    (hr : BB429.run n (0,0) = some (a,b))
    (hg : b+1=2*a) : a%262144≠114685 := by
  intro hm
  let q := a/262144
  have ha : a=262144*q+114685 := by dsimp [q]; omega
  have hb : b=524288*q+229369 := by omega
  exact (no_reach_114685 q) ⟨n, by simpa only [←ha,←hb] using hr⟩

/-- No authentic blank-root terminal is the zero-quotient state. -/
private theorem seed_163837 : ¬Reach 163837 327673 := by
  rintro ⟨n,hn⟩
  exact no_terminal_below_rank 240000 n 163837 327673
    (196605,529002) cp240000 hn (by decide) (by decide)

/-- One symbolic inverse tree simultaneously excludes every positive quotient. -/
private theorem positive_163837 (q : Nat) :
    ¬Reach (262144*q+425981) (524288*q+851961) := by
  have hc : BB429Kernel16.cert 16
      ⟨262144,425981,524288,851961⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16
      ⟨262144,425981,524288,851961⟩ q hc

/-- Complete infinite affine family from true blank root. -/
theorem no_reach_163837 (q : Nat) :
    ¬Reach (262144*q+163837) (524288*q+327673) := by
  cases q with
  | zero => simpa using seed_163837
  | succ q =>
    have h1 : 262144*(q+1)+163837=262144*q+425981 := by omega
    have h2 : 524288*(q+1)+327673=524288*q+851961 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_163837 q)

/-- This residue is impossible at every genuine blank-root halting gateway. -/
theorem blank_halt_not_163837 (n a b : Nat)
    (hr : BB429.run n (0,0) = some (a,b))
    (hg : b+1=2*a) : a%262144≠163837 := by
  intro hm
  let q := a/262144
  have ha : a=262144*q+163837 := by dsimp [q]; omega
  have hb : b=524288*q+327673 := by omega
  exact (no_reach_163837 q) ⟨n, by simpa only [←ha,←hb] using hr⟩

/-- No authentic blank-root terminal is the zero-quotient state. -/
private theorem seed_229373 : ¬Reach 229373 458745 := by
  rintro ⟨n,hn⟩
  exact no_terminal_below_rank 240000 n 229373 458745
    (196605,529002) cp240000 hn (by decide) (by decide)

/-- One symbolic inverse tree simultaneously excludes every positive quotient. -/
private theorem positive_229373 (q : Nat) :
    ¬Reach (262144*q+491517) (524288*q+983033) := by
  have hc : BB429Kernel16.cert 16
      ⟨262144,491517,524288,983033⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16
      ⟨262144,491517,524288,983033⟩ q hc

/-- Complete infinite affine family from true blank root. -/
theorem no_reach_229373 (q : Nat) :
    ¬Reach (262144*q+229373) (524288*q+458745) := by
  cases q with
  | zero => simpa using seed_229373
  | succ q =>
    have h1 : 262144*(q+1)+229373=262144*q+491517 := by omega
    have h2 : 524288*(q+1)+458745=524288*q+983033 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_229373 q)

/-- This residue is impossible at every genuine blank-root halting gateway. -/
theorem blank_halt_not_229373 (n a b : Nat)
    (hr : BB429.run n (0,0) = some (a,b))
    (hg : b+1=2*a) : a%262144≠229373 := by
  intro hm
  let q := a/262144
  have ha : a=262144*q+229373 := by dsimp [q]; omega
  have hb : b=524288*q+458745 := by omega
  exact (no_reach_229373 q) ⟨n, by simpa only [←ha,←hb] using hr⟩

#print axioms no_terminal_below_rank
#print axioms no_reach_229373
#print axioms blank_halt_not_229373
end BB429MoreShifted
