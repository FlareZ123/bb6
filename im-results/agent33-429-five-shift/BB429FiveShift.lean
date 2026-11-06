import BB429InverseKernel16
import Lean.Elab.Tactic.Omega

namespace BB429FiveShift
open BB429NewResidue
set_option maxRecDepth 32768
set_option maxHeartbeats 30000000

/-- Rank-straddle argument from Agent 1, applied to new source-root targets. -/
private theorem straddle
    (k : Nat) (prev after target : BB429.State)
    (hprev : BB429.run k (0,0)=some prev)
    (hafter : BB429.run (k+1) (0,0)=some after)
    (hlo : BB429.rank prev ≤ BB429.rank target)
    (hhi : BB429.rank target < BB429.rank after)
    (hne : prev ≠ target) :
    ∀ n, BB429.run n (0,0) ≠ some target := by
  intro n hrun
  by_cases hn : n < k
  · have heq : k=n+(k-n) := by omega
    rw [heq, BB429.run_add, hrun] at hprev
    simp only [Option.bind_some] at hprev
    have hm := (BB429.run_rank_bounds target prev (k-n) hprev).1
    omega
  · by_cases heq : n=k
    · subst n
      have hsame : target=prev := Option.some.inj (hrun.symm.trans hprev)
      exact hne hsame.symm
    · have hlate : k+1≤n := by omega
      have hsum : n=(k+1)+(n-(k+1)) := by omega
      rw [hsum, BB429.run_add, hafter] at hrun
      simp only [Option.bind_some] at hrun
      have hm := (BB429.run_rank_bounds after target (n-(k+1)) hrun).1
      omega

/-- Exact kernel-checked checkpoint segments of the authentic source accelerator. -/
private theorem cp0 : BB429.run 0 (0,0)=some (0,0) := by decide

private theorem cp200 : BB429.run 200 (0,0)=some (109,767) := by
  rw [show (200:Nat)=0+200 by decide, BB429.run_add, cp0]
  decide

private theorem cp400 : BB429.run 400 (0,0)=some (45,1894) := by
  rw [show (400:Nat)=200+200 by decide, BB429.run_add, cp200]
  decide

private theorem cp600 : BB429.run 600 (0,0)=some (109,2671) := by
  rw [show (600:Nat)=400+200 by decide, BB429.run_add, cp400]
  decide

private theorem cp800 : BB429.run 800 (0,0)=some (1222,1258) := by
  rw [show (800:Nat)=600+200 by decide, BB429.run_add, cp600]
  decide

private theorem cp1000 : BB429.run 1000 (0,0)=some (53,4556) := by
  rw [show (1000:Nat)=800+200 by decide, BB429.run_add, cp800]
  decide

private theorem cp1200 : BB429.run 1200 (0,0)=some (93,5481) := by
  rw [show (1200:Nat)=1000+200 by decide, BB429.run_add, cp1000]
  decide

private theorem cp1400 : BB429.run 1400 (0,0)=some (0,6464) := by
  rw [show (1400:Nat)=1200+200 by decide, BB429.run_add, cp1200]
  decide

private theorem cp1600 : BB429.run 1600 (0,0)=some (9,7172) := by
  rw [show (1600:Nat)=1400+200 by decide, BB429.run_add, cp1400]
  decide

private theorem cp1800 : BB429.run 1800 (0,0)=some (45,7826) := by
  rw [show (1800:Nat)=1600+200 by decide, BB429.run_add, cp1600]
  decide

private theorem cp2000 : BB429.run 2000 (0,0)=some (189,8264) := by
  rw [show (2000:Nat)=1800+200 by decide, BB429.run_add, cp1800]
  decide

private theorem cp2200 : BB429.run 2200 (0,0)=some (765,7838) := by
  rw [show (2200:Nat)=2000+200 by decide, BB429.run_add, cp2000]
  decide

private theorem cp2400 : BB429.run 2400 (0,0)=some (3069,3956) := by
  rw [show (2400:Nat)=2200+200 by decide, BB429.run_add, cp2200]
  decide

private theorem cp2600 : BB429.run 2600 (0,0)=some (3,10821) := by
  rw [show (2600:Nat)=2400+200 by decide, BB429.run_add, cp2400]
  decide

private theorem cp2800 : BB429.run 2800 (0,0)=some (21,11511) := by
  rw [show (2800:Nat)=2600+200 by decide, BB429.run_add, cp2600]
  decide

private theorem cp3000 : BB429.run 3000 (0,0)=some (93,12093) := by
  rw [show (3000:Nat)=2800+200 by decide, BB429.run_add, cp2800]
  decide

private theorem cp3200 : BB429.run 3200 (0,0)=some (109,13043) := by
  rw [show (3200:Nat)=3000+200 by decide, BB429.run_add, cp3000]
  decide

private theorem cp3400 : BB429.run 3400 (0,0)=some (445,13345) := by
  rw [show (3400:Nat)=3200+200 by decide, BB429.run_add, cp3200]
  decide

private theorem cp3600 : BB429.run 3600 (0,0)=some (765,13602) := by
  rw [show (3600:Nat)=3400+200 by decide, BB429.run_add, cp3400]
  decide

private theorem cp3800 : BB429.run 3800 (0,0)=some (109,15827) := by
  rw [show (3800:Nat)=3600+200 by decide, BB429.run_add, cp3600]
  decide

private theorem cp4000 : BB429.run 4000 (0,0)=some (0,16916) := by
  rw [show (4000:Nat)=3800+200 by decide, BB429.run_add, cp3800]
  decide

private theorem cp4200 : BB429.run 4200 (0,0)=some (93,17577) := by
  rw [show (4200:Nat)=4000+200 by decide, BB429.run_add, cp4000]
  decide

private theorem cp4400 : BB429.run 4400 (0,0)=some (6141,6387) := by
  rw [show (4400:Nat)=4200+200 by decide, BB429.run_add, cp4200]
  decide

private theorem cp4600 : BB429.run 4600 (0,0)=some (109,19439) := by
  rw [show (4600:Nat)=4400+200 by decide, BB429.run_add, cp4400]
  decide

private theorem cp4800 : BB429.run 4800 (0,0)=some (3581,13530) := by
  rw [show (4800:Nat)=4600+200 by decide, BB429.run_add, cp4600]
  decide

private theorem cp5000 : BB429.run 5000 (0,0)=some (45,21462) := by
  rw [show (5000:Nat)=4800+200 by decide, BB429.run_add, cp4800]
  decide

private theorem cp5200 : BB429.run 5200 (0,0)=some (10517,1402) := by
  rw [show (5200:Nat)=5000+200 by decide, BB429.run_add, cp5000]
  decide

private theorem cp5400 : BB429.run 5400 (0,0)=some (53,23292) := by
  rw [show (5400:Nat)=5200+200 by decide, BB429.run_add, cp5200]
  decide

private theorem cp5600 : BB429.run 5600 (0,0)=some (1789,20735) := by
  rw [show (5600:Nat)=5400+200 by decide, BB429.run_add, cp5400]
  decide

private theorem cp5800 : BB429.run 5800 (0,0)=some (6905,11422) := by
  rw [show (5800:Nat)=5600+200 by decide, BB429.run_add, cp5600]
  decide

private theorem cp6000 : BB429.run 6000 (0,0)=some (1789,22515) := by
  rw [show (6000:Nat)=5800+200 by decide, BB429.run_add, cp5800]
  decide

private theorem cp6200 : BB429.run 6200 (0,0)=some (5229,16524) := by
  rw [show (6200:Nat)=6000+200 by decide, BB429.run_add, cp6000]
  decide

private theorem cp6400 : BB429.run 6400 (0,0)=some (25,27753) := by
  rw [show (6400:Nat)=6200+200 by decide, BB429.run_add, cp6200]
  decide

private theorem cp6600 : BB429.run 6600 (0,0)=some (765,27122) := by
  rw [show (6600:Nat)=6400+200 by decide, BB429.run_add, cp6400]
  decide

private theorem cp6800 : BB429.run 6800 (0,0)=some (109,29243) := by
  rw [show (6800:Nat)=6600+200 by decide, BB429.run_add, cp6600]
  decide

private theorem cp7000 : BB429.run 7000 (0,0)=some (0,30260) := by
  rw [show (7000:Nat)=6800+200 by decide, BB429.run_add, cp6800]
  decide

private theorem cp7200 : BB429.run 7200 (0,0)=some (765,29522) := by
  rw [show (7200:Nat)=7000+200 by decide, BB429.run_add, cp7000]
  decide

private theorem cp7400 : BB429.run 7400 (0,0)=some (109,31643) := by
  rw [show (7400:Nat)=7200+200 by decide, BB429.run_add, cp7200]
  decide

private theorem cp7600 : BB429.run 7600 (0,0)=some (0,32660) := by
  rw [show (7600:Nat)=7400+200 by decide, BB429.run_add, cp7400]
  decide

private theorem cp7800 : BB429.run 7800 (0,0)=some (765,31922) := by
  rw [show (7800:Nat)=7600+200 by decide, BB429.run_add, cp7600]
  decide

private theorem cp8000 : BB429.run 8000 (0,0)=some (109,34043) := by
  rw [show (8000:Nat)=7800+200 by decide, BB429.run_add, cp7800]
  decide

private theorem cp8200 : BB429.run 8200 (0,0)=some (0,35060) := by
  rw [show (8200:Nat)=8000+200 by decide, BB429.run_add, cp8000]
  decide

private theorem cp8400 : BB429.run 8400 (0,0)=some (765,34322) := by
  rw [show (8400:Nat)=8200+200 by decide, BB429.run_add, cp8200]
  decide

private theorem cp8600 : BB429.run 8600 (0,0)=some (109,36443) := by
  rw [show (8600:Nat)=8400+200 by decide, BB429.run_add, cp8400]
  decide

private theorem cp8800 : BB429.run 8800 (0,0)=some (0,37460) := by
  rw [show (8800:Nat)=8600+200 by decide, BB429.run_add, cp8600]
  decide

private theorem cp9000 : BB429.run 9000 (0,0)=some (765,36722) := by
  rw [show (9000:Nat)=8800+200 by decide, BB429.run_add, cp8800]
  decide

private theorem cp9200 : BB429.run 9200 (0,0)=some (109,38843) := by
  rw [show (9200:Nat)=9000+200 by decide, BB429.run_add, cp9000]
  decide

private theorem cp9400 : BB429.run 9400 (0,0)=some (0,39860) := by
  rw [show (9400:Nat)=9200+200 by decide, BB429.run_add, cp9200]
  decide

private theorem cp9600 : BB429.run 9600 (0,0)=some (765,39122) := by
  rw [show (9600:Nat)=9400+200 by decide, BB429.run_add, cp9400]
  decide

private theorem cp9800 : BB429.run 9800 (0,0)=some (109,41243) := by
  rw [show (9800:Nat)=9600+200 by decide, BB429.run_add, cp9600]
  decide

private theorem cp10000 : BB429.run 10000 (0,0)=some (0,42260) := by
  rw [show (10000:Nat)=9800+200 by decide, BB429.run_add, cp9800]
  decide

private theorem cp10200 : BB429.run 10200 (0,0)=some (765,41522) := by
  rw [show (10200:Nat)=10000+200 by decide, BB429.run_add, cp10000]
  decide

private theorem cp10400 : BB429.run 10400 (0,0)=some (109,43643) := by
  rw [show (10400:Nat)=10200+200 by decide, BB429.run_add, cp10200]
  decide

private theorem cp10600 : BB429.run 10600 (0,0)=some (0,44660) := by
  rw [show (10600:Nat)=10400+200 by decide, BB429.run_add, cp10400]
  decide

private theorem cp10800 : BB429.run 10800 (0,0)=some (765,43922) := by
  rw [show (10800:Nat)=10600+200 by decide, BB429.run_add, cp10600]
  decide

private theorem cp11000 : BB429.run 11000 (0,0)=some (109,46043) := by
  rw [show (11000:Nat)=10800+200 by decide, BB429.run_add, cp10800]
  decide

private theorem cp11200 : BB429.run 11200 (0,0)=some (0,47060) := by
  rw [show (11200:Nat)=11000+200 by decide, BB429.run_add, cp11000]
  decide

private theorem cp11400 : BB429.run 11400 (0,0)=some (765,46322) := by
  rw [show (11400:Nat)=11200+200 by decide, BB429.run_add, cp11200]
  decide

private theorem cp11600 : BB429.run 11600 (0,0)=some (109,48443) := by
  rw [show (11600:Nat)=11400+200 by decide, BB429.run_add, cp11400]
  decide

private theorem cp11800 : BB429.run 11800 (0,0)=some (12285,24862) := by
  rw [show (11800:Nat)=11600+200 by decide, BB429.run_add, cp11600]
  decide

private theorem cp12000 : BB429.run 12000 (0,0)=some (9,50168) := by
  rw [show (12000:Nat)=11800+200 by decide, BB429.run_add, cp11800]
  decide

private theorem cp12200 : BB429.run 12200 (0,0)=some (381,50167) := by
  rw [show (12200:Nat)=12000+200 by decide, BB429.run_add, cp12000]
  decide

private theorem cp12400 : BB429.run 12400 (0,0)=some (12285,27102) := by
  rw [show (12400:Nat)=12200+200 by decide, BB429.run_add, cp12200]
  decide

private theorem cp12600 : BB429.run 12600 (0,0)=some (9,52408) := by
  rw [show (12600:Nat)=12400+200 by decide, BB429.run_add, cp12400]
  decide

private theorem cp12800 : BB429.run 12800 (0,0)=some (381,52407) := by
  rw [show (12800:Nat)=12600+200 by decide, BB429.run_add, cp12600]
  decide

private theorem cp13000 : BB429.run 13000 (0,0)=some (12285,29342) := by
  rw [show (13000:Nat)=12800+200 by decide, BB429.run_add, cp12800]
  decide

private theorem cp13200 : BB429.run 13200 (0,0)=some (9,54648) := by
  rw [show (13200:Nat)=13000+200 by decide, BB429.run_add, cp13000]
  decide

private theorem cp13400 : BB429.run 13400 (0,0)=some (381,54647) := by
  rw [show (13400:Nat)=13200+200 by decide, BB429.run_add, cp13200]
  decide

private theorem cp13600 : BB429.run 13600 (0,0)=some (12285,31582) := by
  rw [show (13600:Nat)=13400+200 by decide, BB429.run_add, cp13400]
  decide

private theorem cp13800 : BB429.run 13800 (0,0)=some (9,56888) := by
  rw [show (13800:Nat)=13600+200 by decide, BB429.run_add, cp13600]
  decide

private theorem cp14000 : BB429.run 14000 (0,0)=some (381,56887) := by
  rw [show (14000:Nat)=13800+200 by decide, BB429.run_add, cp13800]
  decide

private theorem cp14200 : BB429.run 14200 (0,0)=some (12285,33822) := by
  rw [show (14200:Nat)=14000+200 by decide, BB429.run_add, cp14000]
  decide

private theorem cp14400 : BB429.run 14400 (0,0)=some (9,59128) := by
  rw [show (14400:Nat)=14200+200 by decide, BB429.run_add, cp14200]
  decide

private theorem cp14600 : BB429.run 14600 (0,0)=some (381,59127) := by
  rw [show (14600:Nat)=14400+200 by decide, BB429.run_add, cp14400]
  decide

private theorem cp14800 : BB429.run 14800 (0,0)=some (12285,36062) := by
  rw [show (14800:Nat)=14600+200 by decide, BB429.run_add, cp14600]
  decide

private theorem cp15000 : BB429.run 15000 (0,0)=some (9,61368) := by
  rw [show (15000:Nat)=14800+200 by decide, BB429.run_add, cp14800]
  decide

private theorem cp15200 : BB429.run 15200 (0,0)=some (381,61367) := by
  rw [show (15200:Nat)=15000+200 by decide, BB429.run_add, cp15000]
  decide

private theorem cp15400 : BB429.run 15400 (0,0)=some (12285,38302) := by
  rw [show (15400:Nat)=15200+200 by decide, BB429.run_add, cp15200]
  decide

private theorem cp15600 : BB429.run 15600 (0,0)=some (9,63608) := by
  rw [show (15600:Nat)=15400+200 by decide, BB429.run_add, cp15400]
  decide

private theorem cp15800 : BB429.run 15800 (0,0)=some (381,63607) := by
  rw [show (15800:Nat)=15600+200 by decide, BB429.run_add, cp15600]
  decide

private theorem cp16000 : BB429.run 16000 (0,0)=some (12285,40542) := by
  rw [show (16000:Nat)=15800+200 by decide, BB429.run_add, cp15800]
  decide

private theorem cp16200 : BB429.run 16200 (0,0)=some (14333,37288) := by
  rw [show (16200:Nat)=16000+200 by decide, BB429.run_add, cp16000]
  decide

private theorem cp16400 : BB429.run 16400 (0,0)=some (53,66848) := by
  rw [show (16400:Nat)=16200+200 by decide, BB429.run_add, cp16200]
  decide

private theorem cp16600 : BB429.run 16600 (0,0)=some (1789,64351) := by
  rw [show (16600:Nat)=16400+200 by decide, BB429.run_add, cp16400]
  decide

private theorem cp16800 : BB429.run 16800 (0,0)=some (22895,23122) := by
  rw [show (16800:Nat)=16600+200 by decide, BB429.run_add, cp16600]
  decide

private theorem cp17000 : BB429.run 17000 (0,0)=some (221,69462) := by
  rw [show (17000:Nat)=16800+200 by decide, BB429.run_add, cp16800]
  decide

private theorem cp17200 : BB429.run 17200 (0,0)=some (7165,56549) := by
  rw [show (17200:Nat)=17000+200 by decide, BB429.run_add, cp17000]
  decide

private theorem cp17400 : BB429.run 17400 (0,0)=some (25,71829) := by
  rw [show (17400:Nat)=17200+200 by decide, BB429.run_add, cp17200]
  decide

private theorem cp17600 : BB429.run 17600 (0,0)=some (893,71068) := by
  rw [show (17600:Nat)=17400+200 by decide, BB429.run_add, cp17400]
  decide

private theorem cp17800 : BB429.run 17800 (0,0)=some (28669,16491) := by
  rw [show (17800:Nat)=17600+200 by decide, BB429.run_add, cp17600]
  decide

private theorem cp18000 : BB429.run 18000 (0,0)=some (109,74611) := by
  rw [show (18000:Nat)=17800+200 by decide, BB429.run_add, cp17800]
  decide

private theorem cp18200 : BB429.run 18200 (0,0)=some (3581,68642) := by
  rw [show (18200:Nat)=18000+200 by decide, BB429.run_add, cp18000]
  decide

private theorem cp18400 : BB429.run 18400 (0,0)=some (12285,52166) := by
  rw [show (18400:Nat)=18200+200 by decide, BB429.run_add, cp18200]
  decide

private theorem cp18600 : BB429.run 18600 (0,0)=some (10285,57072) := by
  rw [show (18600:Nat)=18400+200 by decide, BB429.run_add, cp18400]
  decide

private theorem cp18800 : BB429.run 18800 (0,0)=some (381,77743) := by
  rw [show (18800:Nat)=18600+200 by decide, BB429.run_add, cp18600]
  decide

private theorem cp19000 : BB429.run 19000 (0,0)=some (381,78599) := by
  rw [show (19000:Nat)=18800+200 by decide, BB429.run_add, cp18800]
  decide

private theorem cp19200 : BB429.run 19200 (0,0)=some (18107,43991) := by
  rw [show (19200:Nat)=19000+200 by decide, BB429.run_add, cp19000]
  decide

private theorem cp19400 : BB429.run 19400 (0,0)=some (893,79276) := by
  rw [show (19400:Nat)=19200+200 by decide, BB429.run_add, cp19200]
  decide

private theorem cp19600 : BB429.run 19600 (0,0)=some (24652,32610) := by
  rw [show (19600:Nat)=19400+200 by decide, BB429.run_add, cp19400]
  decide

private theorem cp19800 : BB429.run 19800 (0,0)=some (381,81999) := by
  rw [show (19800:Nat)=19600+200 by decide, BB429.run_add, cp19600]
  decide

private theorem cp20000 : BB429.run 20000 (0,0)=some (31081,21465) := by
  rw [show (20000:Nat)=19800+200 by decide, BB429.run_add, cp19800]
  decide

private theorem cp20200 : BB429.run 20200 (0,0)=some (7165,70333) := by
  rw [show (20200:Nat)=20000+200 by decide, BB429.run_add, cp20000]
  decide

private theorem cp20400 : BB429.run 20400 (0,0)=some (25,85613) := by
  rw [show (20400:Nat)=20200+200 by decide, BB429.run_add, cp20200]
  decide

private theorem cp20600 : BB429.run 20600 (0,0)=some (25,86561) := by
  rw [show (20600:Nat)=20400+200 by decide, BB429.run_add, cp20400]
  decide

private theorem cp20800 : BB429.run 20800 (0,0)=some (93,87301) := by
  rw [show (20800:Nat)=20600+200 by decide, BB429.run_add, cp20600]
  decide

private theorem cp21000 : BB429.run 21000 (0,0)=some (10071,68099) := by
  rw [show (21000:Nat)=20800+200 by decide, BB429.run_add, cp20800]
  decide

private theorem cp21200 : BB429.run 21200 (0,0)=some (189,88624) := by
  rw [show (21200:Nat)=21000+200 by decide, BB429.run_add, cp21000]
  decide

private theorem cp21400 : BB429.run 21400 (0,0)=some (17121,55514) := by
  rw [show (21400:Nat)=21200+200 by decide, BB429.run_add, cp21200]
  decide

private theorem cp21600 : BB429.run 21600 (0,0)=some (189,90268) := by
  rw [show (21600:Nat)=21400+200 by decide, BB429.run_add, cp21400]
  decide

private theorem cp21800 : BB429.run 21800 (0,0)=some (3069,85356) := by
  rw [show (21800:Nat)=21600+200 by decide, BB429.run_add, cp21600]
  decide

private theorem cp22000 : BB429.run 22000 (0,0)=some (5995,80327) := by
  rw [show (22000:Nat)=21800+200 by decide, BB429.run_add, cp21800]
  decide

private theorem cp22200 : BB429.run 22200 (0,0)=some (0,93064) := by
  rw [show (22200:Nat)=22000+200 by decide, BB429.run_add, cp22000]
  decide

private theorem cp22400 : BB429.run 22400 (0,0)=some (3069,87636) := by
  rw [show (22400:Nat)=22200+200 by decide, BB429.run_add, cp22200]
  decide

private theorem cp22600 : BB429.run 22600 (0,0)=some (3,94489) := by
  rw [show (22600:Nat)=22400+200 by decide, BB429.run_add, cp22400]
  decide

private theorem cp22800 : BB429.run 22800 (0,0)=some (6141,82923) := by
  rw [show (22800:Nat)=22600+200 by decide, BB429.run_add, cp22600]
  decide

private theorem cp23000 : BB429.run 23000 (0,0)=some (3581,88870) := by
  rw [show (23000:Nat)=22800+200 by decide, BB429.run_add, cp22800]
  decide

private theorem cp23200 : BB429.run 23200 (0,0)=some (48317,186) := by
  rw [show (23200:Nat)=23000+200 by decide, BB429.run_add, cp23000]
  decide

private theorem cp23400 : BB429.run 23400 (0,0)=some (45,97542) := by
  rw [show (23400:Nat)=23200+200 by decide, BB429.run_add, cp23200]
  decide

private theorem cp1056x : BB429.run 1056 (0,0)=some (189,4552) := by
  rw [show (1056:Nat)=1000+56 by decide, BB429.run_add, cp1000]
  decide
private theorem cp1056y : BB429.run (1056+1) (0,0)=some (381,4171) := by
  change (BB429.run 1056 (0,0)).bind BB429.next = some (381,4171)
  rw [cp1056x]
  decide

private theorem cp4754x : BB429.run 4754 (0,0)=some (25,20417) := by
  rw [show (4754:Nat)=4600+154 by decide, BB429.run_add, cp4600]
  decide
private theorem cp4754y : BB429.run (4754+1) (0,0)=some (53,20364) := by
  change (BB429.run 4754 (0,0)).bind BB429.next = some (53,20364)
  rw [cp4754x]
  decide

private theorem cp6602x : BB429.run 6602 (0,0)=some (3069,22520) := by
  rw [show (6602:Nat)=6600+2 by decide, BB429.run_add, cp6600]
  decide
private theorem cp6602y : BB429.run (6602+1) (0,0)=some (6141,16379) := by
  change (BB429.run 6602 (0,0)).bind BB429.next = some (6141,16379)
  rw [cp6602x]
  decide

private theorem cp7623x : BB429.run 7623 (0,0)=some (14333,4080) := by
  rw [show (7623:Nat)=7600+23 by decide, BB429.run_add, cp7600]
  decide
private theorem cp7623y : BB429.run (7623+1) (0,0)=some (0,32756) := by
  change (BB429.run 7623 (0,0)).bind BB429.next = some (0,32756)
  rw [cp7623x]
  decide

private theorem cp13916x : BB429.run 13916 (0,0)=some (24573,8185) := by
  rw [show (13916:Nat)=13800+116 by decide, BB429.run_add, cp13800]
  decide
private theorem cp13916y : BB429.run (13916+1) (0,0)=some (20484,16370) := by
  change (BB429.run 13916 (0,0)).bind BB429.next = some (20484,16370)
  rw [cp13916x]
  decide

private theorem cp23570x : BB429.run 23570 (0,0)=some (117,98057) := by
  rw [show (23570:Nat)=23400+170 by decide, BB429.run_add, cp23400]
  decide
private theorem cp23570y : BB429.run (23570+1) (0,0)=some (237,97820) := by
  change (BB429.run 23570 (0,0)).bind BB429.next = some (237,97820)
  rw [cp23570x]
  decide

private theorem seed_1233_0 : ¬ Reach 1233 2465 := by
  rintro ⟨n,hr⟩
  exact straddle 1056 (189,4552) (381,4171) (1233,2465)
    cp1056x cp1056y (by decide) (by decide) (by decide) n hr

private theorem seed_5117_0 : ¬ Reach 5117 10233 := by
  rintro ⟨n,hr⟩
  exact straddle 4754 (25,20417) (53,20364) (5117,10233)
    cp4754x cp4754y (by decide) (by decide) (by decide) n hr

private theorem seed_7165_0 : ¬ Reach 7165 14329 := by
  rintro ⟨n,hr⟩
  exact straddle 6602 (3069,22520) (6141,16379) (7165,14329)
    cp6602x cp6602y (by decide) (by decide) (by decide) n hr

private theorem seed_8189_0 : ¬ Reach 8189 16377 := by
  rintro ⟨n,hr⟩
  exact straddle 7623 (14333,4080) (0,32756) (8189,16377)
    cp7623x cp7623y (by decide) (by decide) (by decide) n hr

private theorem seed_14333_0 : ¬ Reach 14333 28665 := by
  rintro ⟨n,hr⟩
  exact straddle 13916 (24573,8185) (20484,16370) (14333,28665)
    cp13916x cp13916y (by decide) (by decide) (by decide) n hr

private theorem seed_8189_1 : ¬ Reach 24573 49145 := by
  rintro ⟨n,hr⟩
  exact straddle 23570 (117,98057) (237,97820) (24573,49145)
    cp23570x cp23570y (by decide) (by decide) (by decide) n hr

private theorem tail_1233 (q : Nat) :
    ¬ Reach (16384*q+17617) (32768*q+35233) := by
  have hc : BB429Kernel16.cert 12 ⟨16384,17617,32768,35233⟩ = true := by decide
  exact BB429Kernel16.cert_sound 12 ⟨16384,17617,32768,35233⟩ q hc

theorem no_reach_1233 (q : Nat) :
    ¬ Reach (16384*q+1233) (32768*q+2465) := by
  cases q with
  | zero => simpa using seed_1233_0
  | succ q =>
      have h1 : 16384*(q+1)+1233 = 16384*q+17617 := by omega
      have h2 : 32768*(q+1)+2465 = 32768*q+35233 := by omega
      rw [Nat.succ_eq_add_one, h1, h2]
      exact tail_1233 q

private theorem tail_5117 (q : Nat) :
    ¬ Reach (16384*q+21501) (32768*q+43001) := by
  have hc : BB429Kernel16.cert 12 ⟨16384,21501,32768,43001⟩ = true := by decide
  exact BB429Kernel16.cert_sound 12 ⟨16384,21501,32768,43001⟩ q hc

theorem no_reach_5117 (q : Nat) :
    ¬ Reach (16384*q+5117) (32768*q+10233) := by
  cases q with
  | zero => simpa using seed_5117_0
  | succ q =>
      have h1 : 16384*(q+1)+5117 = 16384*q+21501 := by omega
      have h2 : 32768*(q+1)+10233 = 32768*q+43001 := by omega
      rw [Nat.succ_eq_add_one, h1, h2]
      exact tail_5117 q

private theorem tail_7165 (q : Nat) :
    ¬ Reach (16384*q+23549) (32768*q+47097) := by
  have hc : BB429Kernel16.cert 12 ⟨16384,23549,32768,47097⟩ = true := by decide
  exact BB429Kernel16.cert_sound 12 ⟨16384,23549,32768,47097⟩ q hc

theorem no_reach_7165 (q : Nat) :
    ¬ Reach (16384*q+7165) (32768*q+14329) := by
  cases q with
  | zero => simpa using seed_7165_0
  | succ q =>
      have h1 : 16384*(q+1)+7165 = 16384*q+23549 := by omega
      have h2 : 32768*(q+1)+14329 = 32768*q+47097 := by omega
      rw [Nat.succ_eq_add_one, h1, h2]
      exact tail_7165 q

private theorem tail_8189 (q : Nat) :
    ¬ Reach (16384*q+40957) (32768*q+81913) := by
  have hc : BB429Kernel16.cert 12 ⟨16384,40957,32768,81913⟩ = true := by decide
  exact BB429Kernel16.cert_sound 12 ⟨16384,40957,32768,81913⟩ q hc

theorem no_reach_8189 (q : Nat) :
    ¬ Reach (16384*q+8189) (32768*q+16377) := by
  cases q with
  | zero => simpa using seed_8189_0
  | succ t =>
      cases t with
      | zero => simpa using seed_8189_1
      | succ q =>
          have h1 : 16384*((q+1)+1)+8189 = 16384*q+40957 := by omega
          have h2 : 32768*((q+1)+1)+16377 = 32768*q+81913 := by omega
          rw [Nat.succ_eq_add_one, Nat.succ_eq_add_one, h1, h2]
          exact tail_8189 q

private theorem tail_14333 (q : Nat) :
    ¬ Reach (16384*q+30717) (32768*q+61433) := by
  have hc : BB429Kernel16.cert 12 ⟨16384,30717,32768,61433⟩ = true := by decide
  exact BB429Kernel16.cert_sound 12 ⟨16384,30717,32768,61433⟩ q hc

theorem no_reach_14333 (q : Nat) :
    ¬ Reach (16384*q+14333) (32768*q+28665) := by
  cases q with
  | zero => simpa using seed_14333_0
  | succ q =>
      have h1 : 16384*(q+1)+14333 = 16384*q+30717 := by omega
      have h2 : 32768*(q+1)+28665 = 32768*q+61433 := by omega
      rw [Nat.succ_eq_add_one, h1, h2]
      exact tail_14333 q

/-- Five new complete source-root terminal cylinders. -/
def excludedFive : List Nat := [1233,5117,7165,8189,14333]
theorem excludedFive_count : excludedFive.length=5 := by decide
theorem excludedFive_nodup : excludedFive.Nodup := by decide

theorem no_reach_five (r q : Nat) (hm : r ∈ excludedFive) :
    ¬ Reach (16384*q+r) (32768*q+2*r-1) := by
  simp only [excludedFive, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with h|h|h|h|h
  · subst r; simpa using no_reach_1233 q
  · subst r; simpa using no_reach_5117 q
  · subst r; simpa using no_reach_7165 q
  · subst r; simpa using no_reach_8189 q
  · subst r; simpa using no_reach_14333 q

/-- The genuine BB429 blank-start section never visits a terminal having any
    of these five first-counter residue classes modulo 16384. -/
theorem blank_halt_not_five (n a b : Nat)
    (hr : BB429.run n (0,0)=some (a,b))
    (hg : b+1=2*a) :
    a%16384 ∉ excludedFive := by
  intro hm
  let r := a%16384
  let q := a/16384
  have hrmem : r∈excludedFive := by simpa [r] using hm
  have hrpos : 0<r := by
    simp only [excludedFive, List.mem_cons, List.not_mem_nil, or_false] at hrmem
    omega
  have ha : a=16384*q+r := by dsimp [q,r]; omega
  have hb : b=32768*q+2*r-1 := by omega
  exact (no_reach_five r q hrmem) ⟨n, by simpa only [←ha,←hb] using hr⟩

#print axioms blank_halt_not_five
#print axioms no_reach_five
end BB429FiveShift
