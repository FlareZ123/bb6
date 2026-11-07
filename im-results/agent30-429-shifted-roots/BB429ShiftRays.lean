import BB429InverseKernel16
import Lean.Elab.Tactic.Omega

/-!
Exact blank-root exclusions for four BB429 terminal cylinders.
Imports the existing unchanged affine inverse soundness theorem and uses
finite rank straddles solely for parameter zero. The rank-straddle
method was previously introduced by Agent 1 and used by Agent 33.
-/
namespace BB429ShiftRays
open BB429NewResidue
set_option maxHeartbeats 30000000
set_option maxRecDepth 40000

private theorem rank_straddle
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

private theorem cp1000 : BB429.run 1000 (0,0)=some (53,4556) := by decide

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

private theorem cp16107 : BB429.run 16107 (0,0)=some (16396,32722) := by
  rw [show (16107:Nat)=16000+107 by decide, BB429.run_add, cp16000]
  decide

private theorem cp16108 : BB429.run 16108 (0,0)=some (0,65524) := by
  rw [show (16108:Nat)=16107+1 by decide, BB429.run_add, cp16107]
  decide

/-- The authentic blank run crosses this rank without hitting the target. -/
private theorem seed_765_32768 : ¬Reach 765 1529 := by
  rintro ⟨n,hr⟩
  exact rank_straddle 638 (9,3040) (21,3019)
    (765,1529) (by decide) (by decide) (by decide) (by decide) (by decide) n hr

/-- The source-sound inverse certifier handles all positive quotients. -/
private theorem positive_765_32768 (q:Nat) :
    ¬Reach (32768*q+33533) (65536*q+67065) := by
  have hc : BB429Kernel16.cert 16 ⟨32768,33533,65536,67065⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16 ⟨32768,33533,65536,67065⟩ q hc

/-- This infinite affine family is unreachable from the true blank root. -/
theorem no_reach_765_32768 (q:Nat) :
    ¬Reach (32768*q+765) (65536*q+1529) := by
  cases q with
  | zero => simpa using seed_765_32768
  | succ q =>
    have h1 : 32768*(q+1)+765=32768*q+33533 := by omega
    have h2 : 65536*(q+1)+1529=65536*q+67065 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_765_32768 q)

/-- The entire corresponding necessary halting cylinder is excluded. -/
theorem blank_halt_not_765_mod_32768 (n a b : Nat)
    (hr:BB429.run n (0,0)=some (a,b)) (hg:b+1=2*a) :
    a%32768≠765 := by
  intro hm
  let q := a/32768
  have ha : a=32768*q+765 := by dsimp [q]; omega
  have hb : b=65536*q+1529 := by omega
  exact (no_reach_765_32768 q) ⟨n,by simpa only [←ha,←hb] using hr⟩

/-- The authentic blank run crosses this rank without hitting the target. -/
private theorem seed_3281_32768 : ¬Reach 3281 6561 := by
  rintro ⟨n,hr⟩
  exact rank_straddle 3171 (25,13073) (53,13020)
    (3281,6561) (by decide) (by decide) (by decide) (by decide) (by decide) n hr

/-- The source-sound inverse certifier handles all positive quotients. -/
private theorem positive_3281_32768 (q:Nat) :
    ¬Reach (32768*q+36049) (65536*q+72097) := by
  have hc : BB429Kernel16.cert 16 ⟨32768,36049,65536,72097⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16 ⟨32768,36049,65536,72097⟩ q hc

/-- This infinite affine family is unreachable from the true blank root. -/
theorem no_reach_3281_32768 (q:Nat) :
    ¬Reach (32768*q+3281) (65536*q+6561) := by
  cases q with
  | zero => simpa using seed_3281_32768
  | succ q =>
    have h1 : 32768*(q+1)+3281=32768*q+36049 := by omega
    have h2 : 65536*(q+1)+6561=65536*q+72097 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_3281_32768 q)

/-- The entire corresponding necessary halting cylinder is excluded. -/
theorem blank_halt_not_3281_mod_32768 (n a b : Nat)
    (hr:BB429.run n (0,0)=some (a,b)) (hg:b+1=2*a) :
    a%32768≠3281 := by
  intro hm
  let q := a/32768
  have ha : a=32768*q+3281 := by dsimp [q]; omega
  have hb : b=65536*q+6561 := by omega
  exact (no_reach_3281_32768 q) ⟨n,by simpa only [←ha,←hb] using hr⟩

/-- The authentic blank run crosses this rank without hitting the target. -/
private theorem seed_2385_262144 : ¬Reach 2385 4769 := by
  rintro ⟨n,hr⟩
  exact rank_straddle 2246 (3069,3396) (0,9544)
    (2385,4769) (by decide) (by decide) (by decide) (by decide) (by decide) n hr

/-- The source-sound inverse certifier handles all positive quotients. -/
private theorem positive_2385_262144 (q:Nat) :
    ¬Reach (262144*q+264529) (524288*q+529057) := by
  have hc : BB429Kernel16.cert 16 ⟨262144,264529,524288,529057⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16 ⟨262144,264529,524288,529057⟩ q hc

/-- This infinite affine family is unreachable from the true blank root. -/
theorem no_reach_2385_262144 (q:Nat) :
    ¬Reach (262144*q+2385) (524288*q+4769) := by
  cases q with
  | zero => simpa using seed_2385_262144
  | succ q =>
    have h1 : 262144*(q+1)+2385=262144*q+264529 := by omega
    have h2 : 524288*(q+1)+4769=524288*q+529057 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_2385_262144 q)

/-- The entire corresponding necessary halting cylinder is excluded. -/
theorem blank_halt_not_2385_mod_262144 (n a b : Nat)
    (hr:BB429.run n (0,0)=some (a,b)) (hg:b+1=2*a) :
    a%262144≠2385 := by
  intro hm
  let q := a/262144
  have ha : a=262144*q+2385 := by dsimp [q]; omega
  have hb : b=524288*q+4769 := by omega
  exact (no_reach_2385_262144 q) ⟨n,by simpa only [←ha,←hb] using hr⟩

/-- The authentic blank run crosses this rank without hitting the target. -/
private theorem seed_16381_131072 : ¬Reach 16381 32761 := by
  rintro ⟨n,hr⟩
  exact rank_straddle 16107 (16396,32722) (0,65524)
    (16381,32761) cp16107 cp16108 (by decide) (by decide) (by decide) n hr

/-- The source-sound inverse certifier handles all positive quotients. -/
private theorem positive_16381_131072 (q:Nat) :
    ¬Reach (131072*q+147453) (262144*q+294905) := by
  have hc : BB429Kernel16.cert 16 ⟨131072,147453,262144,294905⟩ = true := by decide
  exact BB429Kernel16.cert_sound 16 ⟨131072,147453,262144,294905⟩ q hc

/-- This infinite affine family is unreachable from the true blank root. -/
theorem no_reach_16381_131072 (q:Nat) :
    ¬Reach (131072*q+16381) (262144*q+32761) := by
  cases q with
  | zero => simpa using seed_16381_131072
  | succ q =>
    have h1 : 131072*(q+1)+16381=131072*q+147453 := by omega
    have h2 : 262144*(q+1)+32761=262144*q+294905 := by omega
    simpa only [Nat.succ_eq_add_one, h1, h2] using (positive_16381_131072 q)

/-- The entire corresponding necessary halting cylinder is excluded. -/
theorem blank_halt_not_16381_mod_131072 (n a b : Nat)
    (hr:BB429.run n (0,0)=some (a,b)) (hg:b+1=2*a) :
    a%131072≠16381 := by
  intro hm
  let q := a/131072
  have ha : a=131072*q+16381 := by dsimp [q]; omega
  have hb : b=262144*q+32761 := by omega
  exact (no_reach_16381_131072 q) ⟨n,by simpa only [←ha,←hb] using hr⟩

#print axioms no_reach_765_32768
#print axioms blank_halt_not_765_mod_32768
#print axioms blank_halt_not_3281_mod_32768
#print axioms blank_halt_not_2385_mod_262144
#print axioms blank_halt_not_16381_mod_131072
end BB429ShiftRays
