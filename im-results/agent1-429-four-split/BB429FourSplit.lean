import BB429InverseKernel
import Lean.Elab.Tactic.Omega

namespace BB429FourSplit
set_option maxRecDepth 100000
set_option maxHeartbeats 40000000

/-- A pair of blank-run rank checkpoints gives a complete, all-time
    unreachability certificate, including the equal-rank boundary case. -/
theorem no_reach_rank_straddle
    (k : Nat) (prev after target : BB429.State)
    (hprev : BB429.run k (0,0) = some prev)
    (hafter : BB429.run (k+1) (0,0) = some after)
    (hlo : BB429.rank prev ≤ BB429.rank target)
    (hhi : BB429.rank target < BB429.rank after)
    (hne : prev ≠ target) :
    ∀n, BB429.run n (0,0) ≠ some target := by
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

private theorem no_201_seed :
    ¬ BB429NewResidue.Reach 201 401 := by
  rintro ⟨n,hr⟩
  exact no_reach_rank_straddle 168 (53,696) (109,587) (201,401)
    (by decide) (by decide) (by decide) (by decide) (by decide) n hr

private theorem no_201_tail (q:Nat) :
    ¬ BB429NewResidue.Reach (8192*q+8393) (16384*q+16785) := by
  have hc : BB429Kernel.cert 18 ⟨8192,8393,16384,16785⟩ = true := by decide
  exact BB429Kernel.cert_sound 18 ⟨8192,8393,16384,16785⟩ q hc

theorem no_reach_201 (q:Nat):
    ¬ BB429NewResidue.Reach (8192*q+201) (16384*q+401) := by
  cases q with
  | zero => simpa using no_201_seed
  | succ q =>
      have heq1 : 8192*(q+1)+201=8192*q+8393 := by omega
      have heq2 : 16384*(q+1)+401=16384*q+16785 := by omega
      simpa only [Nat.succ_eq_add_one, heq1, heq2] using no_201_tail q

private theorem no_209_seed :
    ¬ BB429NewResidue.Reach 209 417 := by
  rintro ⟨n,hr⟩
  exact no_reach_rank_straddle 173 (53,728) (109,619) (209,417)
    (by decide) (by decide) (by decide) (by decide) (by decide) n hr

private theorem no_209_tail (q:Nat) :
    ¬ BB429NewResidue.Reach (8192*q+8401) (16384*q+16801) := by
  have hc : BB429Kernel.cert 18 ⟨8192,8401,16384,16801⟩ = true := by decide
  exact BB429Kernel.cert_sound 18 ⟨8192,8401,16384,16801⟩ q hc

theorem no_reach_209 (q:Nat):
    ¬ BB429NewResidue.Reach (8192*q+209) (16384*q+417) := by
  cases q with
  | zero => simpa using no_209_seed
  | succ q =>
      have heq1 : 8192*(q+1)+209=8192*q+8401 := by omega
      have heq2 : 16384*(q+1)+417=16384*q+16801 := by omega
      simpa only [Nat.succ_eq_add_one, heq1, heq2] using no_209_tail q

private theorem no_245_seed :
    ¬ BB429NewResidue.Reach 245 489 := by
  rintro ⟨n,hr⟩
  exact no_reach_rank_straddle 198 (25,929) (53,876) (245,489)
    (by decide) (by decide) (by decide) (by decide) (by decide) n hr

private theorem no_245_tail (q:Nat) :
    ¬ BB429NewResidue.Reach (8192*q+8437) (16384*q+16873) := by
  have hc : BB429Kernel.cert 18 ⟨8192,8437,16384,16873⟩ = true := by decide
  exact BB429Kernel.cert_sound 18 ⟨8192,8437,16384,16873⟩ q hc

theorem no_reach_245 (q:Nat):
    ¬ BB429NewResidue.Reach (8192*q+245) (16384*q+489) := by
  cases q with
  | zero => simpa using no_245_seed
  | succ q =>
      have heq1 : 8192*(q+1)+245=8192*q+8437 := by omega
      have heq2 : 16384*(q+1)+489=16384*q+16873 := by omega
      simpa only [Nat.succ_eq_add_one, heq1, heq2] using no_245_tail q

private theorem no_637_seed :
    ¬ BB429NewResidue.Reach 637 1273 := by
  rintro ⟨n,hr⟩
  exact no_reach_rank_straddle 523 (893,752) (0,2548) (637,1273)
    (by decide) (by decide) (by decide) (by decide) (by decide) n hr

private theorem no_637_tail (q:Nat) :
    ¬ BB429NewResidue.Reach (8192*q+8829) (16384*q+17657) := by
  have hc : BB429Kernel.cert 18 ⟨8192,8829,16384,17657⟩ = true := by decide
  exact BB429Kernel.cert_sound 18 ⟨8192,8829,16384,17657⟩ q hc

theorem no_reach_637 (q:Nat):
    ¬ BB429NewResidue.Reach (8192*q+637) (16384*q+1273) := by
  cases q with
  | zero => simpa using no_637_seed
  | succ q =>
      have heq1 : 8192*(q+1)+637=8192*q+8829 := by omega
      have heq2 : 16384*(q+1)+1273=16384*q+17657 := by omega
      simpa only [Nat.succ_eq_add_one, heq1, heq2] using no_637_tail q

/-- Four entire genuine blank-start #429 halting cylinders are unreachable.
    None of the remaining cylinders is asserted reachable. -/
theorem blank_halt_not_four (n a b : Nat)
    (hr : BB429.run n (0,0) = some (a,b))
    (hg : b+1=2*a) :
    a%8192≠201 ∧ a%8192≠209 ∧ a%8192≠245 ∧ a%8192≠637 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hm
    let q := a/8192
    have ha : a=8192*q+201 := by dsimp [q]; omega
    have hb : b=16384*q+401 := by omega
    apply no_reach_201 q
    exact ⟨n,by simpa only [←ha,←hb] using hr⟩
  · intro hm
    let q := a/8192
    have ha : a=8192*q+209 := by dsimp [q]; omega
    have hb : b=16384*q+417 := by omega
    apply no_reach_209 q
    exact ⟨n,by simpa only [←ha,←hb] using hr⟩
  · intro hm
    let q := a/8192
    have ha : a=8192*q+245 := by dsimp [q]; omega
    have hb : b=16384*q+489 := by omega
    apply no_reach_245 q
    exact ⟨n,by simpa only [←ha,←hb] using hr⟩
  · intro hm
    let q := a/8192
    have ha : a=8192*q+637 := by dsimp [q]; omega
    have hb : b=16384*q+1273 := by omega
    apply no_reach_637 q
    exact ⟨n,by simpa only [←ha,←hb] using hr⟩
#print axioms no_reach_201
#print axioms no_reach_209
#print axioms no_reach_245
#print axioms no_reach_637
#print axioms blank_halt_not_four
end BB429FourSplit
