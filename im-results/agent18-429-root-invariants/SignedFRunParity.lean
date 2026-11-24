import Lean

namespace BB429SignedFRunParity

/-- A finite run of standalone F-blocks in the compressed signed system. -/
inductive FRun : Nat → Nat → Nat → Nat → Nat → Prop where
  | zero (u d : Nat) : FRun 0 u d u d
  | step {m u d um dm : Nat} (hu : u % 2 = 0)
      (tail : FRun m (u / 2) (d + 3 * u + 3) um dm) :
      FRun (m + 1) u d um dm

/-- The exact telescoping identity for a run of F-blocks. -/
theorem fRun_rank {m u d um dm : Nat} (h : FRun m u d um dm) :
    dm + 6 * um = d + 6 * u + 3 * m := by
  induction h with
  | zero u d => simp
  | @step m u d um dm hu tail ih =>
      have hdiv : u = 2 * (u / 2) := by omega
      omega

/-- Exact 2-adic scaling of the first coordinate through an F-run. -/
theorem fRun_power {m u d um dm : Nat} (h : FRun m u d um dm) :
    u = 2 ^ m * um := by
  induction h with
  | zero u d => simp
  | @step m u d um dm hu tail ih =>
      have hdiv : u = 2 * (u / 2) := by omega
      calc
        u = 2 * (u / 2) := hdiv
        _ = 2 * (2 ^ m * um) := by rw [ih]
        _ = 2 ^ (m + 1) * um := by
          simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]

/-- Every F-run consumes exactly its stated number of powers of two. -/
theorem fRun_power_dvd {m u d um dm : Nat} (h : FRun m u d um dm) :
    2 ^ m ∣ u := by
  exact ⟨um, fRun_power h⟩

/-- The compressed EF block. -/
def ef (v d : Nat) : Nat × Nat :=
  (v + (d + 8) / 8, d / 4 + 4)

/-- The compressed SF block. -/
def sf (v d : Nat) : Nat × Nat :=
  (v + (d + 20) / 8, d / 4 - 1)

/-- Exact affine relation after an EF block. -/
theorem ef_output_relation {v d : Nat} (h8 : d % 8 = 0) :
    (ef v d).2 + 2 * v = 2 * (ef v d).1 + 2 := by
  simp [ef]
  omega

/-- Exact affine relation after an SF block. -/
theorem sf_output_relation {v d : Nat} (h8 : d % 8 = 4) :
    (sf v d).2 + 2 * v + 6 = 2 * (sf v d).1 := by
  simp [sf]
  omega

/-- Initial branch-29 signed state after the forced F has D=2u+18.
    If an F-run from it is followed by EF or SF, its length has the
    corresponding even residue classes modulo 8. -/
theorem initial_run_residues {m u d um dm : Nat}
    (hrel : d = 2 * u + 18)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    (um % 2 = 1 ∧ dm % 8 = 0 ∧ (m % 8 = 0 ∨ m % 8 = 4)) ∨
    (um % 2 = 0 ∧ dm % 8 = 4 ∧ (m % 8 = 2 ∨ m % 8 = 6)) := by
  have hsum := fRun_rank hrun
  rcases hnext with ⟨hu, hd⟩ | ⟨hu, hd⟩
  · left
    exact ⟨hu, hd, by omega⟩
  · right
    exact ⟨hu, hd, by omega⟩

/-- After EF, an F-run followed by EF has length 2 or 6 modulo 8;
    one followed by SF has length 0 or 4 modulo 8. -/
theorem after_ef_run_residues {m u d v um dm : Nat}
    (hrel : d + 2 * v = 2 * u + 2)
    (hv : v % 2 = 1)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    (um % 2 = 1 ∧ dm % 8 = 0 ∧ (m % 8 = 2 ∨ m % 8 = 6)) ∨
    (um % 2 = 0 ∧ dm % 8 = 4 ∧ (m % 8 = 0 ∨ m % 8 = 4)) := by
  have hsum := fRun_rank hrun
  rcases hnext with ⟨hu, hd⟩ | ⟨hu, hd⟩
  · left
    exact ⟨hu, hd, by omega⟩
  · right
    exact ⟨hu, hd, by omega⟩

/-- After SF, an F-run followed by EF has length 0 or 4 modulo 8;
    one followed by SF has length 2 or 6 modulo 8. -/
theorem after_sf_run_residues {m u d v um dm : Nat}
    (hrel : d + 2 * v + 6 = 2 * u)
    (hv : v % 2 = 0)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    (um % 2 = 1 ∧ dm % 8 = 0 ∧ (m % 8 = 0 ∨ m % 8 = 4)) ∨
    (um % 2 = 0 ∧ dm % 8 = 4 ∧ (m % 8 = 2 ∨ m % 8 = 6)) := by
  have hsum := fRun_rank hrun
  rcases hnext with ⟨hu, hd⟩ | ⟨hu, hd⟩
  · left
    exact ⟨hu, hd, by omega⟩
  · right
    exact ⟨hu, hd, by omega⟩

/-- Every F-run from the initial line that is followed by a pair has even length. -/
theorem initial_run_even {m u d um dm : Nat}
    (hrel : d = 2 * u + 18)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    m % 2 = 0 := by
  have h := initial_run_residues hrel hrun hnext
  rcases h with ⟨_, _, hm⟩ | ⟨_, _, hm⟩ <;> omega


/-- Refined endpoint table after EF, recording the previous endpoint
    modulo four. -/
theorem after_ef_run_refined_residues {m u d v um dm : Nat}
    (hrel : d + 2 * v = 2 * u + 2)
    (hv : v % 2 = 1)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    (v % 4 = 1 ∧
      ((um % 2 = 1 ∧ dm % 8 = 0 ∧
          ((m % 8 = 2 ∧ um % 4 = 1) ∨ (m % 8 = 6 ∧ um % 4 = 3))) ∨
       (um % 2 = 0 ∧ dm % 8 = 4 ∧
          ((m % 8 = 0 ∧ um % 4 = 2) ∨ (m % 8 = 4 ∧ um % 4 = 0))))) ∨
    (v % 4 = 3 ∧
      ((um % 2 = 1 ∧ dm % 8 = 0 ∧
          ((m % 8 = 2 ∧ um % 4 = 3) ∨ (m % 8 = 6 ∧ um % 4 = 1))) ∨
       (um % 2 = 0 ∧ dm % 8 = 4 ∧
          ((m % 8 = 0 ∧ um % 4 = 0) ∨ (m % 8 = 4 ∧ um % 4 = 2))))) := by
  have hsum := fRun_rank hrun
  by_cases hv1 : v % 4 = 1
  · left
    refine ⟨hv1, ?_⟩
    rcases hnext with ⟨hu,hd⟩ | ⟨hu,hd⟩
    · left
      exact ⟨hu,hd,by omega⟩
    · right
      exact ⟨hu,hd,by omega⟩
  · right
    have hv3 : v % 4 = 3 := by omega
    refine ⟨hv3, ?_⟩
    rcases hnext with ⟨hu,hd⟩ | ⟨hu,hd⟩
    · left
      exact ⟨hu,hd,by omega⟩
    · right
      exact ⟨hu,hd,by omega⟩

/-- Refined endpoint table after SF, recording the previous endpoint
    modulo four. -/
theorem after_sf_run_refined_residues {m u d v um dm : Nat}
    (hrel : d + 2 * v + 6 = 2 * u)
    (hv : v % 2 = 0)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    (v % 4 = 0 ∧
      ((um % 2 = 1 ∧ dm % 8 = 0 ∧
          ((m % 8 = 0 ∧ um % 4 = 3) ∨ (m % 8 = 4 ∧ um % 4 = 1))) ∨
       (um % 2 = 0 ∧ dm % 8 = 4 ∧
          ((m % 8 = 2 ∧ um % 4 = 2) ∨ (m % 8 = 6 ∧ um % 4 = 0))))) ∨
    (v % 4 = 2 ∧
      ((um % 2 = 1 ∧ dm % 8 = 0 ∧
          ((m % 8 = 0 ∧ um % 4 = 1) ∨ (m % 8 = 4 ∧ um % 4 = 3))) ∨
       (um % 2 = 0 ∧ dm % 8 = 4 ∧
          ((m % 8 = 2 ∧ um % 4 = 0) ∨ (m % 8 = 6 ∧ um % 4 = 2))))) := by
  have hsum := fRun_rank hrun
  by_cases hv0 : v % 4 = 0
  · left
    refine ⟨hv0, ?_⟩
    rcases hnext with ⟨hu,hd⟩ | ⟨hu,hd⟩
    · left
      exact ⟨hu,hd,by omega⟩
    · right
      exact ⟨hu,hd,by omega⟩
  · right
    have hv2 : v % 4 = 2 := by omega
    refine ⟨hv2, ?_⟩
    rcases hnext with ⟨hu,hd⟩ | ⟨hu,hd⟩
    · left
      exact ⟨hu,hd,by omega⟩
    · right
      exact ⟨hu,hd,by omega⟩


/-- The first coordinate of EF, in denominator-free form under its guard. -/
theorem ef_u_formula {v d : Nat} (h8 : d % 8 = 0) :
    8 * (ef v d).1 = 8 * v + d + 8 := by
  have hd : d = 8 * (d / 8) := by
    have h := Nat.mod_add_div d 8
    omega
  have hsum : d + 8 = 8 * (d / 8 + 1) := by omega
  have hq : (d + 8) / 8 = d / 8 + 1 := by
    rw [hsum]
    exact Nat.mul_div_cancel_left (d / 8 + 1) (n:=8) (by decide)
  simp [ef, hq]
  omega

/-- The first coordinate of SF, in denominator-free form under its guard. -/
theorem sf_u_formula {v d : Nat} (h8 : d % 8 = 4) :
    8 * (sf v d).1 = 8 * v + d + 20 := by
  have hd : d = 8 * (d / 8) + 4 := by
    have h := Nat.mod_add_div d 8
    omega
  have hsum : d + 20 = 8 * (d / 8 + 3) := by omega
  have hq : (d + 20) / 8 = d / 8 + 3 := by
    rw [hsum]
    exact Nat.mul_div_cancel_left (d / 8 + 3) (n:=8) (by decide)
  simp [sf, hq]
  omega

/-- Exact next-u recurrence when an EF edge is followed by another EF
    after an F-run. -/
theorem ef_ef_pair_recurrence {m u d v um dm : Nat}
    (hrel : d + 2 * v = 2 * u + 2)
    (hrun : FRun m u d um dm)
    (hdm : dm % 8 = 0) :
    8 * (ef um dm).1 + 2 * v = 8 * u + 2 * um + 3 * m + 10 := by
  have hsum := fRun_rank hrun
  have hpair := ef_u_formula (v:=um) hdm
  omega

/-- Exact next-u recurrence when an EF edge is followed by an SF
    after an F-run. -/
theorem ef_sf_pair_recurrence {m u d v um dm : Nat}
    (hrel : d + 2 * v = 2 * u + 2)
    (hrun : FRun m u d um dm)
    (hdm : dm % 8 = 4) :
    8 * (sf um dm).1 + 2 * v = 8 * u + 2 * um + 3 * m + 22 := by
  have hsum := fRun_rank hrun
  have hpair := sf_u_formula (v:=um) hdm
  omega

/-- Exact next-u recurrence when an SF edge is followed by an EF
    after an F-run. -/
theorem sf_ef_pair_recurrence {m u d v um dm : Nat}
    (hrel : d + 2 * v + 6 = 2 * u)
    (hrun : FRun m u d um dm)
    (hdm : dm % 8 = 0) :
    8 * (ef um dm).1 + 2 * v = 8 * u + 2 * um + 3 * m + 2 := by
  have hsum := fRun_rank hrun
  have hpair := ef_u_formula (v:=um) hdm
  omega

/-- Exact next-u recurrence when an SF edge is followed by another SF
    after an F-run. -/
theorem sf_sf_pair_recurrence {m u d v um dm : Nat}
    (hrel : d + 2 * v + 6 = 2 * u)
    (hrun : FRun m u d um dm)
    (hdm : dm % 8 = 4) :
    8 * (sf um dm).1 + 2 * v = 8 * u + 2 * um + 3 * m + 14 := by
  have hsum := fRun_rank hrun
  have hpair := sf_u_formula (v:=um) hdm
  omega


/-- Pair-rank update for EF followed by EF. -/
theorem ef_ef_pair_rank {m u d v um dm : Nat}
    (hrel : d + 2 * v = 2 * u + 2)
    (hrun : FRun m u d um dm)
    (hdm : dm % 8 = 0)
    (hm : m % 2 = 0) :
    4 * (ef um dm).1 + v = 4 * u + um + 3 * (m / 2) + 5 := by
  have hrec := ef_ef_pair_recurrence hrel hrun hdm
  have hmd : m = 2 * (m / 2) := by
    have h := Nat.mod_add_div m 2
    omega
  omega

/-- Pair-rank update for EF followed by SF. -/
theorem ef_sf_pair_rank {m u d v um dm : Nat}
    (hrel : d + 2 * v = 2 * u + 2)
    (hrun : FRun m u d um dm)
    (hdm : dm % 8 = 4)
    (hm : m % 2 = 0) :
    4 * (sf um dm).1 + v = 4 * u + um + 3 * (m / 2) + 11 := by
  have hrec := ef_sf_pair_recurrence hrel hrun hdm
  have hmd : m = 2 * (m / 2) := by
    have h := Nat.mod_add_div m 2
    omega
  omega

/-- Pair-rank update for SF followed by EF. -/
theorem sf_ef_pair_rank {m u d v um dm : Nat}
    (hrel : d + 2 * v + 6 = 2 * u)
    (hrun : FRun m u d um dm)
    (hdm : dm % 8 = 0)
    (hm : m % 2 = 0) :
    4 * (ef um dm).1 + v = 4 * u + um + 3 * (m / 2) + 1 := by
  have hrec := sf_ef_pair_recurrence hrel hrun hdm
  have hmd : m = 2 * (m / 2) := by
    have h := Nat.mod_add_div m 2
    omega
  omega

/-- Pair-rank update for SF followed by SF. -/
theorem sf_sf_pair_rank {m u d v um dm : Nat}
    (hrel : d + 2 * v + 6 = 2 * u)
    (hrun : FRun m u d um dm)
    (hdm : dm % 8 = 4)
    (hm : m % 2 = 0) :
    4 * (sf um dm).1 + v = 4 * u + um + 3 * (m / 2) + 7 := by
  have hrec := sf_sf_pair_recurrence hrel hrun hdm
  have hmd : m = 2 * (m / 2) := by
    have h := Nat.mod_add_div m 2
    omega
  omega

/-- Every F-run after EF that is followed by a pair has even length. -/
theorem after_ef_run_even {m u d v um dm : Nat}
    (hrel : d + 2 * v = 2 * u + 2)
    (hv : v % 2 = 1)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    m % 2 = 0 := by
  have h := after_ef_run_residues hrel hv hrun hnext
  rcases h with ⟨_, _, hm⟩ | ⟨_, _, hm⟩ <;> omega

/-- Every F-run after SF that is followed by a pair has even length. -/
theorem after_sf_run_even {m u d v um dm : Nat}
    (hrel : d + 2 * v + 6 = 2 * u)
    (hv : v % 2 = 0)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    m % 2 = 0 := by
  have h := after_sf_run_residues hrel hv hrun hnext
  rcases h with ⟨_, _, hm⟩ | ⟨_, _, hm⟩ <;> omega

/-- The full modulo-eight endpoint classification, including the
    endpoint first coordinate modulo four. -/
theorem initial_run_refined_residues {m u d um dm : Nat}
    (hrel : d = 2 * u + 18)
    (hrun : FRun m u d um dm)
    (hnext :
      (um % 2 = 1 ∧ dm % 8 = 0) ∨
      (um % 2 = 0 ∧ dm % 8 = 4)) :
    (um % 2 = 1 ∧ dm % 8 = 0 ∧
      ((m % 8 = 0 ∧ um % 4 = 3) ∨ (m % 8 = 4 ∧ um % 4 = 1))) ∨
    (um % 2 = 0 ∧ dm % 8 = 4 ∧
      ((m % 8 = 2 ∧ um % 4 = 2) ∨ (m % 8 = 6 ∧ um % 4 = 0))) := by
  have hsum := fRun_rank hrun
  rcases hnext with ⟨hu, hd⟩ | ⟨hu, hd⟩
  · left
    refine ⟨hu, hd, ?_⟩
    omega
  · right
    refine ⟨hu, hd, ?_⟩
    omega

/-- A pair is available somewhere along the initial F-only spine. -/
def InitialPairAvailable (t : Nat) : Prop :=
  ∃ m um dm, FRun m (48*t) (96*t+18) um dm ∧
    ((um % 2 = 1 ∧ dm % 8 = 0) ∨
     (um % 2 = 0 ∧ dm % 8 = 4))

private theorem pow8_dvd_initial {t m um : Nat}
    (hm : 8 ≤ m) (hpow : 48*t = 2^m*um) :
    2^8 ∣ 48*t := by
  have hp : 2^8 ∣ 2^m := Nat.pow_dvd_pow 2 hm
  exact Nat.dvd_trans hp ⟨um, hpow⟩

private theorem pow8_dvd_initial_with_even_endpoint {t m um : Nat}
    (hm : 6 ≤ m) (hu4 : um % 4 = 0)
    (hpow : 48*t = 2^m*um) :
    2^8 ∣ 48*t := by
  have hfour : 4 ∣ um := Nat.dvd_of_mod_eq_zero hu4
  have hp : 2^(m+2) ∣ 48*t := by
    have hmul : 2^m * 4 ∣ 2^m * um :=
      Nat.mul_dvd_mul_left (2^m) hfour
    have heq : 2^(m+2) = 2^m * 4 := by
      rw [Nat.pow_add]
    rw [← hpow] at hmul
    rw [heq]
    exact hmul
  have hpow8 : 2^8 ∣ 2^(m+2) := Nat.pow_dvd_pow 2 (by omega)
  exact Nat.dvd_trans hpow8 hp

private theorem sixteen_dvd_of_pow8_dvd {t : Nat}
    (h : 2^8 ∣ 48*t) : t % 16 = 0 := by
  obtain ⟨q,hq⟩ := h
  omega

/-- Necessary condition for a pair on the initial F-spine. -/
theorem initial_pair_available_necessary {t : Nat}
    (h : InitialPairAvailable t) :
    t % 4 = 3 ∨ t % 16 = 0 := by
  rcases h with ⟨m,um,dm,hrun,hnext⟩
  have hres := initial_run_refined_residues
    (u:=48*t) (d:=96*t+18) (by omega) hrun hnext
  have hpow := fRun_power hrun
  rcases hres with ⟨hu,hd,hcases⟩ | ⟨hu,hd,hcases⟩
  · rcases hcases with ⟨hm,hum4⟩ | ⟨hm,hum4⟩
    · have hmpos : 8 ≤ m := by
        by_cases hm0 : m = 0
        · rw [hm0] at hpow
          simp at hpow
          omega
        · omega
      right
      exact sixteen_dvd_of_pow8_dvd (pow8_dvd_initial hmpos hpow)
    · by_cases hm4 : m = 4
      · left
        rw [hm4] at hpow
        simp at hpow
        omega
      · have hm8 : 8 ≤ m := by omega
        right
        exact sixteen_dvd_of_pow8_dvd (pow8_dvd_initial hm8 hpow)
  · rcases hcases with ⟨hm,hum4⟩ | ⟨hm,hum4⟩
    · have hm10 : 10 ≤ m := by
        by_cases hm2 : m = 2
        · rw [hm2] at hpow
          simp at hpow
          omega
        · omega
      have hm8 : 8 ≤ m := by omega
      right
      exact sixteen_dvd_of_pow8_dvd (pow8_dvd_initial hm8 hpow)
    · have hm6 : 6 ≤ m := by omega
      right
      exact sixteen_dvd_of_pow8_dvd
        (pow8_dvd_initial_with_even_endpoint hm6 hum4 hpow)

/-- The explicit four-step F spine from the initial parameter line. -/
theorem initial_four_F_run (t : Nat) :
    FRun 4 (48*t) (96*t+18) (3*t) (366*t+30) := by
  refine FRun.step (by omega) ?_
  rw [show 48*t/2 = 24*t by omega]
  rw [show 96*t+18+3*(48*t)+3 = 240*t+21 by omega]
  refine FRun.step (by omega) ?_
  rw [show 24*t/2 = 12*t by omega]
  rw [show 240*t+21+3*(24*t)+3 = 312*t+24 by omega]
  refine FRun.step (by omega) ?_
  rw [show 12*t/2 = 6*t by omega]
  rw [show 312*t+24+3*(12*t)+3 = 348*t+27 by omega]
  refine FRun.step (by omega) ?_
  rw [show 6*t/2 = 3*t by omega]
  rw [show 348*t+27+3*(6*t)+3 = 366*t+30 by omega]
  exact FRun.zero (3*t) (366*t+30)

/-- The explicit six-step F spine when 16 divides t. -/
theorem initial_six_F_run {s : Nat} :
    FRun 6 (768*s) (1536*s+18) (12*s) (6072*s+36) := by
  refine FRun.step (by omega) ?_
  rw [show 768*s/2 = 384*s by omega]
  rw [show 1536*s+18+3*(768*s)+3 = 3840*s+21 by omega]
  refine FRun.step (by omega) ?_
  rw [show 384*s/2 = 192*s by omega]
  rw [show 3840*s+21+3*(384*s)+3 = 4992*s+24 by omega]
  refine FRun.step (by omega) ?_
  rw [show 192*s/2 = 96*s by omega]
  rw [show 4992*s+24+3*(192*s)+3 = 5568*s+27 by omega]
  refine FRun.step (by omega) ?_
  rw [show 96*s/2 = 48*s by omega]
  rw [show 5568*s+27+3*(96*s)+3 = 5856*s+30 by omega]
  refine FRun.step (by omega) ?_
  rw [show 48*s/2 = 24*s by omega]
  rw [show 5856*s+30+3*(48*s)+3 = 6000*s+33 by omega]
  refine FRun.step (by omega) ?_
  rw [show 24*s/2 = 12*s by omega]
  rw [show 6000*s+33+3*(24*s)+3 = 6072*s+36 by omega]
  exact FRun.zero (12*s) (6072*s+36)

/-- Four initial F-blocks land on EF exactly when t=3 mod 4. -/
theorem initial_EF_witness {t : Nat} (ht : t % 4 = 3) :
    ∃ dm, FRun 4 (48*t) (96*t+18) (3*t) dm ∧
      (3*t % 2 = 1 ∧ dm % 8 = 0) := by
  refine ⟨366*t+30, initial_four_F_run t, ?_⟩
  omega

/-- Six initial F-blocks land on SF whenever t is divisible by 16. -/
theorem initial_SF_witness {t : Nat} (ht : t % 16 = 0) :
    ∃ dm, FRun 6 (48*t) (96*t+18) (12*(t/16)) dm ∧
      (12*(t/16) % 2 = 0 ∧ dm % 8 = 4) := by
  let s := t/16
  have hts : t = 16*s := by dsimp [s]; omega
  refine ⟨6072*s+36, ?_, ?_⟩
  · rw [hts]
    have hdiv : 16*s/16 = s := Nat.mul_div_cancel_left s (n:=16) (by decide)
    rw [hdiv]
    have hu : 48*(16*s) = 768*s := by omega
    have hd : 96*(16*s)+18 = 1536*s+18 := by omega
    rw [hu, hd]
    exact initial_six_F_run
  · rw [hts]
    have hdiv : 16*s/16 = s := Nat.mul_div_cancel_left s (n:=16) (by decide)
    rw [hdiv]
    omega

/-- Exact first-pair classification on the initial signed F-spine. -/
theorem initial_pair_available_iff {t : Nat} :
    InitialPairAvailable t ↔ t % 4 = 3 ∨ t % 16 = 0 := by
  constructor
  · exact initial_pair_available_necessary
  · intro h
    rcases h with ht | ht
    · obtain ⟨dm,hrun,hpair⟩ := initial_EF_witness ht
      exact ⟨4,3*t,dm,hrun,Or.inl hpair⟩
    · obtain ⟨dm,hrun,hpair⟩ := initial_SF_witness ht
      exact ⟨6,12*(t/16),dm,hrun,Or.inr hpair⟩


#print axioms fRun_rank
#print axioms ef_output_relation
#print axioms sf_output_relation
#print axioms initial_run_residues
#print axioms after_ef_run_residues
#print axioms after_sf_run_residues
#print axioms initial_run_even
#print axioms after_ef_run_even
#print axioms after_sf_run_even

#print axioms ef_ef_pair_rank
#print axioms ef_sf_pair_rank
#print axioms sf_ef_pair_rank
#print axioms sf_sf_pair_rank
#print axioms ef_u_formula
#print axioms sf_u_formula
#print axioms ef_ef_pair_recurrence
#print axioms ef_sf_pair_recurrence
#print axioms sf_ef_pair_recurrence
#print axioms sf_sf_pair_recurrence
#print axioms after_ef_run_refined_residues
#print axioms after_sf_run_refined_residues
#print axioms initial_run_refined_residues
#print axioms initial_pair_available_necessary
#print axioms initial_EF_witness
#print axioms initial_SF_witness
#print axioms initial_pair_available_iff

end BB429SignedFRunParity
