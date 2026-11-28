import EvenV2
import OddV2Witness
import ResetEven
import Phase6Bridge
import Lean.Elab.Tactic.Omega

namespace BB6.Agent2F321OddTerminal
open BB6.Agent31F321Density
open BB6.Agent2F321Diagonal
open BB6.Agent2F321Bulk
open BB6.Agent2F321EvenV2

theorem middleEven_high_terminal_no_odd_v2_family
    {n k a d A D s u : Nat}
    (hr : CounterReach 1 1 n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 0)
    (hh : HighRun k (4*a+6) 2 A D)
    (ht : A = D + 1)
    (hk : k + 5 = 8 * 4^s * u)
    (hu : u % 2 = 1)
    (hlarge : 2*s + 4 ≤ k) : False := by
  have hev : EvenV2Form (a+2) := reached_below_even_evenV2 hr h1 hp
  have heq := high_run_terminal_equation hh ht
  unfold X Y at heq
  have heq4 : 4*(a+2) + (k+5) = 10 * 2^k := by omega
  rw [hk] at heq4
  obtain ⟨r,hrk⟩ : ∃ r, k = 2 + r := by
    apply Nat.exists_eq_add_of_le
    omega
  have hp2 : 2^(2+r) = 4 * 2^r := by
    rw [Nat.pow_add]
  rw [hrk, hp2] at heq4
  have heq4' : 4 * ((a+2) + 2*4^s*u) = 4 * (10*2^r) := by
    calc
      4 * ((a+2) + 2*4^s*u) = 4*(a+2) + 8*4^s*u := by
        rw [Nat.mul_add]
        have h42 : 4*2 = 8 := by decide
        calc
          4 * (a+2) + 4 * (2*4^s*u) = 4 * (a+2) + (4*2)*(4^s*u) := by congr 1 <;> ac_rfl
          _ = 4*(a+2) + 8*4^s*u := by rw [h42]; ac_rfl
      _ = 10 * (4*2^r) := heq4
      _ = 4 * (10*2^r) := by ac_rfl
  have heq1 : a+2 + 2*4^s*u = 10*2^r :=
    Nat.eq_of_mul_eq_mul_left (by decide) heq4'
  have hrs : 2*s + 2 ≤ r := by omega
  obtain ⟨w,hrw⟩ := Nat.exists_eq_add_of_le hrs
  rw [hrw] at heq1
  have hpows : 2^(2*s+2+w) = 4^s * 4 * 2^w := by
    rw [show 2*s+2+w=(2*s)+(2+w) by omega, Nat.pow_add]
    rw [show 2^(2*s)=4^s by
      rw [show 2*s=s+s by omega, Nat.pow_add]
      rw [show 4^s=(2*2)^s by rfl, Nat.mul_pow]]
    rw [Nat.pow_add]
    have h22 : 2^2 = 4 := by decide
    rw [h22]
    ac_rfl
  rw [hpows] at heq1
  let C := 2*4^s
  let B := 20*2^w
  have hR : 10 * (4^s * 4 * 2^w) = C * B := by
    dsimp [C,B]
    calc
      10 * (4^s * 4 * 2^w) = (10*4) * (4^s * 2^w) := by ac_rfl
      _ = (2*20) * (4^s * 2^w) := by rw [show 10*4 = 2*20 by decide]
      _ = (2*4^s) * (20*2^w) := by ac_rfl
  have heq2 : a+2 + C*u = C*B := by
    rw [← hR]
    simpa [C] using heq1
  have hCpos : 0 < C := by
    dsimp [C]
    exact Nat.mul_pos (by decide) (Nat.pow_pos (by decide))
  have hmul : C*u ≤ C*B := by omega
  have hub : u ≤ B := Nat.le_of_mul_le_mul_left hmul hCpos
  let v := B-u
  have hBeven : B % 2 = 0 := by
    dsimp [B]
    rw [show 20*2^w = 2*(10*2^w) by
      rw [show 20 = 2*10 by decide]
      ac_rfl]
    simp
  have hvodd : v % 2 = 1 := by
    dsimp [v]
    omega
  have hav : a+2 = C*v := by
    dsimp [v]
    calc
      a+2 = C*B - C*u := by omega
      _ = C*(B-u) := by rw [Nat.mul_sub_left_distrib]
  have hnot := BB6.Agent2F321OddV2Witness.oddV2Witness_not_evenV2 s v hvodd
  apply hnot
  rw [← hav]
  simpa [C] using hev

#print axioms middleEven_high_terminal_no_odd_v2_family
end BB6.Agent2F321OddTerminal

namespace BB6.Agent2F321OddTerminal
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321ResetEven
open BB6.Agent2F321Phase6Bridge

theorem linear_le_eight_pow_four (s : Nat) (hs : 1 ≤ s) :
    2*s + 9 ≤ 8 * 4^s := by
  induction s with
  | zero => omega
  | succ s ih =>
      by_cases h0 : s = 0
      · subst s
        decide
      · have hs' : 1 ≤ s := by omega
        have hi := ih hs'
        have hp : 1 ≤ 4^s := Nat.one_le_pow s 4 (by decide)
        rw [Nat.pow_succ]
        omega

theorem middleEven_high_terminal_no_odd_v2
    {n k a d A D s u : Nat}
    (hr : CounterReach 1 1 n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 0)
    (hh : HighRun k (4*a+6) 2 A D)
    (ht : A = D + 1)
    (hk : k + 5 = 8 * 4^s * u)
    (hu : u % 2 = 1) : False := by
  by_cases hs0 : s = 0
  · subst s
    simp at hk
    by_cases hu1 : u = 1
    · subst u
      have hk3 : k = 3 := by omega
      have hlocal := counterReach_to_reach hr
      have hnot := middleEven_high_terminal_not_mod16_three hlocal h1 h2 hp hh ht
      omega
    · have hu3 : 3 ≤ u := by omega
      have hlarge : 4 ≤ k := by omega
      exact middleEven_high_terminal_no_odd_v2_family (s:=0) (u:=u) hr h1 h2 hp hh ht hk hu hlarge
  · have hs1 : 1 ≤ s := by omega
    have hgrow := linear_le_eight_pow_four s hs1
    have hu0 : 0 < u := by omega
    have hmul : 8 * 4^s ≤ (8 * 4^s) * u :=
      Nat.le_mul_of_pos_right (8 * 4^s) hu0
    have hlarge : 2*s + 4 ≤ k := by omega
    exact middleEven_high_terminal_no_odd_v2_family hr h1 h2 hp hh ht hk hu hlarge

#print axioms middleEven_high_terminal_no_odd_v2
end BB6.Agent2F321OddTerminal


namespace BB6.Agent2F321OddTerminal
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321ResetEven

/-- Exact valuation-form corollary: every odd 2-adic valuation of k+5 is
    impossible for a root-reachable middle-even reset-to-terminal High run. -/
theorem middleEven_high_terminal_no_odd_v2_witness
    {n k a d A D s u : Nat}
    (hr : CounterReach 1 1 n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 0)
    (hh : HighRun k (4*a+6) 2 A D)
    (ht : A = D + 1)
    (hk : k + 5 = 2 * 4^s * u)
    (hu : u % 2 = 1) : False := by
  by_cases hs : s = 0
  · subst s
    simp at hk
    have h4 := middleEven_high_terminal_length_mod4 hh ht
    omega
  · obtain ⟨r,hr⟩ : ∃ r, s = r + 1 := by
      have hspos : 0 < s := by omega
      exact ⟨s-1, by omega⟩
    subst s
    have hk' : k + 5 = 8 * 4^r * u := by
      rw [Nat.pow_succ] at hk
      calc
        k + 5 = 2 * (4^r * 4) * u := hk
        _ = (2*4) * 4^r * u := by ac_rfl
        _ = 8 * 4^r * u := by rw [show 2*4 = 8 by decide]
    exact middleEven_high_terminal_no_odd_v2 hr h1 h2 hp hh ht hk' hu

#print axioms middleEven_high_terminal_no_odd_v2_witness
end BB6.Agent2F321OddTerminal
