import ResetHigh
import ResetEven
import OddTerminal
import Lean.Elab.Tactic.Omega

/-!
Root-specific identification of the two persistent symbolic-inverse obstructions
inside the F321 terminal ray d ≡ 4093 (mod 12288).

The finite affine predecessor generator fails along two structured spines. This
file identifies those spines exactly with the authentic Middle-reset followed by
High-only terminal mechanisms, and transports the existing root restrictions onto
the spine indices.
-/

namespace BB6.Agent2F321ObstructionAlignment
open BB6.Agent31F321Density
open BB6.Agent2F321Bulk
open BB6.Agent2F321ResetHigh
open BB6.Agent2F321ResetEven
open BB6.Agent2F321OddTerminal
open BB6.Agent2F321Phase6Bridge

def farThresholdSpine : Nat → Nat
  | 0 => 0
  | m+1 => 4 * farThresholdSpine m + 1

theorem farThresholdSpine_identity (m : Nat) :
    12288 * farThresholdSpine m + 4096 = 2^(12 + 2*m) := by
  induction m with
  | zero => decide
  | succ m ih =>
      rw [farThresholdSpine]
      rw [show 12 + 2*(m+1) = (12 + 2*m) + 2 by omega, Nat.pow_add]
      have h2 : 2^2 = 4 := by decide
      rw [h2]
      omega

def middleUnboundedSpine : Nat → Nat
  | 0 => 13
  | j+1 => 16 * middleUnboundedSpine j + 5

theorem middleUnboundedSpine_identity (j : Nat) :
    12288 * middleUnboundedSpine j + 4096 = 5 * 2^(15 + 4*j) := by
  induction j with
  | zero => decide
  | succ j ih =>
      rw [middleUnboundedSpine]
      rw [show 15 + 4*(j+1) = (15 + 4*j) + 4 by omega, Nat.pow_add]
      have h4 : 2^4 = 16 := by decide
      rw [h4]
      omega

private theorem four_pow_shift (m : Nat) :
    4 * 2^(10 + 2*m) = 2^(12 + 2*m) := by
  rw [show 12 + 2*m = (10 + 2*m) + 2 by omega, Nat.pow_add]
  have h2 : 2^2 = 4 := by decide
  rw [h2]
  ac_rfl

theorem middleOdd_terminal_on_farThresholdSpine
    {n k a d A D : Nat}
    (hr : CounterReach 1 1 n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 1)
    (hh : HighRun k (4*a+6) 1 A D)
    (ht : A = D + 1)
    (hlarge : 12 ≤ k) :
    ∃ m : Nat, m % 4 = 1 ∧
      D = 12288 * farThresholdSpine m + 4093 := by
  have hlocal := counterReach_to_reach hr
  have hterm := middleOdd_high_terminal_parameter hlocal h1 h2 hp hh ht
  let m := (k - 10) / 2
  have hk : k = 10 + 2*m := by
    dsimp [m]
    omega
  have hm : m % 4 = 1 := by
    dsimp [m]
    omega
  refine ⟨m, hm, ?_⟩
  have hsp := farThresholdSpine_identity m
  have hpw := four_pow_shift m
  rw [hk] at hterm
  omega

private theorem middle_index_of_root_candidates {k : Nat}
    (hlarge : 15 ≤ k)
    (hc : k % 16 = 7 ∨ k % 16 = 11 ∨ k % 16 = 15) :
    ∃ j : Nat, k = 15 + 4*j ∧ j % 4 ≠ 1 := by
  let j := (k - 15) / 4
  have hk : k = 15 + 4*j := by
    dsimp [j]
    omega
  have hj : j % 4 ≠ 1 := by
    dsimp [j]
    omega
  exact ⟨j,hk,hj⟩

theorem middleEven_terminal_on_middleUnboundedSpine
    {n k a d A D : Nat}
    (hr : CounterReach 1 1 n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 0)
    (hh : HighRun k (4*a+6) 2 A D)
    (ht : A = D + 1)
    (hlarge : 15 ≤ k) :
    ∃ j : Nat, j % 4 ≠ 1 ∧
      D = 12288 * middleUnboundedSpine j + 4093 := by
  have hlocal := counterReach_to_reach hr
  have hc :=
    middleEven_high_terminal_length_mod16_candidates hlocal h1 h2 hp hh ht
  obtain ⟨j,hk,hj⟩ := middle_index_of_root_candidates hlarge hc
  have hpar := middleEven_high_terminal_parameter hh ht
  refine ⟨j,hj,?_⟩
  have hsp := middleUnboundedSpine_identity j
  rw [hk] at hpar
  omega

theorem middleUnboundedSpine_index_no_odd_v2
    {n k a d A D j s u : Nat}
    (hr : CounterReach 1 1 n a d)
    (h1 : a < d) (h2 : d < 3*a+1) (hp : (d-a)%2 = 0)
    (hh : HighRun k (4*a+6) 2 A D)
    (ht : A = D + 1)
    (hk : k = 15 + 4*j)
    (hj : j + 5 = 2 * 4^s * u)
    (hu : u % 2 = 1) : False := by
  have hkodd : k + 5 = 2 * 4^(s+1) * u := by
    calc
      k + 5 = 4 * (j+5) := by omega
      _ = 4 * (2 * 4^s * u) := by rw [hj]
      _ = 2 * (4^s * 4) * u := by ac_rfl
      _ = 2 * 4^(s+1) * u := by rw [Nat.pow_succ]
  exact middleEven_high_terminal_no_odd_v2_witness
    hr h1 h2 hp hh ht hkodd hu

#print axioms farThresholdSpine_identity
#print axioms middleUnboundedSpine_identity
#print axioms middleOdd_terminal_on_farThresholdSpine
#print axioms middleEven_terminal_on_middleUnboundedSpine
#print axioms middleUnboundedSpine_index_no_odd_v2
end BB6.Agent2F321ObstructionAlignment
