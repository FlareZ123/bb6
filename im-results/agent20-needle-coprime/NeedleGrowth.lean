import Lean
import Lean.Elab.Tactic.Omega

namespace NeedleGrowth

theorem odd_lt_pow (q : Nat) : 2*q+3 < 2^(q+2) := by
  induction q with
  | zero => decide
  | succ q ih =>
    have h : 2*(q+1)+3 < 2*(2^(q+2)) := by omega
    rw [show q+1+2=(q+2)+1 by omega, Nat.pow_succ]
    omega

theorem dyadic_increment (q v k : Nat)
    (h : 2^k ≤ 2^v * (2*q+3)) :
    k+2 ≤ v+3*(q+1) := by
  have hp := odd_lt_pow q
  have hv : 0 < 2^v := Nat.pow_pos (by omega)
  have hu : 2^v*(2*q+3) < 2^(v+q+2) := by
    calc
      2^v*(2*q+3) < 2^v*2^(q+2) := Nat.mul_lt_mul_of_pos_left hp hv
      _ = 2^(v+q+2) := by
        calc
          2^v * 2^(q+2) = 2^(v+(q+2)) := (Nat.pow_add 2 v (q+2)).symm
          _ = 2^(v+q+2) := by
            have hindex : v+(q+2)=v+q+2 := by omega
            rw [hindex]
  have hk : k < v+q+2 := by
    by_cases hk : k < v+q+2
    · exact hk
    · have hle : v+q+2 ≤ k := by omega
      have hh : 2^(v+q+2) ≤ 2^k := Nat.pow_le_pow_right (by omega) hle
      omega
  omega

/-- A successful high-level edge, expressed in the exact shifted-counter
    arithmetic of Space Needle. -/
def Edge (b c : Nat) : Prop :=
  ∃ q v, b = 2^v*(2*q+3) ∧ c = b+v+3*(q+1)

/-- Every one-step update beats the binary logarithm of its input. -/
theorem edge_log_growth {b c : Nat} (h : Edge b c) :
    b + Nat.log2 b + 2 ≤ c := by
  rcases h with ⟨q,v,rfl,rfl⟩
  have hpos : 0 < 2^v := Nat.pow_pos (by omega)
  have hne : 2^v*(2*q+3) ≠ 0 := Nat.mul_ne_zero (by omega) (by omega)
  have hlog := (Nat.log2_eq_iff hne).mp rfl
  have hg := dyadic_increment q v (Nat.log2 (2^v*(2*q+3))) hlog.1
  omega

/-- A path of successful steps is any function satisfying the edge law at
    every consecutive pair. -/
def Orbit (f : Nat → Nat) : Prop := ∀ n, Edge (f n) (f (n+1))

/-- Strict progress guarantees a linear base bound for every orbit. -/
theorem orbit_linear (f : Nat → Nat) (h : Orbit f) (n : Nat) :
    f 0 + n ≤ f n := by
  induction n with
  | zero => omega
  | succ n ih =>
      rcases h n with ⟨q,v,_,hc⟩
      have hnext : f n + 1 ≤ f (n+1) := by rw [hc]; omega
      omega

/-- After entering a dyadic region, every remaining step gains at least
    the region's binary exponent plus two. -/
theorem orbit_dyadic_drift (f : Nat → Nat) (h : Orbit f)
    (M n t : Nat) (hM : 2^M ≤ f n) :
    f n + t*(M+2) ≤ f (n+t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hMnext : 2^M ≤ f (n+t) := by omega
      rcases h (n+t) with ⟨q,v,hfact,hnext⟩
      have hg := dyadic_increment q v M (by rw [←hfact]; exact hMnext)
      have hstep : f (n+t) + M + 2 ≤ f (n+t+1) := by
        rw [hnext]
        omega
      calc
        f n + (t+1)*(M+2) = (f n + t*(M+2))+(M+2) := by rw [Nat.add_mul]; omega
        _ ≤ f (n+t)+(M+2) := by omega
        _ ≤ f (n+(t+1)) := by
          have hi : n+(t+1) = n+t+1 := by omega
          rw [hi]
          omega

/-- The origin-independent superlinear lower bound for every infinite
    successful path. -/
theorem orbit_superlinear (f : Nat → Nat) (h : Orbit f)
    (M n : Nat) (hn : 2^(M+1) ≤ n) :
    (n/2)*(M+2) ≤ f n := by
  have hpow : 2^(M+1)=2^M*2 := by rw [Nat.pow_succ]
  have hlow : 2^M ≤ n := by omega
  have hthreshold := orbit_linear f h (2^M)
  have hstart : 2^M ≤ f (2^M) := by omega
  have hdrift := orbit_dyadic_drift f h M (2^M) (n-2^M) hstart
  have hindex : 2^M+(n-2^M)=n := by omega
  rw [hindex] at hdrift
  have hhalf : n/2 ≤ n-2^M := by omega
  have hmult := Nat.mul_le_mul_right (M+2) hhalf
  have hcomm : (n-2^M)*(M+2) = (M+2)*(n-2^M) := Nat.mul_comm _ _
  omega

#print axioms NeedleGrowth.dyadic_increment
#print axioms NeedleGrowth.edge_log_growth
#print axioms NeedleGrowth.orbit_dyadic_drift
#print axioms NeedleGrowth.orbit_superlinear
end NeedleGrowth
