import PeriodCore

namespace PeriodFinite

theorem bounded_dilation (A : Nat) (e : Nat → Int) (N n : Nat)
    (he : ∀ i, n ≤ i → i < n+N → e i = (A:Int)*e (i+1)) :
    e n = ((A^N:Nat):Int)*e (n+N) := by
  induction N generalizing n with
  | zero => simp
  | succ N ih =>
      have hfirst := he n (by omega) (by omega)
      have htail : ∀ i, n+1≤i → i<n+1+N → e i=(A:Int)*e (i+1) := by
        intro i hi hj
        exact he i (by omega) (by omega)
      have hind := ih (n+1) htail
      calc
        e n = (A:Int)*e (n+1) := hfirst
        _ = (A:Int)*(((A^N:Nat):Int)*e (n+1+N)) := by rw [hind]
        _ = ((A^(N+1):Nat):Int)*e (n+(N+1)) := by
          rw [show n+(N+1) = n+1+N by omega, Nat.pow_succ, Int.natCast_mul]
          ac_rfl

private theorem pow_bound (A N : Nat) (hA : 2 ≤ A) : N < A^N := by
  have h1 := (Nat.lt_two_pow_self : N < 2^N)
  have h2 : 2^N ≤ A^N := Nat.pow_le_pow_left hA N
  omega

/-- Finite quantitative obstruction: a nonzero integer error cannot survive
    more than log_A(|error|) exact dilation stages. -/
theorem bounded_error (A N : Nat) (hA : 2 ≤ A)
    (e : Nat → Int) (he : ∀ i < N, e i = (A:Int)*e (i+1))
    (hne : e 0 ≠ 0) : A^N ≤ (e 0).natAbs := by
  have h := bounded_dilation A e N 0 (by
    intro i hi hj
    exact he i (by omega))
  have hv : (e 0).natAbs = A^N * (e N).natAbs := by
    have hcast := congrArg Int.natAbs h
    simpa [Int.natAbs_mul, Int.natAbs_natCast] using hcast
  have hp : 0 < (e 0).natAbs := Int.natAbs_pos.mpr hne
  have hnonnull : (e N).natAbs ≠ 0 := by
    intro hz
    rw [hz] at hv
    omega
  have hn : 1 ≤ (e N).natAbs := by omega
  have hb := Nat.mul_le_mul_left (A^N) hn
  omega

def error (A : Nat) (H S : Int) (z : Nat → Int) (n : Nat) : Int :=
    ((A:Int)-1)*(z (n+1)-z n) - H*S

theorem affine_error_step (A : Nat) (H S X D : Int)
    (z : Nat → Int) (n : Nat)
    (h0 : (A:Int)*z (n+1)=z n+H*X+(H*S)*(n:Int)+D)
    (h1 : (A:Int)*z (n+2)=z (n+1)+H*X+(H*S)*((n+1:Nat):Int)+D) :
    error A H S z n = (A:Int)*error A H S z (n+1) := by
  have hncast : ((n+1:Nat):Int) = (n:Int)+1 := by simp
  rw [hncast, Int.mul_add] at h1
  have hd : (A:Int)*(z (n+2)-z (n+1)) = z (n+1)-z n+H*S := by
    simp only [Int.mul_sub]
    omega
  let delta : Nat → Int := fun i => z (i+1)-z i
  have hdelta : (A:Int)*delta (n+1) = delta n+H*S := by
    simpa only [delta, show n+1+1=n+2 by omega] using hd
  have hmul := congrArg (fun x:Int => ((A:Int)-1)*x) hdelta
  have hx : (A:Int)*(((A:Int)-1)*delta (n+1)) =
      ((A:Int)-1)*delta n+((A:Int)-1)*(H*S) := by
    calc
      _ = ((A:Int)-1)*((A:Int)*delta (n+1)) := by
        simp only [Int.mul_left_comm]
      _ = _ := by simpa only [Int.mul_add] using hmul
  have hs : ((A:Int)-1)*(H*S) = (A:Int)*(H*S)-H*S := by
    rw [Int.sub_mul]
    simp
  change ((A:Int)-1)*delta n-H*S =
    (A:Int)*(((A:Int)-1)*delta (n+1)-H*S)
  rw [hs] at hx
  calc
    _ = (A:Int)*(((A:Int)-1)*delta (n+1))-(A:Int)*(H*S) := by omega
    _ = (A:Int)*(((A:Int)-1)*delta (n+1)-H*S) := by
      exact (Int.mul_sub _ _ _).symm

/-- An explicit bound for any finite sequence of identical affine blocks.
    The equations need only hold for the displayed finite horizon. -/
theorem finite_repetition_bound (A N : Nat) (hA : 2 ≤ A)
    (H S X D : Int) (z : Nat → Int)
    (hr : ∀ n, n < N+1 →
      (A:Int)*z (n+1)=z n+H*X+(H*S)*(n:Int)+D)
    (hbad : ∀ d:Int, ((A:Int)-1)*d ≠ H*S) :
    A^N ≤ (error A H S z 0).natAbs := by
  have he : ∀ i<N, error A H S z i = (A:Int)*error A H S z (i+1) := by
    intro i hi
    exact affine_error_step A H S X D z i (hr i (by omega))
      (hr (i+1) (by omega))
  have hne : error A H S z 0 ≠ 0 := by
    intro hz
    have hd : ((A:Int)-1)*(z 1-z 0)=H*S := by
      dsimp [error] at hz
      omega
    exact hbad (z 1-z 0) hd
  exact bounded_error A N hA (error A H S z) he hne

#print axioms bounded_error
#print axioms finite_repetition_bound
end PeriodFinite
