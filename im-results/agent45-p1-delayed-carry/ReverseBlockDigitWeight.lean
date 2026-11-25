import ReverseBlock

namespace BB6.Agent45ReverseBlock

/-- Weighted binary digit sum: for B<2^k this is
    Σ_{i<k} i·2^i·bit_i(B), matching the little-endian C++ digitWeight. -/
def digitWeight : Nat → Nat → Nat
  | 0, _ => 0
  | k+1, B => 2*(digitWeight k (B/2) + B/2)

/-- The correction term and the weighted digit sum partition k·B. -/
theorem corr_add_digitWeight (k B : Nat) (hB : B<2^k) :
    corr k B + digitWeight k B = k*B := by
  induction k generalizing B with
  | zero =>
    have hB0 : B=0 := by omega
    subst B
    simp [corr,digitWeight]
  | succ k ih =>
    have hBdiv : B/2<2^k := by
      have hp : B<2^k*2 := by
        simpa [pow_succ,Nat.mul_comm] using hB
      omega
    have hmod : B=2*(B/2)+B%2 := by omega
    have hrec := ih (B/2) hBdiv
    simp only [corr,digitWeight]
    calc
      2*corr k (B/2) + (k+1)*(B%2) +
          2*(digitWeight k (B/2) + B/2)
        = 2*(corr k (B/2) + digitWeight k (B/2)) +
            2*(B/2) + (k+1)*(B%2) := by omega
      _ = 2*(k*(B/2)) + 2*(B/2) + (k+1)*(B%2) := by rw [hrec]
      _ = (k+1)*(2*(B/2)) + (k+1)*(B%2) := by
        have hq : (k+1)*(B/2)=k*(B/2)+B/2 := by
          rw [Nat.add_mul]
          simp
        calc
          2*(k*(B/2)) + 2*(B/2) + (k+1)*(B%2)
            = 2*(k*(B/2)+B/2) + (k+1)*(B%2) := by rw [Nat.mul_add]
          _ = 2*((k+1)*(B/2)) + (k+1)*(B%2) := by rw [← hq]
          _ = (k+1)*(2*(B/2)) + (k+1)*(B%2) := by
            simp [Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc]
      _ = (k+1)*(2*(B/2)+B%2) := by rw [Nat.mul_add]
      _ = (k+1)*B := by rw [hmod]

/-- The block remainder X+corr−(q+k)B is exactly the
    C++-style remainder X−qB−digitWeight(k,B). -/
theorem candidate_remainder_eq (q k X B : Nat)
    (hB : B<2^k)
    (hvalid : (q+k)*B ≤ X+corr k B) :
    X+corr k B-(q+k)*B = X-q*B-digitWeight k B := by
  have hsum := corr_add_digitWeight k B hB
  have hprod : (q+k)*B=q*B+k*B := Nat.add_mul q k B
  omega

#print axioms corr_add_digitWeight
#print axioms candidate_remainder_eq

end BB6.Agent45ReverseBlock
