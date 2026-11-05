import Exceptional

namespace BB6.Agent45Exception

/-- A high-magnitude, low-offset dyadic source hub cannot have a
power-of-two shifted input. All bounds are exact natural-number claims. -/
theorem encoded_no_pure_power
    (N m b d w z alpha t : Nat)
    (hm : m+4≤N)
    (hw : 4≤w) (hz : 0<z)
    (hbeven : b%2=0)
    (hcoord : b+4*w=alpha*2^(N-m))
    (hsmallw : 4*w≤2^(N-m-1))
    (hsmallz : 2*z<2^(N-m-2))
    (hshift : 2^(N-m-2) ∣ d+b/2+3+2*z)
    (hpow : d+b/2+3=2^t) : False := by
  have ha : 1≤alpha := by
    by_cases haa : alpha=0
    · rw [haa] at hcoord
      simp at hcoord
      omega
    · omega
  have hbig : 2^(N-m)≤b+4*w := by
    calc
      2^(N-m) = 1*2^(N-m) := by omega
      _ ≤ alpha*2^(N-m) := Nat.mul_le_mul_right _ ha
      _ = b+4*w := hcoord.symm
  have hsub1 : (N-m-1)+1=N-m := by omega
  have hsub2 : (N-m-2)+1=N-m-1 := by omega
  have hp1 : 2^(N-m)=2*2^(N-m-1) := by
    calc
      2^(N-m) = 2^((N-m-1)+1) := by rw [hsub1]
      _ = 2^(N-m-1)*2 := by rw [Nat.pow_succ]
      _ = 2*2^(N-m-1) := by omega
  have hp2 : 2^(N-m-1)=2*2^(N-m-2) := by
    calc
      2^(N-m-1) = 2^((N-m-2)+1) := by rw [hsub2]
      _ = 2^(N-m-2)*2 := by rw [Nat.pow_succ]
      _ = 2*2^(N-m-2) := by omega
  have hhalf : b=2*(b/2) := by omega
  have hsize : 2^(N-m-2) ≤ d+b/2+3 := by omega
  exact no_power_low_offset (N-m-2) (d+b/2+3) z t hz hsmallz hsize hshift hpow

#print axioms encoded_no_pure_power
end BB6.Agent45Exception
