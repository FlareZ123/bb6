import Agent10BParity

namespace BB6.Agent10B

/-- One-step exact even-translation law for the shifted scalar map. -/
theorem T_even_shift (x d : Nat) : T (x + 2*d) = T x + 3*d := by
  have h := two_T (x+2*d)
  have hx := two_T x
  have hp : (x+2*d)%2 = x%2 := by omega
  rw [hp] at h
  omega

/-- The exact iterate translation from every 2-adic input cylinder. -/
theorem orbit_two_adic_shift (n x d : Nat) :
    orbit n (x+2^n*d) = orbit n x + 3^n*d := by
  induction n generalizing x d with
  | zero => simp [orbit]
  | succ n ih =>
    change orbit n (T (x+2^(n+1)*d)) = orbit n (T x) + 3^(n+1)*d
    have hpow : 2^(n+1)*d=2*(2^n*d) := by
      simp [Nat.pow_succ, Nat.mul_comm, Nat.mul_left_comm]
    rw [hpow, T_even_shift]
    have hin : T x + 3*(2^n*d) = T x + 2^n*(3*d) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    rw [hin, ih]
    simp [Nat.pow_succ, Nat.mul_assoc, Nat.mul_comm]

/-- Divisibility by 2^n suffices for equality of the first n parity digits. -/
theorem prefix_if_dvd (n x y : Nat) (hle : x≤y)
    (hd : 2^n ∣ y-x) : SamePrefix x y n := by
  obtain ⟨q,hq⟩ := hd
  intro j hj
  have hn : n=j+(n-j) := by omega
  have hxy : y = x + 2^j*(2^(n-j)*q) := by
    have heq : 2^n*q = 2^j*(2^(n-j)*q) := by
      rw [hn, Nat.pow_add]
      simp [Nat.mul_assoc]
    omega
  rw [hxy, orbit_two_adic_shift]
  have he : 2 ∣ 2^(n-j)*q := by
    have hp : 0<n-j := by omega
    obtain ⟨v,hv⟩ : ∃ v : Nat, n-j=v+1 :=
      ⟨n-j-1, by omega⟩
    refine ⟨2^v*q, ?_⟩
    rw [hv, Nat.pow_succ]
    simp [Nat.mul_comm, Nat.mul_left_comm]
  obtain ⟨v,hv⟩ := he
  have hm : (3^j*(2^(n-j)*q))%2=0 := by
    rw [hv]
    have heq : 3^j*(2*v)=2*(3^j*v) := by ac_rfl
    rw [heq]
    omega
  rw [Nat.add_mod,hm]
  omega

/-- Forward and reverse finite parity-coding laws, giving an exact iff. -/
theorem prefix_iff_dvd (n x y : Nat) (hle : x≤y) :
    SamePrefix x y n ↔ 2^n ∣ y-x := by
  constructor
  · exact prefix_div_pow_two n x y hle
  · exact prefix_if_dvd n x y hle

/-- Source scalar map's exact 2-adic input translation. -/
theorem G_iter_two_adic_shift (n z d : Nat) :
    iterG n (z+2^n*d) = iterG n z + 3^n*d := by
  have hs := orbit_two_adic_shift n (z+8) d
  have hstart : (z+8)+2^n*d=(z+2^n*d)+8 := by omega
  rw [hstart, orbit_shifted, orbit_shifted] at hs
  omega

/-- Every input parity cylinder admits both possible next parity bits. -/
theorem G_shifted_bit_flip (n z : Nat) :
    (iterG n (z+2^n))%2 = ((iterG n z)+1)%2 := by
  have hs : iterG n (z+2^n) = iterG n z + 3^n := by
    simpa using G_iter_two_adic_shift n z 1
  have hodd : (3^n)%2=1 := by
    simp [Nat.pow_mod]
  rw [hs]
  rw [Nat.add_mod, Nat.add_mod, hodd]
  omega

#print axioms orbit_two_adic_shift
#print axioms prefix_iff_dvd
#print axioms G_iter_two_adic_shift
#print axioms G_shifted_bit_flip
end BB6.Agent10B
