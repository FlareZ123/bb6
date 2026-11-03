import Agent30CrossRadixWord
import Agent30CrossRadixParity

namespace BB6.Agent30Cross

private theorem mul_mod_lift (a b m : Nat) (h : a%m=b%m) :
    (2*a)%m = (2*b)%m := by
  calc
    (2*a)%m = (2*(a%m))%m := by simp [Nat.mul_mod]
    _ = (2*(b%m))%m := by rw [h]
    _ = (2*b)%m := by simp [Nat.mul_mod]

private theorem G_shift_bal (z d : Nat) :
  2*(G (z+d))+7*(z%2)=2*(G z)+3*d+7*((z+d)%2) := by
  have h0:=G_double z
  have h1:=G_double (z+d)
  omega

/-- A one-step obstruction using any odd multiple of a proposed period. -/
theorem G_odd_multiplier_obstruction (z m q : Nat)
    (hm : 0<m) (hq : q%2=1)
    (h : (G (z+m*q))%m = (G z)%m) : m ∣ 7 := by
  by_cases hme : m%2=0
  · let s := m/2
    have hm2 : m=2*s := by dsimp [s]; omega
    have hs : 0<s := by omega
    have hshift : m*q = 2*(s*q) := by rw [hm2]; ac_rfl
    rw [hshift, G_even_shift] at h
    have hzero : (3*s*q)%(2*s) = 0 := by
      have hh : (3*s*q + G z)%(2*s) = (0 + G z)%(2*s) := by
        simpa [Nat.add_comm, Nat.mul_assoc, hm2] using h
      exact (nat_add_mod_cancel (3*s*q) 0 (G z) (2*s)).mp hh
    have hodd : (3*q)%2=1 := by
      rw [Nat.mul_mod, hq]
    have hrem : (3*s*q)%(2*s)=s := by
      have hh: 3*s*q=s*(3*q) := by ac_rfl
      rw [hh, show 2*s = s*2 by omega, Nat.mul_mod_mul_left, hodd]
      simp
    omega
  · have hmo : m%2=1 := by omega
    have hdodd : (m*q)%2=1 := by
      rw [Nat.mul_mod, hmo, hq]
    have hpz : z%2<2 := Nat.mod_lt _ (by decide)
    have hpzd : (z+m*q)%2<2 := Nat.mod_lt _ (by decide)
    have hdpar : z%2+(z+m*q)%2=1 := by omega
    have h2 := mul_mod_lift ((G (z+m*q))) (G z) m h
    have hbal := G_shift_bal z (m*q)
    have h3d : (3*(m*q))%m=0 := by
      simp [Nat.mul_mod, Nat.mul_assoc]
    have hb : 7%m = 0 := by
      rcases Nat.mod_two_eq_zero_or_one z with hp | hp
      · have hp' : (z+m*q)%2=1 := by omega
        rw [hp,hp'] at hbal
        simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero] at hbal
        have hred : ((2*(G z))+7)%m = (2*(G z))%m := by
          calc
            ((2*(G z))+7)%m = (2*(G z)+3*(m*q)+7)%m := by
              simp [Nat.add_mod,h3d,Nat.add_assoc]
            _ = (2*(G (z+m*q)))%m := by rw [←hbal]
            _ = (2*(G z))%m := h2
        exact (nat_add_mod_cancel 7 0 (2*(G z)) m).mp (by simpa [Nat.add_comm] using hred)
      · have hp' : (z+m*q)%2=0 := by omega
        rw [hp,hp'] at hbal
        simp only [Nat.mul_zero,Nat.mul_one,Nat.add_zero] at hbal
        have hred : ((2*(G (z+m*q)))+7)%m = (2*(G (z+m*q)))%m := by
          calc
            ((2*(G (z+m*q)))+7)%m = (2*(G z)+3*(m*q))%m := by rw [hbal]
            _ = (2*(G z))%m := by simp [Nat.add_mod,h3d]
            _ = (2*(G (z+m*q)))%m := h2.symm
        exact (nat_add_mod_cancel 7 0 (2*(G (z+m*q))) m).mp (by simpa [Nat.add_comm] using hred)
    exact Nat.dvd_of_mod_eq_zero hb

/-- A finite congruence quotient of each positive iterate forces modulus to divide 7. -/
theorem iterG_finite_factor_only_seven (k m : Nat) (hm : 0<m)
    (hfactor : ∀ x y : Nat, x%m=y%m →
      (iterG (k+1) x)%m=(iterG (k+1) y)%m) : m ∣ 7 := by
  let z := iterG k 0
  have hh : (iterG (k+1) (2^k*m))%m = (iterG (k+1) 0)%m := by
    apply (hfactor (2^k*m) 0)
    simp
  have hshift : iterG k (2^k*m) = z+3^k*m := by
    simpa [z, Nat.mul_comm] using iterG_two_adic_shift k 0 m
  have hG : (G (z+3^k*m))%m = (G z)%m := by
    change (G (iterG k (2^k*m)))%m = (G (iterG k 0))%m at hh
    rwa [hshift] at hh
  have hodd : (3^k)%2=1 := by simp [Nat.pow_mod]
  exact G_odd_multiplier_obstruction z m (3^k) hm hodd (by
    simpa only [Nat.mul_comm] using hG)

/-- The scalar map is affine modulo each divisor of seven. -/
theorem G_affine_mod_seven_divisor (z m : Nat) (hm : m ∣ 7) :
    G z % m = (5*z+4) % m := by
  have heq : G z + 7*(z/2) = 5*z+4 := by
    unfold G
    omega
  have hzero : (7*(z/2))%m=0 := by
    obtain ⟨q,hq⟩ := hm
    rw [hq]
    simp [Nat.mul_assoc]
  have h := congrArg (fun v:Nat=>v%m) heq
  rw [Nat.add_mod,hzero] at h
  simpa using h

/-- Construct the finite quotient whenever its modulus divides seven. -/
theorem iterG_factors_mod_seven (n m : Nat) (hm : m ∣ 7) :
    ∀ x y : Nat, x%m=y%m → iterG n x%m=iterG n y%m := by
  induction n with
  | zero => intro x y hxy; exact hxy
  | succ n ih =>
    intro x y hxy
    change G (iterG n x)%m=G (iterG n y)%m
    rw [G_affine_mod_seven_divisor _ m hm, G_affine_mod_seven_divisor _ m hm]
    have hh := ih x y hxy
    rw [Nat.add_mod (5*iterG n x) 4 m,
        Nat.add_mod (5*iterG n y) 4 m,
        Nat.mul_mod 5 (iterG n x) m,
        Nat.mul_mod 5 (iterG n y) m,
        hh]

/-- Complete classification of *all* modular factors of all positive iterates. -/
theorem iterG_finite_factor_iff (n m : Nat) (hn : 0<n) (hm : 0<m) :
    (∀ x y : Nat, x%m=y%m → iterG n x%m=iterG n y%m) ↔ m ∣ 7 := by
  constructor
  · intro hf
    obtain ⟨k,rfl⟩ : ∃ k, n=k+1 := ⟨n-1, by omega⟩
    exact iterG_finite_factor_only_seven k m hm hf
  · intro hd
    exact iterG_factors_mod_seven n m hd

#print axioms iterG_finite_factor_iff
#print axioms iterG_factors_mod_seven
#print axioms iterG_finite_factor_only_seven
#print axioms G_odd_multiplier_obstruction
end BB6.Agent30Cross
