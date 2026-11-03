import Curvature

namespace BB6.Agent10IterBarrier

private theorem same_mod_add_dvd (x m c : Nat)
    (h : (x+c)%m=x%m) : m ∣ c := by
  have hs := Nat.sub_mod_eq_zero_of_mod_eq h
  have he : x+c-x=c := by omega
  rw [he] at hs
  exact Nat.dvd_of_mod_eq_zero hs

private theorem affine_mod_midpoint (n h m a b : Nat)
    (ha : ∀ z : Nat, F n z % m = (a*z+b)%m) :
    (F n 0 + F n (2*h))%m=(2*F n h)%m := by
  have h0 := ha 0
  have h1 := ha h
  have h2 := ha (2*h)
  have halgebra : (a*0+b) + (a*(2*h)+b) = 2*(a*h+b) := by
    have ht : a*(2*h)=2*(a*h) := by
      simp [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
    omega
  calc
    (F n 0+F n (2*h))%m
       = ((F n 0)%m+(F n (2*h))%m)%m := Nat.add_mod ..
    _ = ((a*0+b)%m+(a*(2*h)+b)%m)%m := by rw [h0,h2]
    _ = ((a*0+b)+(a*(2*h)+b))%m := (Nat.add_mod ..).symm
    _ = (2*(a*h+b))%m := by rw [halgebra]
    _ = ((2%m)*((a*h+b)%m))%m := by rw [Nat.mul_mod]
    _ = ((2%m)*((F n h)%m))%m := by rw [h1]
    _ = (2*F n h)%m := (Nat.mul_mod ..).symm

/-- Any affine modular quotient of a positive iterate has modulus dividing 7. -/
theorem affine_modulus_divides_seven (n m a b : Nat)
    (hn : 0<n)
    (ha : ∀ z : Nat, F n z % m = (a*z+b)%m) : m ∣ 7 := by
  obtain ⟨k, rfl⟩ : ∃ k : Nat, n=k+1 :=
    ⟨n-1, by omega⟩
  have hmid := F_midpoint k 0
  have hcong :
      (F (k+1) 0 + F (k+1) (2^(k+1)))%m =
      (2*F (k+1) (2^k))%m := by
    simpa [Nat.pow_succ, Nat.mul_comm] using
      affine_mod_midpoint (k+1) (2^k) m a b ha
  simp only [Nat.zero_add] at hmid
  rcases hmid with hmid | hmid
  · have hh : ((F (k+1) 0 + F (k+1) (2^(k+1)))+7)%m =
        (F (k+1) 0 + F (k+1) (2^(k+1)))%m := by
      rw [hmid]
      exact hcong.symm
    exact same_mod_add_dvd _ m 7 hh
  · have hh : ((2*F (k+1) (2^k))+7)%m=(2*F (k+1) (2^k))%m := by
      rw [←hmid]
      exact hcong
    exact same_mod_add_dvd _ m 7 hh

#print axioms affine_modulus_divides_seven
end BB6.Agent10IterBarrier
